"""Stream a discovery tree to its exact certificate fields, without changing them.

The original discovery JSON remains immutable. Equality of every retained
record is checked by a second streaming parse of the reduced JSON.
"""
from pathlib import Path
import gzip,hashlib,json,shutil,time

HERE=Path(__file__).parent
BRANCH_KEYS=('path','axis','cut','normalize_cuts')
LEAF_KEYS=('path','normalize_cuts')
RESULT_KEYS=('FS','multiplier','mcheck_numerator','floor_numerator','empty','reflection','violation_axis')

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while chunk:=f.read(1<<20):h.update(chunk)
    return h.hexdigest()

class Stream:
    def __init__(self,path):
        self.file=path.open('r',encoding='utf8');self.text='';self.pos=0;self.eof=False;self.decoder=json.JSONDecoder()
    def more(self):
        self.text=self.text[self.pos:];self.pos=0;chunk=self.file.read(1<<16)
        self.text+=chunk
        if not chunk:self.eof=True
    def peek(self):
        while True:
            while self.pos<len(self.text) and self.text[self.pos].isspace():self.pos+=1
            if self.pos<len(self.text):return self.text[self.pos]
            if self.eof:return ''
            self.more()
    def eat(self,char):
        assert self.peek()==char,(char,self.peek());self.pos+=1
    def value(self):
        self.peek()
        while True:
            try:
                value,end=self.decoder.raw_decode(self.text,self.pos);self.pos=end;return value
            except json.JSONDecodeError:
                if self.eof:raise
                self.more()
    def array(self):
        self.eat('[')
        if self.peek()!=']':
            while True:
                yield self.value()
                if self.peek()==']':break
                self.eat(',')
        self.eat(']')
    def close(self):self.file.close()

def project(key,row):
    if key=='branches':return {k:row[k] for k in BRANCH_KEYS if k in row}
    result=row['result'];out={k:row[k] for k in LEAF_KEYS if k in row}
    out['result']={k:result[k] for k in RESULT_KEYS if k in result}
    if 'certificate' in result:
        out['result']['certificate']={k:result['certificate'][k] for k in ('lower_bounds','upper_bounds')}
    return out

def transcript(path,output=None):
    stream=Stream(path);metadata={};digest=hashlib.sha256();counts={'branches':0,'accepted':0,'numeric':0,'empty':0}
    stream.eat('{');first=True
    if output:output.write('{')
    while stream.peek()!='}':
        if not first:stream.eat(',')
        key=stream.value();stream.eat(':')
        if output:
            if not first:output.write(',')
            output.write(json.dumps(key)+':')
        if key in ('branches','accepted'):
            if output:output.write('[')
            first_row=True
            for row in stream.array():
                reduced=project(key,row);encoded=json.dumps(reduced,separators=(',',':'))
                assert json.loads(encoded)==reduced
                digest.update(key.encode()+b'\0'+encoded.encode()+b'\n');counts[key]+=1
                if key=='accepted':counts['numeric' if 'FS' in reduced['result'] else 'empty']+=1
                if output:
                    if not first_row:output.write(',')
                    output.write(encoded)
                first_row=False
                if output and sum(counts[k] for k in ('branches','accepted'))%20000==0:
                    print(json.dumps({'projected_records':counts['branches']+counts['accepted']}),flush=True)
            if output:output.write(']')
        else:
            value=stream.value();metadata[key]=value
            if output:output.write(json.dumps(value,separators=(',',':')))
        first=False
    stream.eat('}');assert stream.peek()=='';stream.close()
    if output:output.write('}\n')
    return metadata,digest.hexdigest(),counts

def main():
    started=time.monotonic();source=HERE/'ordered-complete.json';dest=HERE/'ordered-proof-input.json'
    assert not dest.exists(),'Immutable reduced proof input already exists'
    expected=json.loads((HERE/'tailfix-final-merge-manifest.json').read_text())['output']['sha256']
    before=sha(source);assert before==expected
    partial=dest.with_suffix('.partial')
    with partial.open('w',encoding='utf8',newline='\n') as output:metadata,semantic,counts=transcript(source,output)
    newmeta,newsemantic,newcounts=transcript(partial)
    assert metadata==newmeta and semantic==newsemantic and counts==newcounts
    assert sha(source)==before,'Original changed during reduction'
    assert not metadata['unresolved_count'] and metadata['complete_finite_partition']
    partial.replace(dest);packed=dest.with_suffix('.json.gz');packed_partial=packed.with_suffix('.partial')
    with dest.open('rb') as inp,packed_partial.open('wb') as out:
        with gzip.GzipFile(filename='',mode='wb',fileobj=out,compresslevel=9,mtime=0) as handle:
            shutil.copyfileobj(inp,handle,1<<20)
    packed_partial.replace(packed)
    manifest={'scope':__doc__,'source':{'path':source.name,'sha256':before,'bytes':source.stat().st_size},
        'reduced':{'path':dest.name,'sha256':sha(dest),'bytes':dest.stat().st_size},
        'gzip':{'path':packed.name,'sha256':sha(packed),'bytes':packed.stat().st_size},
        'projection':{'branch_keys':BRANCH_KEYS,'leaf_keys':LEAF_KEYS,'result_keys':RESULT_KEYS,
            'certificate_keys':['lower_bounds','upper_bounds']},
        'semantic_certificate_sha256':semantic,'all_retained_records_identical':True,
        'all_tree_metadata_identical':True,'original_unchanged':True,'complete_finite_partition':True,
        'counts':counts,'script_sha256':sha(Path(__file__)),'elapsed_seconds':time.monotonic()-started}
    (HERE/'proof-input-reduction-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest),flush=True)
if __name__=='__main__':main()
