"""Stream an immutable open checkpoint into compact-v2 without loading raw JSON.

The producer saves by atomic replacement; the opened file remains one whole
snapshot. Hashing occurs on that same file handle. Every large map/list is
decoded one entry at a time, packed losslessly and then released. No search,
LP, scalar oracle, or minimizer semantics is changed by this conversion.
"""
from pathlib import Path
import argparse,codecs,hashlib,json,os,time
import cover_compact_codec as codec
HERE=Path(__file__).parent

def open_snapshot(path):
    if os.name!='nt':return path.open('rb')
    # Keep the old inode readable while the live producer atomically replaces
    # its filename. Ordinary Windows CRT open() need not share DELETE access.
    import ctypes,msvcrt
    from ctypes import wintypes
    kernel=ctypes.WinDLL('kernel32',use_last_error=True)
    kernel.CreateFileW.argtypes=[wintypes.LPCWSTR,wintypes.DWORD,wintypes.DWORD,wintypes.LPVOID,wintypes.DWORD,wintypes.DWORD,wintypes.HANDLE]
    kernel.CreateFileW.restype=wintypes.HANDLE
    handle=kernel.CreateFileW(str(path.resolve()),0x80000000,1|2|4,None,3,0x08000000,None)
    if handle==wintypes.HANDLE(-1).value:raise ctypes.WinError(ctypes.get_last_error())
    descriptor=msvcrt.open_osfhandle(handle,os.O_RDONLY|os.O_BINARY)
    return os.fdopen(descriptor,'rb')

class Stream:
    def __init__(self,path):
        self.file=open_snapshot(path);self.buffer='';self.eof=False;self.decoder=codecs.getincrementaldecoder('utf-8')()
        self.sha=hashlib.sha256();self.size=0;self.json=json.JSONDecoder()
    def more(self):
        raw=self.file.read(1<<20);self.sha.update(raw);self.size+=len(raw)
        if not raw:self.eof=True
        self.buffer+=self.decoder.decode(raw,final=not raw)
    def peek(self):
        while True:
            self.buffer=self.buffer.lstrip()
            if self.buffer:return self.buffer[0]
            if self.eof:return ''
            self.more()
    def token(self,expected):
        assert self.peek()==expected,(expected,self.buffer[:80]);self.buffer=self.buffer[1:]
    def value(self):
        self.peek()
        while True:
            try:
                value,end=self.json.raw_decode(self.buffer)
                # A number at a chunk boundary may have more digits.
                if end==len(self.buffer) and not self.eof:self.more();continue
                self.buffer=self.buffer[end:];return value
            except json.JSONDecodeError:
                if self.eof:raise
                self.more()
    def array(self,transform):
        self.token('[');out=[]
        if self.peek()!=']':
            while True:
                out.append(transform(self.value()))
                if self.peek()!=',':break
                self.token(',')
        self.token(']');return out
    def mapping(self,transform):
        self.token('{');out={}
        if self.peek()!='}':
            while True:
                key=self.value();assert isinstance(key,str) and key not in out;self.token(':')
                out[key]=transform(self.value())
                if len(out)%2000==0:print(json.dumps({'packed_map_entries':len(out),'input_bytes_read':self.size}),flush=True)
                if self.peek()!=',':break
                self.token(',')
        self.token('}');return out

def convert(path):
    stream=Stream(path);stream.token('{');out={}
    while stream.peek()!='}':
        key=stream.value();assert isinstance(key,str) and key not in out;stream.token(':')
        if key=='accepted':value=stream.array(codec.pack_leaf)
        elif key=='sublevel_contractions':value=stream.mapping(codec.pack_obbt)
        elif key=='contractions':value=stream.mapping(lambda rows:[codec.pack_newton(row) for row in rows])
        else:value=stream.value()
        out[key]=value
        if stream.peek()!=',':break
        stream.token(',')
    stream.token('}');assert stream.peek()=='';stream.file.close()
    assert out['format']=='RelevantBelow-KKT-OBBT-v1';out['format']='RelevantBelow-KKT-OBBT-compact-v2'
    out['compact_origin']={'source_path':str(path),'source_sha256':stream.sha.hexdigest(),'source_bytes':stream.size,
      'source_checked':out['checked'],'codec_sha256':hashlib.sha256(Path(codec.__file__).read_bytes()).hexdigest()}
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();start=time.monotonic();out=convert(args.input);temp=args.output.with_suffix('.partial')
    with temp.open('w',encoding='utf8',newline='\n') as f:
        for piece in json.JSONEncoder(separators=(',',':')).iterencode(out):f.write(piece)
        f.write('\n')
    temp.replace(args.output)
    receipt={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'input':out['compact_origin'],'compact_bytes':args.output.stat().st_size,'checked':out['checked'],
      'pending':out['unresolved_count'],'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.with_suffix('.conversion.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
