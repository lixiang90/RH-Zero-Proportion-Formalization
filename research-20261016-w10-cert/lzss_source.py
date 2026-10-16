"""Pure byte LZSS source packaging; no proof or external program is trusted.

Eight tokens share a low-bit-first flag byte. A zero bit is one literal byte;
a one bit is [distance-1 low8, high8, length-3], with overlapping copies.
The Lean command expander must reproduce these bytes and then elaborate them
normally. Final default-kernel and nanoda replay remain mandatory.
"""
from collections import defaultdict,deque
from pathlib import Path
import argparse,hashlib,json,time
from emit_tree import encode

def compress(raw):
  chains=defaultdict(deque);out=bytearray();i=0
  while i<len(raw):
    flagpos=len(out);out.append(0)
    for bit in range(8):
      if i>=len(raw):break
      key=raw[i:i+4];best=dist=0
      for j in reversed(chains[key]):
        if i-j>65536:break
        n=4;limit=min(258,len(raw)-i)
        if limit<4:continue
        while n<limit and raw[j+n]==raw[i+n]:n+=1
        if n>best:best=n;dist=i-j
        if n==limit:break
      count=best if best>=4 else 1
      if count>1:
        out[flagpos]|=1<<bit;out.extend([(dist-1)&255,(dist-1)>>8,count-3])
      else:out.append(raw[i])
      for k in range(i,i+count):
        chain=chains[raw[k:k+4]];chain.append(k)
        if len(chain)>24:chain.popleft()
      i+=count
  return bytes(out)

def decompress(data,expected):
  out=bytearray();pos=0
  while len(out)<expected:
    flags=data[pos];pos+=1
    for bit in range(8):
      if len(out)>=expected:break
      if flags>>bit&1:
        d=data[pos]+256*data[pos+1]+1;n=data[pos+2]+3;pos+=3
        assert d<=len(out)
        for _ in range(n):out.append(out[-d])
      else:out.append(data[pos]);pos+=1
  assert len(out)==expected and pos==len(data)
  return bytes(out)

def command(raw):
  data=compress(raw);assert decompress(data,len(raw))==raw
  parts=[encode(int.from_bytes(data[i:i+256],'little')) for i in range(0,len(data),256)]
  source=f'w10_expand {len(raw)} {len(data)} ['+',\n'.join('"'+s+'"' for s in parts)+']\n'
  return source,data

def main():
  ap=argparse.ArgumentParser();ap.add_argument('input',type=Path)
  ap.add_argument('--output',type=Path);args=ap.parse_args()
  raw=args.input.read_bytes();started=time.monotonic();source,data=command(raw)
  if args.output:args.output.write_bytes(source.encode('utf8'))
  result={'input_bytes':len(raw),'input_sha256':hashlib.sha256(raw).hexdigest(),
    'compressed_bytes':len(data),'encoded_command_bytes':len(source.encode('utf8')),
    'roundtrip_passed':True,'seconds':time.monotonic()-started}
  print(json.dumps(result))
if __name__=='__main__':main()
