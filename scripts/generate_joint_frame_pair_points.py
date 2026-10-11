from pathlib import Path
import argparse,json,hashlib

if not __debug__:raise SystemExit('Assertions must remain enabled; do not use -O')

ap=argparse.ArgumentParser();ap.add_argument('--formal-root',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--check',action='store_true');args=ap.parse_args()
root=args.formal_root
main=root
cert=json.loads((root/'output/am-joint-frame-pair-certificate.json').read_text())
old=json.loads((main/'output/am-ninth-span-point-catalog.json').read_text())
oldpoints={p for p,v,n in old['point_catalog']}
extra=[(p,v) for p,v,n in cert['point_catalog'] if p not in oldpoints]
assert len(extra)==180
text=['import RecordProportion.NinthSpanPoints','','namespace RHWeil.RecordSubmission.JointFramePairPoints',
 'open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD','noncomputable section','set_option maxRecDepth 100000',
 'set_option maxHeartbeats 0','set_option stderrAsMessages false','set_option Elab.async false','',
 '/-- The original 541-entry proved catalog is preserved; only 180 new entries are added. -/',
 'def extraCatalog : Array (Nat × Nat) := #[']
text += [f'  ({p},{v}),' for p,v in extra]
text += [']','',
 'def catalogPoint (t : Nat) : Nat := if t < 541 then NinthSpanPoints.catalogPoint t else ((extraCatalog[t-541]?).getD (0,0)).1',
 'def catalogValue (t : Nat) : Nat := if t < 541 then NinthSpanPoints.catalogValue t else ((extraCatalog[t-541]?).getD (0,0)).2',
 'def regionIndex (t : Nat) : Nat := (catalogPoint t + 16384) >>> 15',
 'def regionLower (t : Nat) : Nat := rgA AMW.Cert.PC8CLData.REG (regionIndex t)',
 'def regionUpper (t : Nat) : Nat := rgB AMW.Cert.PC8CLData.REG (regionIndex t)',
 'def catalogCheck (t : Nat) : Bool := decide (catalogValue t < 2^96) && PointSoundness.tangentCheck (regionLower t) (regionUpper t) (catalogPoint t) (catalogValue t)',
 'attribute [local irreducible] extraCatalog AMW.Cert.PC8CLData.PT','']
chunks=[]
for start in range(0,180,16):
 end=min(180,start+16);chunks.append((start,end))
 text.append(f'private theorem extra_block_{start} : allFrom {541+start} {end-start} catalogCheck = true := by decide +kernel')
text += ['', 'private theorem extra_all : allFrom 541 180 catalogCheck = true := by']
for k,(start,end) in enumerate(chunks):
 if k==0:text.append(f'  have h0 := extra_block_{start}')
 else:text.append(f'  have h{k} : allFrom 541 {end} catalogCheck = true := allFrom_add h{k-1} extra_block_{start}')
text += [f'  exact h{len(chunks)-1}','',
 'theorem catalogChecks (t : Nat) (ht : t < 721) : catalogCheck t = true := by',
 '  by_cases ho : t < 541',
 '  · simpa only [catalogCheck,catalogValue,catalogPoint,if_pos ho,regionLower,regionUpper,regionIndex,',
 '      NinthSpanPoints.catalogCheck,NinthSpanPoints.regionLower,NinthSpanPoints.regionUpper,NinthSpanPoints.regionIndex] using NinthSpanPoints.catalogChecks t ho',
 '  · have he : t - 541 < 180 := by omega',
 '    have h := allFrom_spec extra_all (t-541) he',
 '    simpa only [Nat.add_sub_of_le (by omega : 541 ≤ t)] using h','']
previous=(root/'RecordProportion/NinthSpanPoints.lean').read_text(encoding='utf8')
tail=previous.split('theorem catalogValue_lt',1)[1]
tail=tail.replace('541','721').replace('RHWeil.RecordSubmission.NinthSpanPoints','RHWeil.RecordSubmission.JointFramePairPoints')
text.append('theorem catalogValue_lt'+tail)
out=root/'RecordProportion/JointFramePairPoints.lean'
generated='\n'.join(text)
if args.check:assert out.read_text(encoding='utf8').replace('\r\n','\n')==generated
else:out.write_text(generated,encoding='utf8',newline='\n')
print(json.dumps({'source':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'new_entries':180,'inherited_entries':541,'bytes':out.stat().st_size}))
