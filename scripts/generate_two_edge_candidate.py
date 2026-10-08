"""Reproduce the fixed two-edge proof-routing candidate without changing formal data.

Run --check --legacyImport --output tmp/optimized-twoedge/candidate_1224.lean
to check the complete isolated family source. Normal output uses the formal
FloydTwoEdge import. Output is confined to this repository's ignored tmp tree.
The fixed49/6 route lists are proof hints; every resulting original integer
proposition still requires ordinary Lean kernel verification. This generator
alone certifies neither those propositions nor official website acceptance.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
if not __debug__:
 raise SystemExit('Run without -O: hash and structure checks must remain enabled.')
DATA_SHA='0b12cba764e62ac55f1d7acdebc6c86cf1a26253ccb31939519b983f01b1bc59'
FLOYD_SHA='e381f27356dca8ea3d876981c544f4d12298a4246eafaef94ec620b58b8701a3'
PREFIX_SHA='e2a276016590de1c6c9212000616b1ab2b5530baedea862ed57db8adad51bd21'
FULL=[14,15,16,191,826,1104]
TWO=[3,4,35,54,57,59,86,90,134,157,161,164,167,182,271,333,355,370,419,420,478,480,562,570,571,601,701,780,806,808,877,890,892,894,901,926,929,933,934,939,940,1010,1013,1078,1097,1199,1200,1203,1213]
# These fixed lists guide only ordinary proof selection. They are not assumptions.
# Every emitted theorem still proves the original integerCertificateCheck i=true
# and is required to pass the usual Lean kernel and refuse all recovery holes.
def sha(blob):return hashlib.sha256(blob).hexdigest()
def extension(prefix):
 basic=prefix.split('noncomputable def basicIntegerCertificateLower (index : Nat) : Int :=\n',1)[1].split('\n\nnoncomputable def basicIntegerCertificateCheck',1)[0]
 basic=basic.replace('primitiveBound left right (column+1) column','twoEdgeBound left right (column+1) column').replace('primitiveBound left right column (column+1)','twoEdgeBound left right column (column+1)')
 proof=prefix.split('theorem basicIntegerCertificateLower_le (index : Nat) :\n',1)[1].split('\ntheorem integerCheck_of_basic',1)[0]
 proof=proof.replace('basicIntegerCertificateLower','twoEdgeIntegerCertificateLower').replace('pairClosure_le_primitive','pairClosure_le_twoEdge')
 return '''
noncomputable def twoEdgeBound (left right i j : Nat) : Int :=
  (List.range 9).foldl
    (fun best k => min best
      (primitiveBound left right i k + primitiveBound left right k j))
    (primitiveBound left right i j)

theorem pairClosure_le_twoEdge (left right i j : Nat) (hi : i < 9) (hj : j < 9) :
    ((pairClosure left right)[9*i+j]?).getD 0 ≤ twoEdgeBound left right i j := by
  unfold twoEdgeBound
  apply RHWeilRecord.FloydTwoEdge.lower_le_foldl_min
  · exact pairClosure_le_primitive left right i j hi hj
  · intro k hk
    have hk9 : k < 9 := List.mem_range.mp hk
    have h := RHWeilRecord.FloydTwoEdge.closure_le_two_edge
      (primitiveBounds left right) i j k hi hj hk9
    change ((pairClosure left right)[9*i+j]?).getD 0 ≤
      ((primitiveBounds left right)[9*i+k]?).getD 0 +
      ((primitiveBounds left right)[9*k+j]?).getD 0 at h
    rw [primitiveBounds_entry left right i k hi hk9,
        primitiveBounds_entry left right k j hk9 hj] at h
    exact h

noncomputable def twoEdgeIntegerCertificateLower (index : Nat) : Int :=
'''+basic+'''

noncomputable def twoEdgeIntegerCertificateCheck (index : Nat) : Bool :=
  decide (2*805260*(5*10000000000*32768)*1000000000 ≤ twoEdgeIntegerCertificateLower index)

theorem twoEdgeIntegerCertificateLower_le (index : Nat) :
'''+proof+'''
theorem integerCheck_of_twoEdge {index : Nat} (h : twoEdgeIntegerCertificateCheck index = true) :
    integerCertificateCheck index = true := by
  apply decide_eq_true
  exact (of_decide_eq_true h).trans (twoEdgeIntegerCertificateLower_le index)

'''
def clock(stage):return '\nrun_cmd Lean.Elab.Command.liftIO <| do\n  let now ← IO.monoMsNow\n  IO.eprintln s!"COST '+stage+' {now}"\n'
def main():
 parser=argparse.ArgumentParser(description='Reproduce the unchanged-target two-edge Lean candidate from the committed fixed Data source. No ignored diagnostic or extension inputs required.')
 parser.add_argument('--output',type=Path,default=Path('tmp/optimized-twoedge/repro/candidate_1224.lean'))
 parser.add_argument('--legacy-import','--legacyImport',dest='legacy_import',action='store_true',help='Reproduce the original isolated candidate header exactly; normal output imports the formal generic FloydTwoEdge module.')
 parser.add_argument('--check',action='store_true',help='Compare existing output, without writing it.')
 args=parser.parse_args()
 output=(ROOT/args.output).resolve()
 tmp_root=(ROOT/'tmp').resolve()
 if tmp_root != ROOT/'tmp' or tmp_root not in output.parents or output.suffix!='.lean':
  parser.error('--output must resolve to a .lean file strictly inside this repository tmp directory')
 blob=(ROOT/'RecordProportion/FiniteCertificateData.lean').read_bytes()
 generic=(ROOT/'RecordProportion/FloydTwoEdge.lean').read_bytes()
 assert sha(blob)==DATA_SHA and sha(generic)==FLOYD_SHA
 original=blob.decode('utf-8');marker='/- The command emits ordinary theorem declarations.';prefix,tail=original.split(marker,1);tail=marker+tail
 assert sha(prefix.encode())==PREFIX_SHA and 'theorem integer_representative_' not in prefix
 assert len(FULL)==6 and len(TWO)==49 and len(set(FULL+TWO))==55 and all(0<=i<1224 for i in FULL+TWO)
 old='''      let command := "theorem integer_representative_" ++ toString index ++
        " : integerCertificateCheck " ++ toString index ++
        " = true := by\\n  first\\n  | exact integerCheck_of_basic (by decide +kernel)\\n  | decide +kernel"'''
 new='''      let fullIndices : List Nat := '''+str(FULL)+'''
      let twoIndices : List Nat := '''+str(TWO)+'''
      let proof := if fullIndices.contains index then "decide +kernel"
        else if twoIndices.contains index then "exact integerCheck_of_twoEdge (by decide +kernel)"
        else "exact integerCheck_of_basic (by decide +kernel)"
      let command := "theorem integer_representative_" ++ toString index ++
        " : integerCertificateCheck " ++ toString index ++ " = true := by " ++ proof'''
 assert tail.count(old)==1;tail=tail.replace(old,new)
 chunks=tail.split('prove_integer_batch 0 16\n',1);assert len(chunks)==2
 tail=chunks[0]+clock('PROOFS_BEGIN')+'prove_integer_batch 0 16\n'+chunks[1]
 tail=tail.replace('combine_integer_representatives\n\nend',clock('PROOFS_END')+'combine_integer_representatives\n\nend')
 header='import «tmp».«optimized-twoedge».FloydTwoEdge\n' if args.legacy_import else 'import RecordProportion.FloydTwoEdge\n'
 ext=extension(prefix);result=(header+prefix+ext+tail).encode('utf-8')
 assert sha(ext.encode())=='a14a56653a337473f4cbd460610234fc393992bf43af73dea3bec79567e7d279'
 if args.legacy_import:assert sha(result)=='6b58615dc531711b1a716242a225d0c39c70c0a843f81e39b1901efdb47e00f1'
 if args.check:assert output.read_bytes()==result
 else:output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes(result)
 print(json.dumps({'output':str(output),'bytes':len(result),'sha256':sha(result),'unchanged_prefix_sha256':PREFIX_SHA,'fixed_original_data_sha256':DATA_SHA,'fixed_generic_sha256':FLOYD_SHA,'route_counts':{'primitive':1169,'two_edge':49,'full':6},'computational_definitions_unchanged':True,'proof_routing_is_not_a_hypothesis':True,'legacy_header':args.legacy_import,'checked_not_written':args.check},indent=2))
if __name__=='__main__':main()
