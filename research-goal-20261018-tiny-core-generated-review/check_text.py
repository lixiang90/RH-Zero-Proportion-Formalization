"""Read-only inverse text projection. No generator import or proof evaluation."""
from hashlib import sha256
import difflib
import json
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PREP=ROOT/'research-goal-20261018-tiny-core-preparation'
def read(p):return p.read_bytes().decode('utf8')
def digest(p):return sha256(p.read_bytes()).hexdigest()
def once(s,a,b):assert s.count(a)==1,(a[:80],s.count(a));return s.replace(a,b,1)
def block(s,a,b):
    assert s.count(a)==s.count(b)==1
    return s[s.index(a):s.index(b)]
def main():
    assert not (HERE/'text-review.json').exists()
    src=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
    core=ROOT/'StructuralS1RTiny20261018/Core.lean'
    assert digest(src)=='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
    assert digest(core)=='9fbdf3f2dc62333b636d3b25dfb3bf2b15e3b8c628ece73d6ba1bc768fc5f1a6'
    original,new=read(src),read(core)
    v0=read(PREP/'generate_core.py');v1=read(PREP/'generate_core_v1.py')
    expected=once(v0,"'hwin W hW hrun\\n',","'hwin W hW hrun',")
    expected=once(expected,"'hwin W hW (fun idx hi g hg => tiny_forget (hrun idx hi g hg))\\n')", "'hwin W hW (fun idx hi g hg => tiny_forget (hrun idx hi g hg))')")
    assert v1==expected
    diff=''.join(difflib.unified_diff(original.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='accepted/Solution.lean',tofile='StructuralS1RTiny20261018/Core.lean'))
    assert diff==read(PREP/'Core.diff')
    text=new
    header=block(text,'/- PREPARATION ONLY:','/- Performance update:')
    assert header.endswith('-/\n') and header.count('\n')==8
    text=once(text,header,'')
    text=once(text,'noncomputable def tinyDeltaN : ℕ := 389500523\nnoncomputable def tinyTauN : ℕ := cN + 2 * tinyDeltaN\n','')
    old_eq=block(original,'noncomputable def stEq (a b : St)','theorem covered_of_walkCP')
    added=block(text,'noncomputable def tinyExceptionState : St','abbrev ST : Type :=')
    assert block(added,'noncomputable def stEq (a b : St)','noncomputable def tinyTarget')==old_eq
    state_line=re.search(r'(?m)^noncomputable def tinyExceptionState : St := ⟨([^⟩]+)⟩$',added)[1]
    stated=[int(s.strip()) for s in state_line.split(',')]
    exception=json.loads((ROOT/'research-goal-20261018-tiny-overlap-independent/unique-exception.json').read_text(encoding='utf8'))
    e=exception['state'];expected_state=[v for pair in zip(e['L']+e['A'],e['U']+e['B']) for v in pair]+[e['M']]
    assert stated==expected_state and len(stated)==73
    assert 'if stEq s tinyExceptionState = true then cN else tinyTauN' in added
    assert 'Pg tinyTauN 8 BS TS g ∨ (InCell 8 PR tinyExceptionCell g ∧ Pg cN 8 BS TS g)' in added
    text=once(text,added,'')
    text=once(text,'structure St where\n','abbrev Covered : Cl → Prop := CovBy 8 PR (Pg cN 8 BS TS)\nstructure St where\n')
    text=once(text,'theorem covered_of_walkCP',old_eq+'theorem covered_of_walkCP')
    text=once(text,'cov_splitB (P := TinyGoal)','cov_splitB (P := Pg cN 8 BS TS)')
    check=block(text,'noncomputable def mcheckP ','theorem mcheckP_ok ')
    normal=once(check,'def mcheckP (goalN : ℕ) (top : ℕ)','def mcheckP (top : ℕ)')
    assert len(re.findall(r'\bgoalN\b',normal))==1
    normal=re.sub(r'\bgoalN\b','cN',normal)
    assert normal==block(original,'noncomputable def mcheckP ','theorem mcheckP_ok ')
    text=once(text,check,normal)
    proof=block(text,'theorem mcheckP_ok ','noncomputable def mleafP ')
    normal=once(proof,'theorem mcheckP_ok (goalN : ℕ) ','theorem mcheckP_ok ')
    normal=once(normal,'mcheckP goalN top bk','mcheckP top bk')
    assert len(re.findall(r'\bgoalN\b',normal))==1
    normal=re.sub(r'\bgoalN\b','cN',normal)
    assert normal==block(original,'theorem mcheckP_ok ','noncomputable def mleafP ')
    text=once(text,proof,normal)
    leaf=block(text,'noncomputable def mleafP ','/- Eliminate forced decoder values')
    normal=once(leaf,'def mleafP (goalN : ℕ) (top : ℕ)','def mleafP (top : ℕ)')
    normal=once(normal,'mcheckP goalN top bk','mcheckP top bk')
    assert normal==block(original,'noncomputable def mleafP ','/- Eliminate forced decoder values')
    text=once(text,leaf,normal)
    generic=block(text,'theorem mleafP_target_ok ','theorem mleafP_ok ')
    normal=once(generic,'theorem mleafP_target_ok (goalN : ℕ) ','theorem mleafP_ok ')
    normal=once(normal,'mleafP goalN top bk','mleafP top bk')
    normal=once(normal,': CovBy 8 PR (Pg goalN 8 BS TS) (toCl s) := by',': Covered (toCl s) := by')
    normal=once(normal,'(mcheckP_ok goalN _ ','(mcheckP_ok _ ')
    assert normal==block(original,'theorem mleafP_ok ','noncomputable def fleaf ')
    wrapper=block(text,'theorem mleafP_ok ','noncomputable def fleaf ')
    assert 'tiny_target_sound hg (mleafP_target_ok (tinyTarget s) hlb hD hpt hR w s h g hg)' in wrapper
    text=once(text,generic+wrapper,normal)
    step=block(text,'noncomputable def leafStep ','theorem fleaf_ok ')
    normal,n=re.subn(r'mleafP \(tinyTarget (⟨[^⟩]+⟩)\) top bk tD bD pb R \(Nat.shiftRight w 2\) (⟨[^⟩]+⟩)',lambda m:('mleafP top bk tD bD pb R (Nat.shiftRight w 2) '+m[2]) if m[1]==m[2] else 'INVALID_DIFFERENT_TARGET_STATE',step)
    assert n==1 and normal==block(original,'noncomputable def leafStep ','theorem fleaf_ok ')
    text=once(text,step,normal)
    step_proof=block(text,'theorem leafStep_ok ','noncomputable def WMASK ')
    normal=once(step_proof,'mleafP (tinyTarget s) top bk','mleafP top bk')
    normal=once(normal,'  · intro g hg\n    left\n    right\n','  · intro g hg\n    right\n')
    assert normal==block(original,'theorem leafStep_ok ','noncomputable def WMASK ')
    text=once(text,step_proof,normal)
    text=once(text,'hwin W hW (fun idx hi g hg => tiny_forget (hrun idx hi g hg))','hwin W hW hrun')
    assert text==original,'unaccounted_source_difference'
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b',new)
    assert not re.search(r'(?m)^\s*axiom\s',new)
    result={'schema':'tiny-generated-Core-independent-inverse-text-review-v1','passed_text_identity':True,
        'Core_sha256':digest(core),'Core_bytes':core.stat().st_size,'generator_v1_sha256':digest(PREP/'generate_core_v1.py'),
        'generator_v1_only_two_anchor_newline_escapes_removed':True,'diff_matches_actual_source_bytes':True,
        'full_73_exception_state_matches_independent_original':True,
        'all_mcheckP_guards_and_other_arithmetic_byte_identical_after_only_goal_parameter':True,
        'mleafP_decoder_and_flow_byte_identical_except_goal_forwarding':True,
        'leafStep_target_and_actual_state_literals_identical':True,
        'all_remaining_source_bytes_equal_after_documented_inverse_projection':True,
        'no_new_axiom_or_sorry_or_native_decide':True,'new_Lean_or_mathematical_runs':0,
        'static_logical_review':'TinyGoal/wrapper/reflection/forgetting reviewed; no concrete error found',
        'compile_cursor_dichotomy_pair_counting_final_export_still_pending':True}
    with (HERE/'text-review.json').open('x',encoding='utf8') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result))
if __name__=='__main__':main()
