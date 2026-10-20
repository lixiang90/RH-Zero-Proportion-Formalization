"""Source-text-only W9A2 quantitative walk preparation. No Lean or search."""
from pathlib import Path
from hashlib import sha256
import difflib
import json
import re
import os

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT/'research-goal-20261019-w9a2-record/official/proof/Solution.lean'
SOURCE_SHA = '241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7'
GEOMETRY = ROOT/'research-goal-20261019-w9a2-certificate-analysis/geometry-audit.json'
GEOMETRY_SHA = '7d860bb023594ecc4dc84308435acbdcdeb5da7d8d81991220045955575b9c67'
CORE = ROOT/'StructuralW9A220261020/Core.lean'

def pin(data): return sha256(data).hexdigest()
def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as h:
        h.write(data); h.flush(); os.fsync(h.fileno())
def replace_once(text, old, new):
    assert text.count(old) == 1, ('unique_anchor',old[:100],text.count(old))
    return text.replace(old,new,1)
def block(text, start, end):
    assert text.count(start)==text.count(end)==1,(start,end)
    return text[text.index(start):text.index(end)]

def main():
    assert not CORE.exists() and not (HERE/'core-generation.json').exists()
    raw=SOURCE.read_bytes(); gr=GEOMETRY.read_bytes()
    assert pin(raw)==SOURCE_SHA and pin(gr)==GEOMETRY_SHA
    original=raw.decode('utf-8'); text=original; geo=json.loads(gr)
    text=replace_once(text,'import ChallengeDeps.CandidateSpec\n','')
    wrapper=block(text,'section\n/-\nCopyright (c) 2026 R. Arun Chandru. Released under Apache-2.0.','/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS')
    text=replace_once(text,wrapper,'')
    leaves=geo['first24']; assert len(leaves)==24
    assert geo['source_sha256']==SOURCE_SHA
    costs=[int(x['margin'])//335544320000000000 for x in leaves]
    states=[x['state'] for x in leaves]
    assert all(len(s)==73 and s[-1]==0 for s in states)
    assert len({tuple(s) for s in states})==24
    assert all(0<=k<10**12 for k in costs)
    text=replace_once(text,'abbrev Covered : Cl → Prop := CovBy 8 PR (Pg cN 8 BS TS)\n','')
    eq=block(text,'def stEq (a b : St)','theorem covered_of_walkCP')
    text=replace_once(text,eq,'')
    states_src='def qState : ℕ → St\n'+''.join('  | '+str(k)+' => ⟨'+', '.join(map(str,s))+'⟩\n' for k,s in enumerate(states))+'  | _ => ⟨'+', '.join(['0']*73)+'⟩\n'
    costs_src='def qCost : ℕ → ℕ\n'+''.join(f'  | {k} => {v}\n' for k,v in enumerate(costs))+'  | _ => 0\n'
    added=states_src+costs_src+'''def qCell (k : ℕ) : Cl := toCl (qState k)
def qGoodIncrement : ℕ := 1000000000000
def qGoodTarget : ℕ := cN + qGoodIncrement
def qDagIncrement : ℕ := 121390593524
'''+eq+'''def qTargetFrom : List ℕ → St → ℕ
  | [], _ => qGoodTarget
  | k :: ks, s => if stEq s (qState k) then cN + qCost k else qTargetFrom ks s
def qTarget (s : St) : ℕ := qTargetFrom (List.range 24) s
def QuantGoal (g : ℕ → ℝ) : Prop :=
  Pg qGoodTarget 8 BS TS g ∨
    ∃ k, k < 24 ∧ InCell 8 PR (qCell k) g ∧ Pg (cN + qCost k) 8 BS TS g
abbrev Covered : Cl → Prop := CovBy 8 PR QuantGoal
theorem quant_forget {g : ℕ → ℝ} (h : QuantGoal g) : Pg cN 8 BS TS g := by
  rcases h with h | ⟨k, _, _, h⟩
  · rcases h with h | h
    · left
      have hh : (cN : ℝ) ≤ (qGoodTarget : ℝ) := by
        exact_mod_cast (Nat.le_add_right cN qGoodIncrement)
      exact hh.trans h
    · exact Or.inr h
  · rcases h with h | h
    · left
      have hh : (cN : ℝ) ≤ ((cN + qCost k : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_right cN (qCost k))
      exact hh.trans h
    · exact Or.inr h
theorem qTargetFrom_sound (ks : List ℕ) (hks : ∀ k ∈ ks, k < 24)
    {s : St} {g : ℕ → ℝ} (hg : InCell 8 PR (toCl s) g)
    (h : Pg (qTargetFrom ks s) 8 BS TS g) : QuantGoal g := by
  induction ks with
  | nil => exact Or.inl h
  | cons k ks ih =>
    by_cases hs : stEq s (qState k) = true
    · right
      refine ⟨k, hks k (by simp), ?_, ?_⟩
      · simpa only [qCell, St_eq hs] using hg
      · simpa only [qTargetFrom, hs, Bool.true_eq, ↓reduceIte] using h
    · apply ih (fun j hj => hks j (List.mem_cons_of_mem k hj))
      simpa only [qTargetFrom, hs, ↓reduceIte] using h
theorem qTarget_sound {s : St} {g : ℕ → ℝ}
    (hg : InCell 8 PR (toCl s) g) (h : Pg (qTarget s) 8 BS TS g) : QuantGoal g :=
  qTargetFrom_sound _ (fun _ hk => List.mem_range.mp hk) hg h
'''
    text=replace_once(text,'abbrev ST : Type :=',added+'abbrev ST : Type :=')
    text=replace_once(text,'cov_splitB (P := Pg cN 8 BS TS)','cov_splitB (P := QuantGoal)')
    checker=block(text,'def mcheckP (top : ℕ)','theorem mcheckP_ok')
    assert len(re.findall(r'\bcN\b',checker))==1
    new=replace_once(checker,'def mcheckP (top : ℕ)','def mcheckP (goalN : ℕ) (top : ℕ)')
    text=replace_once(text,checker,re.sub(r'\bcN\b','goalN',new))
    proof=block(text,'theorem mcheckP_ok ','def mleafP ')
    new=replace_once(proof,'theorem mcheckP_ok ','theorem mcheckP_ok (goalN : ℕ) ')
    new=replace_once(new,'mcheckP top bk','mcheckP goalN top bk')
    assert len(re.findall(r'\bcN\b',new))==1
    text=replace_once(text,proof,re.sub(r'\bcN\b','goalN',new))
    leaf=block(text,'def mleafP ','theorem mleafP_ok ')
    new=replace_once(leaf,'def mleafP (top : ℕ)','def mleafP (goalN : ℕ) (top : ℕ)')
    new=replace_once(new,'mcheckP top bk','mcheckP goalN top bk')
    text=replace_once(text,leaf,new)
    proof=block(text,'theorem mleafP_ok ','def fleaf ')
    new=replace_once(proof,'theorem mleafP_ok ','theorem mleafP_target_ok (goalN : ℕ) ')
    new=replace_once(new,'mleafP top bk','mleafP goalN top bk')
    new=replace_once(new,': Covered (toCl s) := by',': CovBy 8 PR (Pg goalN 8 BS TS) (toCl s) := by')
    new=replace_once(new,'(mcheckP_ok _ ','(mcheckP_ok goalN _ ')
    wrapper='''theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x))
    (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP (qTarget s) top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  intro g hg
  exact qTarget_sound hg (mleafP_target_ok (qTarget s) hlb hD hpt hR w s h g hg)
'''
    text=replace_once(text,proof,new+wrapper)
    step=block(text,'def leafStep ','theorem fleaf_ok ')
    pat=r'mleafP top bk tD bD pb R \(Nat.shiftRight w 2\) (⟨[^⟩]+⟩)'
    assert len(re.findall(pat,step))==1
    new=re.sub(pat,lambda m:'mleafP (qTarget '+m[1]+') top bk tD bD pb R (Nat.shiftRight w 2) '+m[1],step)
    text=replace_once(text,step,new)
    proof=block(text,'theorem leafStep_ok ','def WMASK ')
    new=replace_once(proof,'mleafP top bk tD bD pb R (Nat.shiftRight w 2) s','mleafP (qTarget s) top bk tD bD pb R (Nat.shiftRight w 2) s')
    new=replace_once(new,'  · intro g hg\n    right\n','  · intro g hg\n    left\n    right\n')
    text=replace_once(text,proof,new)
    proof=block(text,'theorem cert_of (cov ','\nend AMW.Cert.PC9QB6M\n')
    new=replace_once(proof,'hwin W hW hrun','hwin W hW (fun idx hi g hg => quant_forget (hrun idx hi g hg))')
    text=replace_once(text,proof,new)
    header='''/- PREPARATION ONLY: W9A2 quantitative finite-state walk.
Official source 241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7.
All original numerical payloads, kernel, guards, topology and cursors remain
unchanged. Each numerical leaf checks a state-dependent natural target.
No compiler or kernel has checked this generated variant yet.
-/
'''
    text=header+text
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b',text)
    assert not re.search(r'^\s*axiom\s',text,re.M)
    def protected(t):
        return [line for line in t.splitlines() if ' := zfNat64 ' in line
          or re.match(r'def (?:WL\d\w*|WD\d\w*|PTT\w*|COV|TOP\w*|BK\w*|REG|BND|BS|TS|PR)\b',line)
          or re.match(r'theorem rc\d+\s*:',line)]
    assert protected(text)==protected(original)
    data=text.encode('utf-8'); write(CORE,data)
    diff=''.join(difflib.unified_diff(original.splitlines(keepends=True),text.splitlines(keepends=True),fromfile='official/Solution.lean',tofile='StructuralW9A220261020/Core.lean'))
    write(HERE/'Core.diff',diff.encode('utf-8'))
    manifest={'status':'PREPARED_ONLY_NOT_COMPILED','source_sha256_start':SOURCE_SHA,'source_sha256_end':pin(SOURCE.read_bytes()),'geometry_sha256':GEOMETRY_SHA,
      'output':{'path':CORE.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':pin(data)},'added_bytes':len(data)-len(raw),
      'protected_payload_and_rc_lines_identical':True,'stale_public_wrapper_and_CandidateSpec_import_removed':True,'licenses_retained':True,'first24_state_count':24,'costs':costs,'good_increment':10**12,
      'DAG_increment':121390593524,'source_only_operations':True,'numerical_replay_search_LP_compiler_runs':0,
      'obligations':['ordinary Lean checking of new qTarget soundness and generalized mleaf proof','all original 48 rc decide+kernel must evaluate for quantitative target, with exact original cursor/end','all new Core theorem transitive permitted-axiom check','whole flattened source/runtime/Comparator/nanoda verification']}
    assert manifest['source_sha256_end']==SOURCE_SHA
    write(HERE/'core-generation.json',(json.dumps(manifest,indent=2)+'\n').encode())
    print(json.dumps(manifest))

if __name__=='__main__': main()
