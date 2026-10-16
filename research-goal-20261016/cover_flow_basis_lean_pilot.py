"""Generate a kernel-checkable edge-only pilot from four real OBBT flows."""
from pathlib import Path
import gzip,hashlib,json
from cover_correlated_replay import a
HERE=Path(__file__).parent;ROOT=HERE.parent
def vec(xs):return '!['+', '.join(str(x) for x in xs)+']'
def main():
    folder=HERE/'cover-obbt-archive';manifest=json.loads((folder/'manifest.json').read_bytes())
    shard=manifest['witness_shards'][0];raw=(folder/shard['file']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==shard['sha256']
    row=json.loads(gzip.decompress(raw))['rows'][0];state=row['old_cell']
    upper=[[a.edge_value(state,i,j) for j in range(10)] for i in range(10)]
    lines=['/- Real OBBT flow data; no global floor or zero proportion is claimed. -/',
      'import StructuralGoal20261016.FlowBasisCodec','set_option Elab.async false',
      'set_option maxHeartbeats 0','set_option maxRecDepth 100000',
      'namespace StructuralGoal20261016.FlowBasisPilot','open FlowBasisCodec',
      'def upper : Fin 10 → Fin 10 → ℤ := '+vec([vec(r) for r in upper])]
    for k,cert in enumerate(row['certificates'][:4]):
        flow=cert['flow'];edges=[(i,j) for i,j,y,u in flow['nonzero_flow']]
        lines += [f'def edges{k} : List Edge := ['+', '.join(f'({i}, {j})' for i,j in edges)+']',
          f'def coefficient{k} : Fin 10 → ℤ := '+vec(list(map(int,flow['divergence']))),
          f'def target{k} : ℤ := ({-int(flow["cost"])})',
          f'theorem checked{k} : checkBasis edges{k} upper coefficient{k} 0 target{k} = true := by decide +kernel',
          f'theorem bound{k} (x : Fin 10 → ℝ) (hx : ∀ i j, x j-x i ≤ (upper i j : ℝ)) :',
          f'    (target{k} : ℝ) ≤ ∑ i, (coefficient{k} i : ℝ)*x i := by',
          f'  simpa using checkBasis_sound edges{k} upper coefficient{k} 0 target{k} checked{k} x hx']
    lines += ['set_option pp.fullNames true']+[f'#print axioms bound{k}' for k in range(4)]
    lines += ['end StructuralGoal20261016.FlowBasisPilot']
    dest=ROOT/'StructuralGoal20261016/FlowBasisPilot.lean';dest.write_text('\n'.join(lines)+'\n',encoding='utf8')
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'manifest_sha256':hashlib.sha256((folder/'manifest.json').read_bytes()).hexdigest(),
      'witness_shard_sha256':shard['sha256'],'original_path':row['path'],
      'generated_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),
      'ordinary_Lean_passed':False,'complete_global_cover':False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out))
if __name__=='__main__':main()
