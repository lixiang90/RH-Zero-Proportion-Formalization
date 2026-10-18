"""One-time pure-text preparation adaptation; does not invoke generation."""
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT/'research-goal-20261018-tiny-flatten-preparation'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    oldmanifest = OLD/'prepared-files.json'
    assert sha(oldmanifest.read_bytes()) == '918b37786fb8c462169d270d0d011be69d5bf7e72f9144032f69dfa865fdd7af'
    m = json.loads(oldmanifest.read_text(encoding='utf-8'))
    for r in m['files']:
        assert sha((ROOT/r['path']).read_bytes()) == r['sha256']
    outputs = {}
    gen = (OLD/'generate_draft.py').read_text(encoding='utf-8')
    gen = gen.replace(
        "('StructuralS1RTiny20261018.Dev.Localization', 'StructuralS1RTiny20261018/Dev/Localization.lean')",
        "('StructuralS1RTiny20261018.Phase1.Localization', 'StructuralS1RTiny20261018/Phase1/Localization.lean')")
    gen = gen.replace(
        "('StructuralS1RTiny20261018.Dev.Final', 'StructuralS1RTiny20261018/Dev/Final.lean')",
        "('StructuralS1RTiny20261018.Phase1.Final', 'StructuralS1RTiny20261018/Phase1/Final.lean')")
    outputs['generate_draft.py'] = gen
    prep = (OLD/'prepare_only.py').read_text(encoding='utf-8')
    replacements = {
      'StructuralS1RTiny20261018/Dev/Localization.lean': 'StructuralS1RTiny20261018/Phase1/Localization.lean',
      '8d02de83edfced0a98a9b717a4b6c9de65d9ccc392d914084a59fda7b958f179': 'ad722eca53b43ff28ccfe9f66e338979ac05ff7088fe067dc395ea5e1c9cf758',
      'StructuralS1RTiny20261018/Dev/Final.lean': 'StructuralS1RTiny20261018/Phase1/Final.lean',
      'f4d398bc846415d6e428c07055ea799f2d70318aafeee69ab3a4864baf05b3de': 'f99f0bafbc724b657f7321cf262d3550711a9c303c18a93ac03c3b15104ec497',
      'assert module_bytes == 1_976_729': 'assert module_bytes == 1_976_894',
      "'schema':'tiny-flatten-generator-prepared-v1'": "'schema':'tiny-flatten-generator-prepared-v2'",
      "'schema':'tiny-flatten-static-preparation-v1'": "'schema':'tiny-flatten-static-preparation-v2'",
      "owned = ['generate_draft.py','prepare_only.py','official-wrapper.lean.txt','SPEC.zh.md',":
        "owned = ['generate_draft.py','prepare_only.py','adapt_v1.py','v0-to-v1.diff','version-delta.json','official-wrapper.lean.txt','SPEC.zh.md',",
    }
    for a,b in replacements.items():
        assert prep.count(a) == 1, a
        prep = prep.replace(a,b)
    old = " 'research-goal-20261018-tiny-runtime-preparation/compiler-prepared.json',"
    new = old + "\n 'research-goal-20261018-tiny-runtime-preparation/phase1-prepared.json',\n 'research-goal-20261016/gates/tiny-phase1-ordinary-20261018.json',\n 'research-goal-20261018-tiny-flatten-preparation/prepared-files.json',\n 'research-goal-20261018-tiny-flatten-preparation/generate_draft.py',"
    assert prep.count(old) == 1
    prep = prep.replace(old,new)
    outputs['prepare_only.py'] = prep
    outputs['official-wrapper.lean.txt'] = (OLD/'official-wrapper.lean.txt').read_text(encoding='utf-8')
    spec = (OLD/'SPEC.zh.md').read_text(encoding='utf-8')
    spec = spec.replace('固定顺序：CurrentPrefix、Dev.Core、Dev.Localization、Dev.Counting、Dev.Final。',
      '固定顺序：CurrentPrefix、Dev.Core、Phase1.Localization、Dev.Counting、Phase1.Final。\n模块路径更新，Lean namespace 仍为 Dev.Localization/Dev.Final；wrapper 完全不变。')
    spec = spec.replace('1,976,729 bytes', '1,976,894 bytes')
    spec = spec.replace('research-goal-20261018-tiny-flatten-preparation/generate_draft.py',
      'research-goal-20261018-tiny-flatten-preparation-v1/generate_draft.py')
    spec = spec.replace('6. 网站全流程 3200s Comparator/3240s job、8GiB 及部署限制内的真实资源证明；模块\n   cache 成功或源文本小不等于此门通过。',
      '6. 网站全流程 Comparator 3200s / job 3240s 与部署限制内的真实资源证明。\n   捕获的 8GiB 来自 `ulimit -f` 文件大小限制，不能解释成 RAM 上限；实际内存限制\n   另待部署合同确认。模块 cache 成功或源文本小不等于此门通过。未来 soleowner\n   统一 launcher 的总 t0 必须在调用本 generator 之前，纯文本生成时间同样计入\n   3200s，不先单独生成再重新起表。')
    spec += '\n## 版本与停止线\n\n旧 v0 prepared918b377…/generator ebbaaba… 保留且未执行。v1仅绑定正式授权的\n同命题API修复源与Final import-only变化，非重新选择数学目标。普通模块编译仍由\nsoleowner负责；本包既不执行它，也不预判通过。即使新普通模块通过，本 prepared\n仍不自动授权生成。须由root审查后决定统一生产launcher的唯一执行。\n'
    assert '8GiB 及部署限制' not in spec
    outputs['SPEC.zh.md'] = spec
    diff = ''.join(''.join(difflib.unified_diff(
          (OLD/name).read_text(encoding='utf-8').splitlines(keepends=True),
          data.splitlines(keepends=True), fromfile='v0/'+name,tofile='v1/'+name))
          for name,data in outputs.items())
    outputs['v0-to-v1.diff'] = diff
    for name,data in outputs.items():
        assert not (HERE/name).exists(), name
    for name,data in outputs.items():
        with (HERE/name).open('x', encoding='utf-8', newline='\n') as f:
            f.write(data)
    delta = {'schema':'tiny-flatten-preparation-v0-to-v1',
      'prior_manifest_sha256':sha(oldmanifest.read_bytes()),
      'phase1_prepared_path':'research-goal-20261018-tiny-runtime-preparation/phase1-prepared.json',
      'phase1_prepared_sha256':'3127e3c803dfb0752d140384648d3439e7e5153f006f8b31b0799c2c9f322ebc',
      'generator_algorithm_changed':False,'wrapper_bytes_changed':False,
      'module_paths_changed':['Phase1.Localization','Phase1.Final'],
      'namespace_names_changed':False,'source_threshold_changed':False,
      'trusted_constants_modified':False,'old_files_modified':False,
      'generator_executions':0,'Lean_runs':0,'mathematical_evaluations':0,
      'text_files_written':[{ 'name':name,'sha256':sha(data.encode()),'bytes':len(data.encode())}
                            for name,data in outputs.items()]}
    with (HERE/'version-delta.json').open('x',encoding='utf-8',newline='\n') as f:
        json.dump(delta,f,ensure_ascii=False,indent=2); f.write('\n')
    print(json.dumps({'adaptation_written':True,'generator_executions':0,'upload_ready':False}))

if __name__ == '__main__':
    main()
