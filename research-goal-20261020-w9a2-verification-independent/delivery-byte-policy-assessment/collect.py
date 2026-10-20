"""Read-only byte facts and conditional fingerprints; writes no source variant."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
DRAFT=ROOT/'research-goal-20261020-w9a2-delivery/draft-v5'


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    source=DRAFT/'Solution.lean';wrapper=DRAFT/'frozen-inputs/public-wrapper.lean.txt'
    raw=source.read_bytes();w=wrapper.read_bytes()
    assert sha(raw)=='650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13'
    assert sha(w)=='4813d6c2cdb05a78a6d0ed1135458c849e735ac4ab86c36c78d830fb0980e5d1'
    assert raw.endswith(w)and raw[-1:]==w[-1:]==b'\n'and raw[-2:-1]!=b'\n'
    positions=[i for i in range(len(raw)-1)if raw[i:i+2]==b'\r\n']
    assert len(positions)==raw.count(b'\r')==221
    assert len(raw)-len(raw.lstrip())==0 and len(raw)-len(raw.rstrip())==1
    conditional={'original_string_payload_without_normalization':{'bytes':len(raw),'sha256':sha(raw)},
        'only_one_terminal_LF_removed':{'bytes':len(raw)-1,'sha256':sha(raw[:-1]),
            'wrapper_bytes':len(w)-1,'wrapper_sha256':sha(w[:-1])},
        'CRLF_to_LF_then_terminal_whitespace_removed':{'bytes':len(raw.replace(b'\r\n',b'\n').rstrip()),
            'sha256':sha(raw.replace(b'\r\n',b'\n').rstrip())}}
    assert source.read_bytes()==raw and wrapper.read_bytes()==w
    evidence={'scope':'Current frozen file facts only; no current website policy inference and no source variant generated',
        'source':{'path':str(source.relative_to(ROOT)),'bytes':len(raw),'sha256':sha(raw)},
        'wrapper':{'path':str(wrapper.relative_to(ROOT)),'bytes':len(w),'sha256':sha(w)},
        'leading_whitespace_bytes':0,'trailing_whitespace_bytes':1,'trailing_byte':'LF',
        'internal_CRLF_count':221,'CRLF_byte_offsets':positions,
        'conditional_fingerprints_only_not_observed_wire':conditional,
        'generator_static_fact':'Frozen runner generate_sources appends b"\\n" plus the exact frozen wrapper bytes and does not hardcode the wrapper SHA. Gate assembler supports a new draft manifest and new complete source SHA/bytes.',
        'conditional_plan_if_policy_requires_only_trim':'Only after current official policy confirmation, a new draft could remove wrapper final LF and update complete source/parameter/manifest hashes. Five module bodies and all twelve development roots would remain byte-identical.',
        'current_official_policy_verified_by_this_report':False,'actual_wire_payload_observed':False,
        'frozen_sources_or_runners_modified':False,'normalized_source_variants_written':False,
        'compiler_export_kernel_or_website_actions':0,'main_round_counter_changed':False}
    with(HERE/'evidence.json').open('x',encoding='utf-8',newline='\n')as f:json.dump(evidence,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({'source_bytes':len(raw),'source_sha256':sha(raw),'CRLF_count':len(positions),'source_variants_written':0}))


if __name__=='__main__':main()
