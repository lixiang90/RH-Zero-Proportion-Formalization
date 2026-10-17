"""Count actual printable source, including the retained old analytic proof.

The source skeleton is not a functional submission: the proposed Huffman
decoder/checkpoint expander and the complete Lean cover are still absent.
Even its known retained parts exceed the site's decimal 2,000,000-byte cap.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, json, sys

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
OLD=ROOT/'research-20261016-w10-cert'
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(OLD))
import prune_core
# The old public bundler's report writes core-pruning.json. Disable only that
# reporting side effect; do not modify any old function or on-disk source.
old_pruning=(OLD/'core-pruning.json').read_bytes()
prune_core.report=lambda *unused:None
import bundle
source,hashes,imports,readable,metadata=bundle.compressed_bundle(True,True,True,32768)
assert (OLD/'core-pruning.json').read_bytes()==old_pruning
previous=json.loads((OLD/'submission-size-assessment.json').read_bytes())
original=source.encode('utf8')
assert len(original)==previous['assembled_source_bytes']==5777945
assert sha(original)==previous['assembled_source_sha256']
assert hashes==previous['source_modules_sha256']
begin=source.index('/- Source: StructuralW10Cert20261016.Certificate -/')
end=source.index('/- Source: StructuralW10Cert20261016.Final -/',begin)
removed=source[begin:end].encode('utf8')
base_before=source[:begin].encode('utf8');base_after=source[end:].encode('utf8')
fixed=len(base_before)+len(base_after)
reserve=128000
reservation=('\n/- FUTURE DECODER, AUX EXPANDER, FIXED-GEOMETRY ADAPTER BUDGET; '+
             'NO IMPLEMENTATION OR LEAN VERIFICATION IS CLAIMED.\n').encode()
reservation+=b' '*(reserve-len(reservation)-4)+b'\n-/\n'
assert len(reservation)==reserve
rows=[]
for name in ['field-huffman','delta-huffman']:
    data=(HERE/(name+'-data.lean')).read_bytes()
    skeleton=base_before+data+reservation+base_after
    if name=='field-huffman':(HERE/'single-file-size-skeleton.txt').write_bytes(skeleton)
    known=fixed+len(data);budget=len(skeleton)
    def target(cap_fixed):
        # Engineering target at the observed average encoded cost. This is
        # explicitly not an information-theoretic or mathematical lower bound.
        remaining=(2000000-cap_fixed)*95615//len(data)
        return {'remaining_numeric_leaves_at_observed_average':remaining,
                'numeric_leaf_reduction':95615-remaining,
                'reduction_fraction':str(Fraction(95615-remaining,95615))}
    rows.append({'codec':name,'printable_data_source_bytes':len(data),
      'known_retained_source_bytes':known,'known_part_excess_bytes':known-2000000,
      'budgeted_decoder_expander_bytes':reserve,'budgeted_complete_source_bytes':budget,
      'budgeted_complete_source_sha256':sha(skeleton),'known_parts_under_limit':False,
      'proportional_merge_target_without_new_decoder_cost':target(fixed),
      'proportional_merge_target_with_reserved_decoder_cost':target(fixed+reserve)})
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
     'frozen_original_bundle_sha256':sha(original),'frozen_original_bundle_bytes':len(original),
     'retained_source_module_sha256':hashes,
     'Certificate_block_removed_bytes':len(removed),'Certificate_block_removed_sha256':sha(removed),
     'exact_retained_base_wrapper_license_bytes':fixed,
     'retained_encoded_analytic_base_bytes':metadata['encoded_base_source_bytes'],
     'website_limit_bytes':2000000,'rows':rows,
     'merge_target_assumptions':'Encoded bytes scale in proportion to numeric leaf count; fixed Huffman models and nonnumeric leaves are not separately reoptimized. These are engineering targets, not a proof that every compressor needs these merges.',
     'new_Lean_decoder_implemented':False,'new_Lean_compilation_performed':False,
     'complete_W10_cover_Lean_proven':False,'website_submission_ready':False,
     'new_zero_proportion_proven':False}
(HERE/'source-size-accounting.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'fixed_source_bytes':fixed,'rows':rows}))
