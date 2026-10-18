"""Fixed O byte inventory only: no producer import or mathematical evaluation.

Writes two predetermined UTF-8 Lean *data* texts. They are not compiled or
claimed to contain the missing proof consumer. All rationals retain the exact
saved numerator/denominator; no rounding, pruning or encoding family search.
"""
from pathlib import Path
from hashlib import sha256
import gzip
import json
import os
import sys
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PACKET='research-goal-20261018-stageO-fixed-curvature-preparation/curvature-packet.json'
PACKET_SHA='a952a8bd239bddaa0c8d1f24b45a5096cb3a3b6ff19f067baaba46686eb11cbf'
O_MANIFEST='research-goal-20261018-stageO-fixed-curvature-preparation/files.json'
O_MANIFEST_SHA='9eeb39270ad6853ee7ad3472c0446237ad21b64be0db442815e2566bfe97191b'
READOUT='research-goal-20261018-stageN2-pooled-component-resumption/first-Below-readout.json'
READOUT_SHA='3ade873c5f40f065876c8c1917aec528593171514d5dfd54a35ef16b24316324'
SOURCE='research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_SHA='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode('ascii')+b'\n'
def row(p):return {'path':rel(p),'bytes':p.stat().st_size,'sha256':pin(p)}
def write_bytes(p,b):
    with p.open('xb') as f:f.write(b);f.flush();os.fsync(f.fileno())
def write_json(p,x):write_bytes(p,(json.dumps(x,indent=2,allow_nan=False)+'\n').encode('utf-8'))
def rational_parts(text):
    parts=text.split('/');assert len(parts) in (1,2)
    n=int(parts[0]);d=int(parts[1]) if len(parts)==2 else 1
    assert d>0
    return n,d
def int_literal(n):return str(n) if n>=0 else '('+str(n)+')'
def rat(text):
    n,d=rational_parts(text);return 'qr '+int_literal(n)+' '+str(d)
def list_block(name,ty,items):
    return 'def '+name+' : List '+ty+' := [\n'+',\n'.join('  '+v for v in items)+'\n]\n'
def naturals(xs):return '['+', '.join(str(v) for v in xs)+']'
def read_original_record(desc):
    p=ROOT/desc['path']
    with p.open('rb') as f:f.seek(desc['offset']);b=f.read(desc['bytes'])
    assert len(b)==desc['bytes'] and sha256(b).hexdigest()==desc['compressed_member_sha256']
    raw=gzip.decompress(b);assert sha256(raw).hexdigest()==desc['decoded_sha256']
    value=json.loads(raw);assert canonical(value)==raw;return value
def integer_statistics(texts):
    integers=[];denominators=[]
    for text in texts:
        n,d=rational_parts(text);integers.append(abs(n));integers.append(d);denominators.append(d)
    def stats(values):return {'maximum_decimal_digits':max(len(str(v)) for v in values),
        'maximum_bit_length':max(v.bit_length() for v in values)}
    return {'integer_numerator_or_denominator':stats(integers),'denominator_only':stats(denominators),
        'rational_literal_count':len(texts),'measurement_only_no_rational_reduction_or_evaluation':True}

def main():
    for name in ['LiteralOnePair.lean','SelectorOnePair.lean','inventory.json','files.json']:
        assert not (HERE/name).exists(),('single_fixed_format_inventory_no_retry',name)
    for name,h in [(PACKET,PACKET_SHA),(O_MANIFEST,O_MANIFEST_SHA),(READOUT,READOUT_SHA),(SOURCE,SOURCE_SHA)]:assert pin(ROOT/name)==h
    packet=load(ROOT/PACKET);readout=load(ROOT/READOUT);record=read_original_record(readout['proof_record'])
    assert packet['G_index']==record['G_index']==1322606
    assert packet['pair']==record['pair']==[278,665] and packet['chart']==record['chart']=='rev/id'
    exact=record['normalized_exact_reconstruction'];weights=exact['exact_dual']['raw_row_weights']
    bases=exact['support_plan']['base_rows'];unknowns=[d['row_id'] for d in exact['exact_dual']['normalized_columns']]
    cells=packet['selected_original_CellA_cells'];anchors=packet['weighted_anchor_rows'];pstar=packet['laplace_proof']['p_star']
    assert len(weights)==305 and len(bases)==42 and len(unknowns)<=9
    assert len(cells)==23 and len(anchors)==49 and len(pstar)==10 and pstar[0]=='0'
    assert packet['laplace_proof']['gauge_vertex_per_component']==[0]
    cell_index={(c['L'],c['U']):i for i,c in enumerate(cells)};assert len(cell_index)==23
    original_selectors={}
    for a in anchors:
        for c in a['original_cells']:
            key=(c['L'],c['U']);sel=(c['chain'],c['ordinal'])
            if key in original_selectors:assert original_selectors[key]==sel
            original_selectors[key]=sel
    assert set(original_selectors)==set(cell_index)
    cell_selectors=[original_selectors[(c['L'],c['U'])] for c in cells]
    header=('-- Data-only byte inventory for fixed G1322606. No proof consumer.\n'
        '-- No compilation, source-acceptance or global-floor claim.\nimport Mathlib\n')
    target='def targetNumerator : Nat := 893766123055294719\ndef targetDenominator : Nat := 100000000000000000000\n'
    literal_sections=[]
    literal_sections.append(('header',header+'namespace OOnePairLiteral\n'+
        'def qr (n : Int) (d : Nat) : Rat := (n : Rat) / (d : Rat)\n'+
        'def originalCells : Nat × Nat := (278, 665)\ndef chart : Nat := 2\n'+target))
    literal_sections.append(('raw_dual_305',list_block('rawDual','Rat',[rat(v) for v in weights])))
    cell_items=[]
    for c,(chain,ordinal) in zip(cells,cell_selectors):
        cell_items.append('('+str(chain)+', '+str(ordinal)+', '+str(c['L'])+', '+str(c['U'])+', '+rat(c['m_quantitative'])+')')
    literal_sections.append(('original_CellA_23_m',list_block('cellCurvature','(Nat × Nat × Nat × Nat × Rat)',cell_items)))
    anchor_items=[]
    for a in anchors:
        i,j=a['physical_span'];ids=[cell_index[(c['L'],c['U'])] for c in a['original_cells']]
        anchor_items.append('('+', '.join(map(str,[a['row_id'],i,j,a['q_integer']]))+', '+naturals(ids)+')')
    literal_sections.append(('anchor_row_49_mapping',list_block('anchorRows','(Nat × Nat × Nat × Nat × List Nat)',anchor_items)))
    literal_sections.append(('p_star_9_rationals',list_block('pStarWithoutGauge0','Rat',[rat(v) for v in pstar[1:]])))
    literal_sections.append(('footer','end OOnePairLiteral\n'))
    literal_text='\n'.join(s for _,s in literal_sections);write_bytes(HERE/'LiteralOnePair.lean',literal_text.encode('utf-8'))
    selector_sections=[]
    selector_sections.append(('header',header+'namespace OOnePairSelectors\n'+
        'def originalCells : Nat × Nat := (278, 665)\ndef chart : Nat := 2\n'+target))
    selector_sections.append(('group_base_row_42',list_block('groupBaseRows','Nat',[str(x) for x in bases])))
    selector_sections.append(('normalized_unknown_row_IDs',list_block('normalizedUnknownRows','Nat',[str(x) for x in unknowns])))
    selector_sections.append(('positive_anchor_row_49_IDs',list_block('positiveAnchorRows','Nat',[str(a['row_id']) for a in anchors])))
    selector_sections.append(('original_REG_23_selectors',list_block('originalRegCells','(Nat × Nat)',[
        '('+str(k)+', '+str(t)+')' for k,t in cell_selectors])))
    selector_sections.append(('footer','end OOnePairSelectors\n'))
    selector_text='\n'.join(s for _,s in selector_sections);write_bytes(HERE/'SelectorOnePair.lean',selector_text.encode('utf-8'))
    def sections(xs):
        return [{'section':name,'utf8_bytes':len(s.encode('utf-8'))} for name,s in xs]+[
            {'section':'join_newlines','utf8_bytes':len(xs)-1}]
    rationals={'raw_dual':weights,'cell_m':[c['m_quantitative'] for c in cells],'p_star':pstar[1:]}
    result={'schema':'O-fixed-pair-two-explicit-source-format-byte-inventory-v1','fixed_G_index':1322606,
        'source_and_data_input_sha256':{PACKET:PACKET_SHA,O_MANIFEST:O_MANIFEST_SHA,READOUT:READOUT_SHA,SOURCE:SOURCE_SHA},
        'original_record_member':readout['proof_record'],
        'literal_format':{'source':row(HERE/'LiteralOnePair.lean'),'section_bytes':sections(literal_sections),
            'raw_dual_rationals':305,'original_CellA_m_rationals':23,'anchor_mappings':49,'p_star_rationals':9,
            'integer_statistics_by_field':{k:integer_statistics(v) for k,v in rationals.items()},
            'combined_integer_statistics':integer_statistics(sum(rationals.values(),[]))},
        'selector_format':{'source':row(HERE/'SelectorOnePair.lean'),'section_bytes':sections(selector_sections),
            'group_base_rows':len(bases),'normalized_unknown_rows':len(unknowns),
            'saved_normalized_rank_metadata':exact['exact_dual']['normalized_rank'],
            'positive_anchor_row_ids':49,'original_REG_cell_selectors':23,
            'reconstruction_contract_only_not_implemented_in_Lean':True,
            'deterministic_required_steps':['decode_same_original_source_cells_FS_and_pooled_groups',
                'normalize_selected_raw_columns_by_abs_delta_S_and_solve_fixed_support_with_free_unknowns0',
                'restore_raw_mu_and_verify_all52_nonnegative_balance_cost',
                'evaluate_original_REG_CellA_cells_and_verify_guards_quantitative_m',
                'reconstruct_fixed_hulls_and_m_min_and_original_anchor_rows',
                'form_same_nonnegative_c_and_exact_component_gauge_Laplace_solution',
                'verify_full10_stationarity_and_uniform_payment_against_target']},
        'proof_consumer_source_and_runtime_bytes_not_counted':True,'Lean_parser_or_kernel_runs':0,
        'curvature_FS_matrix_solver_new_point_evaluations':0,
        'no_rounding_compression_parameter_search_or_alternate_format_trials':True,
        'JSON_or_gzip_bytes_are_not_submission_source_bytes':True,
        'one_pair_only_no_extrapolation_to_remaining_pairs':True,
        'uploaded_merged_Lean_source_size_or_acceptance_proven':False}
    assert sum(x['utf8_bytes'] for x in result['literal_format']['section_bytes'])==len(literal_text.encode('utf-8'))
    assert sum(x['utf8_bytes'] for x in result['selector_format']['section_bytes'])==len(selector_text.encode('utf-8'))
    write_json(HERE/'inventory.json',result)
    print(json.dumps({'literal_source_bytes':len(literal_text.encode('utf-8')),
        'selector_source_bytes':len(selector_text.encode('utf-8')),'raw_dual_count':305,
        'normalized_unknown_selectors':len(unknowns),'stats':result['literal_format']['combined_integer_statistics'],
        'Lean_or_curvature_or_matrix_runs':0}))
if __name__=='__main__':main()
