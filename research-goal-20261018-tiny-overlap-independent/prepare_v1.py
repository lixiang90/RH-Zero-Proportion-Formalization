"""Version the explicit parent-authorized final score-wiring repair only."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
old=(HERE/'audit_once.py').read_text(encoding='utf8')
assert not (HERE/'audit_once_v1.py').exists()
before="H=F(overlap['new_window_floor_H']);current=F(overlap['record_ratio_recovered_from_source_parameters'])"
after="H=F(overlap['new_window_floor_H'])-F(overlap['new_total_pressure_B9']);current=F(overlap['record_ratio_recovered_from_source_parameters'])"
assert old.count(before)==1
new=old.replace(before,after)
before2="candidate=H/(1-c);assert candidate>current"
after2="candidate=H/(1-c);assert candidate>current\n    cross=candidate.numerator*current.denominator-current.numerator*candidate.denominator;assert cross>0"
assert new.count(before2)==1;new=new.replace(before2,after2)
before3="'candidate_minus_current_exact':str(candidate-current),'candidate_strictly_exceeds_fresh_current':True,"
after3="'candidate_minus_current_exact':str(candidate-current),'candidate_strictly_exceeds_fresh_current':True,\n        'strict_comparison_cross_integer':str(cross),'score_identity':'(window_H-pressure_B9)/(1-joint_floor)',\n        'metadata_read_passes':2,'extra_metadata_read_due_to_authorized_ratio_wiring_fix':True,\n        'original_failed_source_and_terminal_preserved':True,"
assert new.count(before3)==1;new=new.replace(before3,after3)
with (HERE/'audit_once_v1.py').open('x',encoding='utf8') as f:f.write(new)
print('Prepared v1 only: pressure subtraction, explicit cross integer, repair provenance; fixed metadata/math selection unchanged.')
