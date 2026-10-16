"""Use the frozen analytic library's phase boundaries as branch landmarks.

Only the branch choice changes. All geometry and exact integer leaf checks
are inherited unchanged from ordered_generate.
"""
import ordered_generate as o

original_cut=o.g.cut
def phase_cut(state,rec):
    axis,cut=original_cut(state,rec);lo=state[0][axis];hi=state[1][axis]
    if cut==16*o.g.SC:return axis,cut
    choices=[v for v in o.g.f.BND if lo+64<v<hi-64]
    if choices:cut=min(choices,key=lambda v:abs(v-cut))
    return axis,cut
o.g.cut=phase_cut
if __name__=='__main__':o.main()
