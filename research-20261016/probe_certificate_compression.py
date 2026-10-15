"""Count cheap box checks before allocating sparse exact flow certificates."""
import hashlib,itertools,json,time
from pathlib import Path
import affine_leaf_replay as a

def main():
    st=time.time();leaves=a.collect();potential,hashes=a.potential()
    target=8598*(a.DEN//10**6);bounds=[(278528,491520),(491520,819200),(819200,13107200)]
    count=quick=needflow=0;remaining=[];cache={}
    for ix,cell in enumerate(leaves):
        choices=[[t for t,(l,u) in enumerate(bounds) if max(10*cell['lo'][r],l)<=min(10*cell['hi'][r],u)] for r in range(8)]
        for word in itertools.product(*choices):
            lo=[max(10*cell['lo'][r],bounds[t][0]) for r,t in enumerate(word)]
            hi=[min(10*cell['hi'][r],bounds[t][1]) for r,t in enumerate(word)]
            if word not in cache:cache[word]=potential(word)
            const,extra=cache[word]
            coeff=[(x+y)//10 for x,y in zip(cell['coeff'],extra)]
            assert all((x+y)%10==0 for x,y in zip(cell['coeff'],extra))
            val=cell['intercept']+const+sum(c*(l if c>=0 else u) for c,l,u in zip(coeff,lo,hi))
            count+=1
            if val>=target:quick+=1
            else:
                needflow+=1
                remaining.append({'leaf':ix,'word':list(word),'floor':val/a.DEN,'root':cell['root'],
                    'pos':cell['pos'],'reflected':cell['reflected']})
    result={'status':'exact cheap-bound size probe; infeasible pair domains still included here',
        'leaf_count':len(leaves),'cartesian_boxes':count,'cheap_box_passes':quick,
        'boxes_needing_flow_or_infeasibility':needflow,'potential_hashes':hashes,
        'seconds':time.time()-st,'remaining':remaining}
    path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='remaining'},indent=2))

if __name__=='__main__':main()
