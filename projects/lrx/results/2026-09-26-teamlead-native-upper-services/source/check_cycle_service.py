"""Literal native interpreter checks for arbitrary cycles, not a proof or BFS."""
import json,itertools
from pathlib import Path
root=Path(__file__).resolve().parent
count=0; maximal=0; lengths=set(); signs=set()
for n in range(2,10):
 for k in range(1,n):
  # First cycle label is the initial adjacent passive label; later labels
  # occur at diverse, nonconsecutive positions, not necessarily index two.
  orders=[list(range(1,k+1)),[1]+list(range(n-1,n-k,-1))]
  for labels in orders:
   for w in [-2,-1,0,1,2]:
    for edge_w in [-1,0,1]:
     for H in [-5,0,7]:
      xs=list(range(n));h=H;z={a:H+a+n*((a%3)-1) for a in xs}
      contract=lambda v,head:v+(head-v)//n
      y={a:contract(z[a],h) for a in xs};M=n-1
      tau={a:y[b]-y[a]+M*edge_w for a,b in zip(labels,labels[1:])}
      tau[labels[-1]]=M*w-sum(tau.values())
      macro=lambda t:['X','L']*t if t>=0 else ['R','X']*(-t)
      word=['X']+sum((macro(tau[a])+['X'] for a in labels),[])
      for op in word:
       if op=='X':
        a,b=xs[:2];z[a]+=1;z[b]-=1;xs[0],xs[1]=b,a
       elif op=='L':h+=1;xs=xs[1:]+xs[:1]
       else:h-=1;xs=xs[-1:]+xs[:-1]
       assert all((z[a]-h-j)%n==0 for j,a in enumerate(xs))
      assert xs[0]==0 and h==H+M*w
      assert len(word)==1+len(labels)+2*sum(abs(t) for t in tau.values())
      assert all(contract(z[a],h)==y[a]+tau.get(a,0) for a in xs)
      count+=1;maximal=max(maximal,len(word));lengths.add(k)
      signs.update((t>0)-(t<0) for t in tau.values())
result={'all_pass':True,'cases':count,'n_range':[2,9],'cycle_sizes':sorted(lengths),
 'transport_signs':sorted(signs),'max_word_length':maximal,
 'scope':'literal native fixtures, self-audit; not independent review or all-n proof'}
(root/'CYCLE_REPLAY_4H.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
