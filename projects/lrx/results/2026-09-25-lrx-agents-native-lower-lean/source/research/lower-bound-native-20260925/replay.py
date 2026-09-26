"""Independent finite native-list diagnostics; never an arbitrary-n proof. Python stdlib only."""
from itertools import permutations,product
import json

def native(op,xs):
 if op=='L':return xs[1:]+xs[:1]
 if op=='R':return xs[-1:]+xs[:-1]
 return xs[1::-1]+xs[2:]
def reflect(xs):return xs[1::-1]+xs[:1:-1]
def view(pa,pb,c):
 n=len(pa)+len(pb);t=[None]*n
 for label,pos in enumerate(pa):t[pos]=label
 for label,pos in enumerate(pb,start=len(pa)):t[len(pa)+pos]=label
 return t[c:]+t[:c]

def main():
 transitions=endpoints=patterns=contiguous=0
 for a in range(1,5):
  for b in range(1,5):
   n=a+b
   for pa in permutations(range(a)):
    for pb in permutations(range(b)):
     for c in range(n):
      xs=view(pa,pb,c)
      for h in (-1,0,1):
       assert view(pa,pb,(c+1)%n)==native('L',xs)
       hn=h+(c+1==n);cp=(c+1)%n
       assert n*hn+cp==n*h+c+1
       assert view(pa,pb,(c-1)%n)==native('R',xs)
       hn=h-(c==0);cp=(c-1)%n
       assert n*hn+cp==n*h+c-1
       transitions+=2
       if (xs[0]<a)==(xs[1]<a):
        assert c+1<n and c+1!=a
        qa=list(pa);qb=list(pb)
        x,y=xs[:2]
        if x<a:qa[x],qa[y]=qa[y],qa[x]
        else:qb[x-a],qb[y-a]=qb[y-a],qb[x-a]
        assert view(qa,qb,c)==native('X',xs)
        transitions+=1
      for c0 in range(n):
       if xs==reflect(view(tuple(range(a)),tuple(range(b)),c0)):
        assert all(pa[x]+x+1==a for x in range(a))
        assert all(pb[x]+x+1==b for x in range(b))
        assert (c+c0+2)%n==a
        endpoints+=1
 for n in range(2,11):
  for colors in product((0,1),repeat=n):
   patterns+=1
   criterion=True
   for x in range(n):
    for y in range(x+1,n):
     if colors[x]!=colors[y]:continue
     kept=[z for z in range(n) if z in (x,y) or colors[z]!=colors[x]]
     i,j=kept.index(x),kept.index(y)
     if (i+1)%len(kept)!=j and (j+1)%len(kept)!=i:criterion=False
   cuts=[i for i in range(n) if colors[i]!=colors[(i+1)%n]]
   assert criterion==(len(cuts)<=2)
   if not criterion:continue
   contiguous+=1
   # Construct the three runs rooted at label zero, then rotate the suffix.
   i=0
   while i<n and colors[i]==colors[0]:i+=1
   j=i
   while j<n and colors[j]!=colors[0]:j+=1
   assert all(colors[k]==colors[0] for k in range(j,n))
   p=list(range(j,n))+list(range(i));q=list(range(i,j))
   rotated=list(range(j,n))+list(range(j))
   assert rotated==p+q
   assert all(colors[k]==colors[0] for k in p)
   assert all(colors[k]!=colors[0] for k in q)
 return {'status':'PASS','local_native_transitions':transitions,'reflection_endpoints':endpoints,'binary_patterns':patterns,'patterns_satisfying_contiguity':contiguous,'scope':'a,b=1..4, all within-arc permutations/cursors; winding -1,0,1; binary patterns n=2..10. No BFS; diagnostic only.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
