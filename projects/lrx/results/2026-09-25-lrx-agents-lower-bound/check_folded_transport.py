"""Independent bounded checks of B v2 identities; not a general proof."""
import itertools, json, math
from pathlib import Path

def folded(state,c,h):
    v=[0]*len(state)
    for z,label in enumerate(state):v[label]=z-(z>c)+h
    return v

def cursor(c,h,j,d):
    q,c2=divmod(c+d,j)
    return c2,h+q

counts={"local_steps":0,"endpoint_identities":0,"geometric_bounds":0,"projection_steps":0}
for j in range(2,8):
    for state in itertools.permutations(range(j)):
        for c in range(j):
            for h in [-1,0,1]:
                before=folded(state,c,h)
                for d in [-1,1]:
                    c2,h2=cursor(c,h,j,d);after=folded(state,c2,h2)
                    change=[y-x for x,y in zip(before,after)]
                    assert sum(abs(x) for x in change)==1 and sum(change)==d
                    crossed=state[(c+1)%j] if d==1 else state[c]
                    assert change[crossed]==d
                    counts["local_steps"]+=1
                if c<j-1:
                    s=list(state);s[c],s[c+1]=s[c+1],s[c]
                    assert folded(s,c,h)==before
                    counts["local_steps"]+=1
for j in range(2,101):
    for c in range(j):
        v=j-1 if c==j-1 else j-2-c
        z=folded(list(range(j)),c,0)
        for h in [-3,0,4]:
            f=folded(list(reversed(range(j))),v,h)
            scalar=(j-1 if c==j-1 else j-2)+h
            assert all(a+b==scalar for a,b in zip(z,f));counts["endpoint_identities"]+=1
    for t in range(-2,2*j+2):
        assert sum(abs(2*i-t) for i in range(j))>=j*j//2;counts["geometric_bounds"]+=1
# A cursor edge is retained iff its clockwise start is internal to that block.
# Outside edges all map to O. A full rotation is charged to the crossed position.
for n in range(4,51):
    for a in range(2,n-1):
        b=n-a
        def proj(c,start,size):
            k=(c-start)%n
            return k if k<size-1 else size-1
        for c in range(n):
            v=(a-2-c)%n
            for start,size in [(0,a),(a,b)]:
                u1,v1=proj(c,start,size),proj(v,start,size)
                assert v1==(size-1 if u1==size-1 else size-2-u1)
            for d in [-1,1]:
                cc=(c+d)%n;crossed=(c+1)%n if d==1 else c
                charged=0
                for start,size in [(0,a),(a,b)]:
                    inside=start<=crossed<start+size
                    u1,v1=proj(c,start,size),proj(cc,start,size)
                    assert v1==((u1+d)%size if inside else u1)
                    charged+=inside
                assert charged==1;counts["projection_steps"]+=1
print(json.dumps({"status":"PASS","counts":counts,"scope":"bounded independent identity checks; not proof for all n"},indent=2))
