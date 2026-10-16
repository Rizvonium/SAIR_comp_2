# Independent re-implementation of AC-Solver move semantics (free reduction only).
import ast, sys, collections
def red(w):
    out=[]
    for a in w:
        if out and out[-1]==-a: out.pop()
        else: out.append(a)
    return out
def inv(w): return [-a for a in reversed(w)]
# move_id -> (kind, i, arg)
MOVES={0:('m',1,+1),1:('m',0,-1),2:('m',1,-1),3:('m',0,+1),
 4:('c',1,-1),5:('c',0,-2),6:('c',1,-2),7:('c',0,1),8:('c',1,1),9:('c',0,2),10:('c',1,2),11:('c',0,-1)}
def apply(r,mid,L):
    k,i,a=MOVES[mid]; r=[list(r[0]),list(r[1])]
    if k=='m':
        j=1-i; w=red(r[i]+(r[j] if a>0 else inv(r[j])))
    else:
        w=red([a]+r[i]+[-a])
    if len(w)<=L: r[i]=w
    return r
def parse_pres(line):
    v=ast.literal_eval(line); L=len(v)//2
    return [[a for a in v[:L] if a],[a for a in v[L:] if a]],L
def S(w): return ''.join({1:'x',-1:'X',2:'y',-2:'Y'}[a] for a in w)
base=sys.argv[1]
