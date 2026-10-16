# Emulate ACSolverX substitution moves (L=24) and expand each into SAIR ac-r2-v1 elementary moves.
import sys,ast,json
import os
_D=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,_D); from aclib import red,inv
src=open(_D+'/convert.py').read()
exec(src.split('# ac-r2-v1 simulator')[1].split('def to_target')[0])  # sair, AC2SAIR, CANON, conj_moves
L=24
def decode(a):
    k1=a//(4*L)+1; rem=a%(4*L); k2t=rem//4; ij=rem%4; i=ij//2; j=ij%2
    return i,j,k1,k2t*(-1)**j-j
def rot(w,k):
    n=len(w); k%=n; return w[k:]+w[:k]
def cycred_p(w):
    p=0
    while len(w)-2*p>1 and w[p]==-w[len(w)-1-p]: p+=1
    return w[:p], w[p:len(w)-p]
def booth(w): return min(rot(w,k) for k in range(len(w)))
def s_emul(x,act):
    i,r,k1,k2=decode(act)
    A=rot(x[0],k1); B=rot(inv(x[1]) if r else x[1],k2)
    W=red(A+B)
    if len(W)>L: return x,None
    _,Wc=cycred_p(W)
    if Wc==A: return x,None
    N=booth(Wc); y=[list(x[0]),list(x[1])]; y[i]=N; return y,(i,r,k1,k2,N)
def conj_to(i,W,T):
    """moves on relator i turning freely-reduced W into T (T a rotation of cycred(W))."""
    p,Wc=cycred_p(W)
    for s in range(len(Wc)):
        if Wc[s:]+Wc[:s]==T: return conj_moves(i,inv(p+Wc[:s]))
    raise ValueError('not rotation')
def expand(x,info):
    i,r,k1,k2,N=info; mv=[]; st=[list(x[0]),list(x[1])]
    def app(ms):
        nonlocal st
        for m in ms: st=sair(st,m); mv.append(m)
    r0o=list(st[0]); 
    app(conj_to(0,st[0],rot(st[0],k1)))
    if r: app([1])
    r1e=list(st[1]); app(conj_to(1,st[1],rot(st[1],k2)))
    if i==0:
        app([2]); app(conj_to(0,st[0],N))
        app(conj_to(1,st[1],r1e))
        if r: app([1])
    else:
        app([4]); app(conj_to(1,st[1],N))
        app(conj_to(0,st[0],r0o))
    return mv,st
def run(x,path):
    x=[list(x[0]),list(x[1])]; allm=[]; nsup=0
    for a in path:
        if a<0: break
        y,info=s_emul(x,int(a)); nsup+=1
        if info is not None:
            mv,st=expand(x,info); assert st==y,(st,y); allm+=mv
        x=y
        if len(x[0])+len(x[1])==2: break
    if len(x[0])==1 and len(x[1])==1:
        suf=CANON[(tuple(x[0]),tuple(x[1]))]; allm+=suf
        for m in suf: x=sair(x,m)
        return allm,nsup,x==[[1],[2]]
    return allm,nsup,False

def booth_jax(word,Lfull=24):
    """Faithful python transcription of ACSolverX booth_lex_min_rotation_masked (padded array of size Lfull)."""
    s=list(word)+[0]*(Lfull-len(word)); length=len(word); s2=s+s
    f=[-1]*(2*Lfull); k=0
    for i in range(1,2*Lfull):
        j=f[i-k-1]
        while True:
            ijk=k+j+1
            valid=(i<length) and (ijk<length)
            neq=(s2[i]!=s2[ijk]) or (not valid)
            if not ((j!=-1) and neq): break
            if (ijk>=length) or (s2[i]<s2[ijk]): k=i-j-1
            j=f[j]
        neq2=(s2[i]!=s2[k]) or (i>=length) or (k>=length)
        if (j==-1) and neq2: f[i-k]=-1
        else: f[i-k]=j+1
        if (j==-1) and ((s2[i]!=s2[k]) or (i>=length) or (k>=length)):
            if (s2[i]<s2[k]) or (k>=length): k=i
    return k
def booth(w): return rot(w,booth_jax(w))
