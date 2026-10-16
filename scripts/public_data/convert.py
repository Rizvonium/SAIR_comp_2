import sys,json,ast
sys.path.insert(0,sys.argv[1]); from aclib import red,inv,parse_pres,S
A,C,OUT=sys.argv[2],sys.argv[3],sys.argv[4]
# ac-r2-v1 simulator
def sair(r,m):
    r=[list(r[0]),list(r[1])]
    if m in (0,1): r[m]=inv(r[m])
    elif m in (2,3,4,5):
        i=0 if m<4 else 1; j=1-i; o=r[j] if m%2==0 else inv(r[j]); r[i]=red(r[i]+o)
    else:
        i=0 if m<10 else 1; g={0:1,1:-1,2:2,3:-2}[(m-6)%4]; r[i]=red([g]+r[i]+[-g])
    return r
AC2SAIR={0:4,1:3,2:5,3:2,4:11,5:9,6:13,7:6,8:10,9:8,10:12,11:7}
CANON={((1,),(2,)):[],((-1,),(2,)):[0],((1,),(-2,)):[1],((-1,),(-2,)):[0,1],((-2,),(-1,)):[2,0,4,3],((-2,),(1,)):[2,5,2,8],((2,),(-1,)):[3,4,3,10],((2,),(1,)):[0,2,5,2,8]}
def conj_moves(i,word):
    # moves conjugating relator i by word u: r -> u r u^-1, letter by letter from the right end of u
    out=[]
    for g in reversed(word):
        base=6 if i==0 else 10; out.append(base+{1:0,-1:1,2:2,-2:3}[g])
    return out
def to_target(src,tgt):
    """moves transforming relator word src into word tgt where tgt is a cyclic rotation of src or src^-1 (both cyclically reduced)."""
    for pre,w in (([],src),(['inv'],inv(src))):
        n=len(w)
        for k in range(n):
            if w[k:]+w[:k]==tgt: return pre,k,w
    return None
def prefix(P,G):
    moves=[]; r=[list(P[0]),list(P[1])]
    def app(ms):
        nonlocal r
        for m in ms: r=sair(r,m); moves.append(m)
    def match(a,b): return to_target(a,b) is not None
    if not(match(r[0],G[0]) and match(r[1],G[1])):
        # swap: (a,b)->(ab,b)->(ab,a^-1)->(aba^-1,a^-1)->(b,a^-1)->(b,a)
        a=list(r[0]); app([2,5,2]); app(conj_moves(0,inv(a))); app([1])
        assert [r[0],r[1]]==[red(P[1]),red(P[0])] or True
    for i in (0,1):
        res=to_target(r[i],G[i]); assert res, (S(r[i]),S(G[i]))
        pre,k,w=res
        if pre: app([i])
        # rotate w by k: w = u v, target v u = u^-1 w u -> conjugate by u^-1
        u=r[i][:k]; app(conj_moves(i,inv(u)))
        assert r[i]==G[i],(S(r[i]),S(G[i]))
    return moves
man=json.load(open(C+'/tools/verifier/data/manifest.json'))
pool={c['challenge_id']:c for c in man['challenges']}
gs=[parse_pres(l)[0] for l in open(A+'/greedy_solved_presentations.txt')]
paths=[ast.literal_eval(l) for l in open(A+'/greedy_search_paths.txt')]
inpool=json.load(open(sys.argv[5]))
res=[];
for e in inpool:
    c=pool[e['challenge_id']]; P=c['initial_relators']; G=gs[e['greedy_idx']]
    pre=prefix(P,G)
    body=[AC2SAIR[m-1] for m,_ in paths[e['greedy_idx']][1:]]
    r=[list(P[0]),list(P[1])]
    for m in pre+body: r=sair(r,m)
    suf=CANON[(tuple(r[0]),tuple(r[1]))]
    for m in suf: r=sair(r,m)
    assert r==[[1],[2]]
    full=pre+body+suf
    res.append({'challenge_id':c['challenge_id'],'moves':full,'len':len(full),'prefix_len':len(pre),'source':'shehper/AC-Solver greedy_search_paths.txt line %d'%(e['greedy_idx']+1)})
json.dump(res,open(OUT,'w'),indent=0)
L=sorted(x['len'] for x in res); print('verified',len(res),'lengths min/med/max',L[0],L[len(L)//2],L[-1])
with open(OUT.replace('.json','_submission.txt'),'w') as f:
    for x in res: f.write('%s: %s # from AC-Solver greedy path (MIT, shehper/AC-Solver@fd65d8f)\n'%(x['challenge_id'],json.dumps(x['moves'])))
