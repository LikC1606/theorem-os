import sys
from functools import lru_cache

def counts(h, N):
    # graph vertices (x,y), 0<=y<h; x shifted integer
    start=(0,0)
    # DFS iterative, record paths ending y=h-1 at each length
    out=[0]*(N+1)
    # path stack with bitset visited; path list
    # adjacency derived square grid
    def nbrs(v):
        x,y=v
        r=[]
        if y>0: r.append((x,y-1))
        if y<h-1: r.append((x,y+1))
        r.append((x-1,y)); r.append((x+1,y))
        return r
    # Use recursion h small, N maybe 34
    path=[start]; vis={start}
    def dfs(v,d):
        if d>=2 and v[1]==h-1: out[d]+=1
        if d==N: return
        for w in nbrs(v):
            if w not in vis:
                vis.add(w); path.append(w)
                dfs(w,d+1)
                path.pop(); vis.remove(w)
    dfs(start,1)
    return out

if __name__=='__main__':
    h=int(sys.argv[1]); N=int(sys.argv[2])
    o=counts(h,N)
    for n in range(1,N+1):
        if o[n]: print(n,o[n])
