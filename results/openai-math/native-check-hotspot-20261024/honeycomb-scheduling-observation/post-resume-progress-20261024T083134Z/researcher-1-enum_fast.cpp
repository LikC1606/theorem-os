#include <bits/stdc++.h>
using namespace std;
int H,N; long long cnt[64]; unsigned char vis[2][128][16]; long long nodes;
// i in [-N,N] mapped +N; j 0..H-1; o 0 up 1 down
inline void dfs(int o,int i,int j,int n){
    nodes++;
    if(o==1 && j==H-1) cnt[n]++;
    if(n==N) return;
    int ii=i+N;
    if(o==0){
        // up(i,j)->down(i,j-1),(i,j),(i-1,j)
        if(j-1>=0 && !vis[1][ii][j-1]){vis[1][ii][j-1]=1; dfs(1,i,j-1,n+1); vis[1][ii][j-1]=0;}
        if(!vis[1][ii][j]){vis[1][ii][j]=1; dfs(1,i,j,n+1); vis[1][ii][j]=0;}
        if(i-1>=-N && !vis[1][ii-1][j]){vis[1][ii-1][j]=1; dfs(1,i-1,j,n+1); vis[1][ii-1][j]=0;}
    } else {
        // down(k,l)->up(k,l+1),(k,l),(k+1,l)
        if(j+1<H && !vis[0][ii][j+1]){vis[0][ii][j+1]=1; dfs(0,i,j+1,n+1); vis[0][ii][j+1]=0;}
        if(!vis[0][ii][j]){vis[0][ii][j]=1; dfs(0,i,j,n+1); vis[0][ii][j]=0;}
        if(i+1<=N && !vis[0][ii+1][j]){vis[0][ii+1][j]=1; dfs(0,i+1,j,n+1); vis[0][ii+1][j]=0;}
    }
}
int main(int argc,char**argv){
    H=stoi(argv[1]); N=stoi(argv[2]);
    memset(cnt,0,sizeof(cnt)); memset(vis,0,sizeof(vis)); nodes=0;
    vis[0][N][0]=1; dfs(0,0,0,1); vis[0][N][0]=0;
    cout<<"H "<<H<<" N "<<N<<" nodes "<<nodes<<"\n";
    for(int n=0;n<=N;n++) if(cnt[n]) cout<<n<<":"<<cnt[n]<<" "; cout<<"\n";
    cout<<"ratios: "; for(int n=2;n<=N;n++) if(cnt[n]&&cnt[n-2]) cout<<n<<":"<<fixed<<setprecision(5)<<pow((double)cnt[n]/cnt[n-2],1.0/2.0)<<" "; cout<<"\n";
}
