#include <bits/stdc++.h>
using namespace std;
struct V { int o,i,j; };
int H, N;
unsigned long long cnt[64];
inline bool adj(V a, V b){
  if(a.o==0 && b.o==1){ int i=a.i,j=a.j,k=b.i,l=b.j; return (k==i&&l==j-1)||(k==i&&l==j)||(k==i-1&&l==j); }
  if(a.o==1 && b.o==0){ int k=a.i,l=a.j,i=b.i,j=b.j; return (k==i&&l==j-1)||(k==i&&l==j)||(k==i-1&&l==j); }
  return false;
}
vector<V> nbr(V v){
  vector<V> out;
  if(v.o==0){ int i=v.i,j=v.j; int cand[3][2]={{i,j-1},{i,j},{i-1,j}}; for(auto&c:cand) if(c[1]>=0&&c[1]<H) out.push_back({1,c[0],c[1]}); }
  else { int k=v.i,l=v.j; int cand[3][2]={{k,l+1},{k,l},{k+1,l}}; for(auto&c:cand) if(c[1]>=0&&c[1]<H) out.push_back({0,c[0],c[1]}); }
  return out;
}
unordered_set<long long> seen;
inline long long key(V v){ return ((long long)v.o*1000000007LL + (long long)(v.i+1000000)*1000003LL + (v.j+1000000)); }
void dfs(V v,int n){
  if(v.o==1 && v.j==H-1) cnt[n]++;
  if(n==N) return;
  for(V w:nbr(v)){ long long k=key(w); if(!seen.count(k)){ seen.insert(k); dfs(w,n+1); seen.erase(k);} }
}
int main(int argc,char**argv){
  H=stoi(argv[1]); N=stoi(argv[2]);
  memset(cnt,0,sizeof(cnt));
  V s{0,0,0}; seen.insert(key(s)); dfs(s,1); seen.erase(key(s));
  cout<<"H "<<H<<" N "<<N<<"\n";
  for(int n=0;n<=N;n++) if(cnt[n]) cout<<n<<":"<<cnt[n]<<" "; cout<<"\n";
  cout<<"ratios: "; for(int n=2;n<=N;n++) if(cnt[n]&&cnt[n-2]) cout<<n<<":"<<fixed<<setprecision(5)<<pow((double)cnt[n]/cnt[n-2],1.0/2.0)<<" "; cout<<"\n";
}
