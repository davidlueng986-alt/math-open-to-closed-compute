// Exact finite simple cycle checker for all 3-sheet permutation covers of simple cubic base.
// Gauge: tree edges identity; each chord has permutation x -> (-1)^bit * x + a (mod 3).
// Exit status 0 means all inputs processed; a per-graph DFS cutoff is classified UNKNOWN.
#include <bits/stdc++.h>
using namespace std;
struct E {int u,v,j;};
int n,p,m,q,N,lim,deg_[64],nei[64][8];
long long nodes=0,cutoff=3000000;
vector<E> edges;
void add(int u,int v){
 if(u<0||v<0||u>=N||v>=N||deg_[u]>=8||deg_[v]>=8)abort();
 nei[u][deg_[u]++]=v;nei[v][deg_[v]++]=u;
}
void build(const vector<int>&a,int parity){
 N=n*p;
 if(N>63)abort();
 fill(deg_,deg_+N,0);
 for(auto e:edges){
  int bit=(e.j<0)?0:((parity>>e.j)&1);
  int shift=(e.j<0)?0:a[e.j];
  for(int x=0;x<3;x++)add(e.u*3+x,e.v*3+((shift+(bit?-x:x)+3)%3));
 }
 for(int i=0;i<N;i++)if(deg_[i]!=3)abort();
}
bool dfs(int root,int u,int length,uint64_t seen){
 if(++nodes>cutoff)return false;
 if(length==lim){
  for(int k=0;k<deg_[u];k++)if(nei[u][k]==root)return true;
  return false;
 }
 for(int k=0;k<deg_[u];k++){
  int v=nei[u][k];
  if(v<=root||(seen&(1ULL<<v)))continue;
  if(dfs(root,v,length+1,seen|(1ULL<<v)))return true;
 }
 return false;
}
int exists_cycle(int L){
 if(L>N)return 0;
 nodes=0;lim=L;
 for(int root=0;root<N;root++)for(int i=0;i<deg_[root];i++){
  int v=nei[root][i];
  if(v>root&&dfs(root,v,2,(1ULL<<root)|(1ULL<<v)))return 1;
  if(nodes>cutoff)return -1;
 }
 return 0;
}
int main(int argc,char**argv){
 ios::sync_with_stdio(false);cin.tie(nullptr);
 if(argc>1)cutoff=stoll(argv[1]);
 if(!(cin>>n>>p>>m>>q))return 2;
 if(p!=3)return 2;
 edges.resize(m);
 for(auto &e:edges)cin>>e.u>>e.v>>e.j;
 int parity,k;cin>>parity>>k;
 int misses[8]={};
 vector<int>a(q);
 for(int t=0;t<k;t++){
  for(int &x:a)cin>>x;
  build(a,parity);
  bool okay=true;
  for(int L:{4,8,16,32}){
   if(L>N)continue;
   int outcome=exists_cycle(L);
   if(outcome!=0){
    if(outcome<0)misses[7]++;
    else misses[(int)log2(L)]++;
    okay=false;break;
   }
  }
  if(okay){
   cout<<"WITNESS";
   for(int x:a)cout<<" "<<x;
   cout<<"\n";
  }
 }
 cout<<"STATS "<<k;
 for(int x:misses)cout<<" "<<x;
 cout<<"\n";
 return 0;
}
