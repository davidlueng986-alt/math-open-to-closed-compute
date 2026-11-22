// ERDOS-64 complete finite candidate verifier for regular C_m covers.
// Exhaustive depth-first search for each power-of-2 simple cycle.
// For N<=63, a uint64_t stores the visited vertices. Timeout = UNKNOWN.
#include <bits/stdc++.h>
using namespace std;
struct E { int u,v,j; };
int n,p,m,q,N;
vector<E> edges;
int deg_[128], adj_[128][8], target;
long long nodes;
long long cutoff=10000000;
void add_edge(int u,int v) {
  if (deg_[u]>=8 || deg_[v]>=8) abort();
  adj_[u][deg_[u]++]=v;
  adj_[v][deg_[v]++]=u;
}
bool dfs(int start,int u,int depth,uint64_t visited){
  if (++nodes>cutoff) return false;
  if (depth==target) {
    for(int k=0;k<deg_[u];k++) if(adj_[u][k]==start) return true;
    return false;
  }
  for(int k=0;k<deg_[u];k++){
    int v=adj_[u][k];
    if(v<=start || (visited & (1ULL<<v))) continue;
    if(dfs(start,v,depth+1,visited|(1ULL<<v))) return true;
  }
  return false;
}
int has_cycle(int L) {
  if(L>N)return 0;
  target=L;nodes=0;
  for(int a=0;a<N;a++)for(int i=0;i<deg_[a];i++){
    int b=adj_[a][i];
    if(b>a && dfs(a,b,2,(1ULL<<a)|(1ULL<<b)))return 1;
    if(nodes>cutoff)return -1;
  }
  return 0;
}
void build(const vector<int>& voltage){
  N=n*p;
  if(N>63)abort();
  fill(deg_,deg_+N,0);
  for(auto e:edges){
    int shift=e.j<0 ? 0 : voltage[e.j];
    for(int k=0;k<p;k++) add_edge(e.u*p+k,e.v*p+(k+shift)%p);
  }
}
int main(int argc,char**argv) {
  ios::sync_with_stdio(false);cin.tie(nullptr);
  if(argc>1)cutoff=stoll(argv[1]);
  cin>>n>>p>>m>>q;
  edges.resize(m);
  for(int i=0;i<m;i++)cin>>edges[i].u>>edges[i].v>>edges[i].j;
  int assignments;cin>>assignments;
  vector<int>x(q);
  int fail[8]={};
  int witnesses=0;
  for(int t=0;t<assignments;t++){
    for(int i=0;i<q;i++)cin>>x[i];
    build(x);
    bool good=true;
    for(int L:{4,8,16,32}){
      if(L>N)continue;
      int r=has_cycle(L);
      if(r!=0){
        fail[r>0 ? (int)log2(L) : 7]++;
        good=false;
        break;
      }
    }
    if(good){
      cout<<"WITNESS";
      for(auto a:x)cout<<" "<<a;
      cout<<"\n";
    }
  }
  cout<<"STATS "<<assignments;
  for(int i:fail)cout<<" "<<i;
  cout<<"\n";
}
