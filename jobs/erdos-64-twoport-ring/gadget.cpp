// Direct finite counterexample search from two-terminal cubic-edge-deletion gadgets.
// Given a cubic F and edge e, K=F-e has two degree-2 ports, all other degrees 3.
// K is C_{2^k}-free iff e lies on every power-of-two cycle of F.
// Join t copies K in a cyclic ring by edges b_i -- a_(i+1); all degrees become 3.
// Each new simple cycle is a concatenation of simple a-b paths, one per copy,
// plus t connecting edges. Exact path-length sumsets decide the construction.
// One successful ring is a complete NO witness to the original conjecture.
#include <bits/stdc++.h>
using namespace std;
struct G {
 int n=0,m=0; vector<array<int,8>> adj; vector<int> deg; vector<vector<int>> id; vector<pair<int,int>> edges;
 explicit G(int n_):n(n_),adj(n_),deg(n_,0),id(n_,vector<int>(n_,-1)){}
 void add(int u,int v){
  if(u==v||id[u][v]>=0||deg[u]>=8||deg[v]>=8)throw runtime_error("bad edge");
  id[u][v]=id[v][u]=m++;adj[u][deg[u]++]=v;adj[v][deg[v]++]=u;edges.emplace_back(u,v);
 }
};
G from_graph6(const string&s){
 if(s.empty()||s[0]<63||s[0]>125)throw runtime_error("invalid graph6 header");
 int n=s[0]-63;G g(n);int q=0;
 for(int v=1;v<n;v++)for(int u=0;u<v;u++){
  int at=1+q/6;if(at>=(int)s.size())throw runtime_error("graph6 truncated");
  if(((s[at]-63)>>(5-q%6))&1)g.add(u,v);q++;
 }
 return g;
}
G* cur;uint64_t candidates;int cycle_len;
bool sieve_dfs(int root,int v,int dep,uint64_t used,uint64_t vertices){
 if(dep==cycle_len){
  int e=cur->id[v][root];if(e>=0){
   candidates &= used|(1ULL<<e);
   if(!candidates)return true;
  }return false;
 }
 for(int j=0;j<cur->deg[v];j++){
  int w=cur->adj[v][j];
  if(w>root&&!(vertices&(1ULL<<w)))
   if(sieve_dfs(root,w,dep+1,used|(1ULL<<cur->id[v][w]),vertices|(1ULL<<w)))return true;
 }
 return false;
}
void sieve(G&g,int len){
 if(!candidates||len>g.n)return;
 cur=&g;cycle_len=len;
 for(int u=0;u<g.n&&candidates;u++)for(int j=0;j<g.deg[u]&&candidates;j++){
  int v=g.adj[u][j];
  if(v>u)sieve_dfs(u,v,2,1ULL<<g.id[u][v],(1ULL<<u)|(1ULL<<v));
 }
}
G without_edge(const G&f,int eid){
 G g(f.n);for(int i=0;i<f.m;i++)if(i!=eid)g.add(f.edges[i].first,f.edges[i].second);return g;
}
bool has_dfs(const G&g,int root,int u,int dep,int len,uint64_t visit){
 if(dep==len)return g.id[u][root]>=0;
 for(int i=0;i<g.deg[u];i++){
  int v=g.adj[u][i];
  if(v>root&&!(visit&(1ULL<<v))&&has_dfs(g,root,v,dep+1,len,visit|(1ULL<<v)))return true;
 }return false;
}
bool has_cycle(const G&g,int len){
 if(len>g.n)return false;
 for(int root=0;root<g.n;root++)for(int j=0;j<g.deg[root];j++){
  int v=g.adj[root][j];
  if(v>root&&has_dfs(g,root,v,2,len,(1ULL<<root)|(1ULL<<v)))return true;
 }return false;
}
void terminal_paths(const G&g,int u,int v,int w,uint64_t seen,uint64_t&lens){
 if(u==v){lens|=1ULL<<w;return;}
 for(int k=0;k<g.deg[u];k++){
  int nxt=g.adj[u][k];
  if(!(seen&(1ULL<<nxt)))terminal_paths(g,nxt,v,w+1,seen|(1ULL<<nxt),lens);
 }
}
int ring_valid_t(uint64_t lens,int max_t){
 bitset<8192> reachable;reachable.set(0);
 for(int t=1;t<=max_t;t++){
  bitset<8192> next;
  for(int k=1;k<=31;k++)if(lens&(1ULL<<k))next|=(reachable<<(k+1));
  reachable=next;
  if(t<2)continue;
  bool bad=false;
  for(int p=4;p<8192;p*=2)if(reachable.test(p)){bad=true;break;}
  if(!bad)return t;
 }
 return 0;
}
uint64_t total=0,short_ok=0,all_cycle_ok=0,usable_ports=0,good_ratio=0,ring_good=0;
void process(const string&s,int n){
 G f=from_graph6(s);
 if(f.n!=n||f.m!=3*n/2)throw runtime_error("not expected cubic graph");
 for(int d:f.deg)if(d!=3)throw runtime_error("noncubic input");
 total++;candidates=(1ULL<<f.m)-1;
 sieve(f,4);sieve(f,8);
 if(!candidates)return;short_ok++;
 sieve(f,16);
 if(!candidates)return;all_cycle_ok++;
 for(int e=0;e<f.m;e++)if(candidates&(1ULL<<e)){
  G K=without_edge(f,e);auto [a,b]=f.edges[e];
  for(int u=0;u<K.n;u++)if(K.deg[u]!=(u==a||u==b?2:3))throw runtime_error("gadget degree mismatch");
  for(int L:{4,8,16})if(has_cycle(K,L))throw runtime_error("gadget has forbidden cycle");
  uint64_t lens=0;terminal_paths(K,a,b,0,1ULL<<a,lens);
  if(!lens)continue;
  usable_ports++;
  int d=__builtin_ctzll(lens),D=63-__builtin_clzll(lens);
  if(D+1<2*(d+1))good_ratio++;
  int t=ring_valid_t(lens,128);
  if(t){
   ring_good++;
   cerr<<"WITNESS base_n="<<n<<" base_g6="<<s<<" edge="<<a<<","<<b
       <<" path_length_mask="<<lens<<" d="<<d<<" D="<<D
       <<" t="<<t<<" resulting_n="<<t*n<<"\n";
  }
 }
}
int main(int argc,char**argv){
 if(argc!=2)return 2;
 int n=stoi(argv[1]);ios::sync_with_stdio(false);cin.tie(nullptr);
 string line;try{
  while(getline(cin,line)){
   if(line.empty()||line[0]=='>')continue;
   process(line,n);
  }
 }catch(const exception&e){cerr<<"FATAL: "<<e.what()<<"\n";return 1;}
 cout<<"STATS "<<n<<" "<<total<<" "<<short_ok<<" "<<all_cycle_ok
     <<" "<<usable_ports<<" "<<good_ratio<<" "<<ring_good<<"\n";
}
