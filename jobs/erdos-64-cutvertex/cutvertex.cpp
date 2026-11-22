// Exhaustive edge-subdivision / cut-vertex disproof search for Erdős #64.
// Generate connected cubic F. Subdivide edge e to H; two copies of H glued
// at the new 2-valent vertex form a minimum-degree-3 graph D(F,e).
// Exact criterion: e is in every (4,8,16)-cycle of F and in no
// (3,7,15)-cycle of F. Each surviving e is rechecked independently on H.
// No 32-cycle can appear in D because the glue vertex is a cut-vertex
// and each copy H has <=25 vertices. This searches an exact subclass only.
#include <bits/stdc++.h>
using namespace std;
struct G {
 int n=0,m=0;
 vector<array<int,8>> adj;
 vector<int> degree;
 vector<vector<int>> eid;
 vector<pair<int,int>> edges;
 G(int k=0):n(k),adj(k),degree(k,0),eid(k,vector<int>(k,-1)){}
 void add(int u,int v){
  if(u==v||eid[u][v]>=0||degree[u]>=8||degree[v]>=8)throw runtime_error("invalid edge");
  eid[u][v]=eid[v][u]=m++;
  edges.emplace_back(u,v);
  adj[u][degree[u]++]=v;adj[v][degree[v]++]=u;
 }
};
G decode(const string&s){
 if(s.empty()||s[0]<63||s[0]>125)throw runtime_error("bad graph6 header");
 int n=s[0]-63;G g(n);int pos=0;
 for(int j=1;j<n;j++)for(int i=0;i<j;i++){
  int at=1+pos/6;
  if(at>=(int)s.size())throw runtime_error("incomplete graph6");
  if(((s[at]-63)>>(5-pos%6))&1)g.add(i,j);
  pos++;
 }
 return g;
}
string encode(const G&g){
 if(g.n>=63)throw runtime_error("large graph6");
 string out(1,char(g.n+63));int b=0,k=0;
 for(int j=1;j<g.n;j++)for(int i=0;i<j;i++){
  b=(b<<1)+(g.eid[i][j]>=0);k++;
  if(k==6){out.push_back(char(63+b));b=k=0;}
 }
 if(k)out.push_back(char(63+(b<<(6-k))));
 return out;
}
G* current;
int target,mode;
uint64_t possible;
bool dfs_sieve(int start,int u,int depth,uint64_t seen,uint64_t used){
 if(depth==target){
  int e=current->eid[u][start];
  if(e>=0){
   uint64_t cyc=used|(1ULL<<e);
   if(mode==0)possible &=cyc;
   else possible &=~cyc;
   if(possible==0)return true;
  }
  return false;
 }
 for(int i=0;i<current->degree[u];i++){
  int v=current->adj[u][i];
  if(v<=start||(seen&(1ULL<<v)))continue;
  if(dfs_sieve(start,v,depth+1,seen|(1ULL<<v),
               used|(1ULL<<current->eid[u][v])))return true;
 }
 return false;
}
void sieve(G&g,int L,int op){
 if(!possible||L>g.n)return;
 current=&g;target=L;mode=op;
 for(int root=0;root<g.n&&possible;root++)
  for(int j=0;j<g.degree[root]&&possible;j++){
   int v=g.adj[root][j];
   if(v>root)dfs_sieve(root,v,2,(1ULL<<root)|(1ULL<<v),
                      1ULL<<g.eid[root][v]);
  }
}
bool dfs_cycle(const G&g,int root,int u,int dep,int len,uint64_t seen){
 if(dep==len)return g.eid[u][root]>=0;
 for(int i=0;i<g.degree[u];i++){
  int v=g.adj[u][i];
  if(v>root&&!(seen&(1ULL<<v))&&
     dfs_cycle(g,root,v,dep+1,len,seen|(1ULL<<v)))return true;
 }
 return false;
}
bool has_cycle(const G&g,int L){
 if(L>g.n)return false;
 for(int i=0;i<g.n;i++)for(int j=0;j<g.degree[i];j++){
  int v=g.adj[i][j];
  if(v>i&&dfs_cycle(g,i,v,2,L,(1ULL<<i)|(1ULL<<v)))return true;
 }
 return false;
}
G subdivision(const G&f,int omitted){
 G h(f.n+1);
 for(int i=0;i<f.m;i++)if(i!=omitted)
  h.add(f.edges[i].first,f.edges[i].second);
 auto [a,b]=f.edges[omitted];
 h.add(a,f.n);h.add(b,f.n);
 return h;
}
G glue(const G&h){
 const int special=h.n-1,n=h.n;
 G g(2*n-1);
 for(auto [a,b]:h.edges){
  g.add(a==special?2*n-2:a,b==special?2*n-2:b);
  g.add(a==special?2*n-2:a+n-1,b==special?2*n-2:b+n-1);
 }
 return g;
}
long long total=0,after8=0,after16=0,final_edges=0,witness=0;
void process(const string&line,int n){
 G f=decode(line);
 if(f.n!=n||f.m!=3*n/2||encode(f)!=line)
  throw runtime_error("graph6 census parser mismatch");
 for(int d:f.degree)if(d!=3)throw runtime_error("noncubic generator output");
 total++;
 possible=(1ULL<<f.m)-1;
 sieve(f,4,0);sieve(f,8,0);
 if(!possible)return;
 after8++;
 sieve(f,3,1);sieve(f,7,1);
 if(!possible)return;
 sieve(f,16,0);
 if(!possible)return;
 after16++;
 sieve(f,15,1);
 if(!possible)return;
 for(int e=0;e<f.m;e++)if(possible&(1ULL<<e)){
  final_edges++;
  G h=subdivision(f,e);
  if(has_cycle(h,4)||has_cycle(h,8)||has_cycle(h,16))
   throw runtime_error("independent exact witness verification failed");
  G g=glue(h);
  if(g.n!=2*n+1||g.m!=3*n+3)
   throw runtime_error("witness graph size invariant failed");
  for(int d:g.degree)if(d<3)
   throw runtime_error("witness min-degree invalid");
  // Any simple cycle of g lies in one copy of h, as shared vertex is cut.
  witness++;
  cerr<<"WITNESS n="<<g.n<<" base6="<<line
      <<" removed_edge="<<f.edges[e].first<<","<<f.edges[e].second
      <<" witness6="<<encode(g)<<"\n";
 }
}
int main(int argc,char**argv){
 ios::sync_with_stdio(false);cin.tie(nullptr);
 if(argc!=2)return 2;
 int n=stoi(argv[1]);string line;
 try{
  while(getline(cin,line)){
   if(line.empty()||line[0]=='>')continue;
   process(line,n);
  }
 }catch(const exception&e){cerr<<"FATAL: "<<e.what()<<"\n";return 1;}
 cout<<"STATS "<<n<<" "<<total<<" "<<after8<<" "<<after16
     <<" "<<final_edges<<" "<<witness<<"\n";
}
