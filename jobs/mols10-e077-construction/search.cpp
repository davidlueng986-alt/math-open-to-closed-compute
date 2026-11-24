// E077 constructive 3-MOLS search. No negative output is a global nonexistence claim.
// C++17, standard library only. Exact inner transversal and cover routines.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Mask=__uint128_t;
using Square=array<int,100>;
struct Pair{Square a,b;};
struct Eval{int packing=0,total=0;bool packing_complete=true;uint64_t pack_nodes=0;vector<Mask> chosen;vector<int> odd_cycle;};
struct Candidate{Pair p;Eval e;};
static int N=10,N2=100,FULL=1023;
static Mask ALL=(Mask(1)<<100)-1;
static mt19937_64 rng;
static uint64_t total_transversal_nodes=0,total_mate_nodes=0,total_pack_nodes=0,evaluated_pairs=0,valid_mutants=0,iterations=0;
static uint64_t mate_limit=200000,pack_limit=200000;static int mate_cap=16;
static vector<Candidate> elite;static unordered_set<string> seen;static string outdir;static int seed;
static chrono::steady_clock::time_point started;
int pop(Mask m){return __builtin_popcountll((uint64_t)m)+__builtin_popcountll((uint64_t)(m>>64));}
int first(Mask m){uint64_t a=(uint64_t)m;return a?__builtin_ctzll(a):64+__builtin_ctzll((uint64_t)(m>>64));}
double elapsed(){return chrono::duration<double>(chrono::steady_clock::now()-started).count();}
int pick(int n){return int(rng()%n);}
bool latin(const Square&s){for(int r=0;r<N;r++){int m=0;for(int c=0;c<N;c++){int a=s[N*r+c];if(a<0||a>=N)return false;m|=1<<a;}if(m!=FULL)return false;}for(int c=0;c<N;c++){int m=0;for(int r=0;r<N;r++)m|=1<<s[N*r+c];if(m!=FULL)return false;}return true;}
bool orth(const Square&a,const Square&b){array<bool,100>u{};for(int i=0;i<N2;i++){int v=N*a[i]+b[i];if(u[v])return false;u[v]=true;}return true;}
void verify(const Pair&p){if(!latin(p.a)||!latin(p.b)||!orth(p.a,p.b))throw runtime_error("Invalid orthogonal pair");}
string key(const Pair&p){string s;s.reserve(200);for(int i=0;i<N2;i++)s.push_back(char('0'+p.a[i]));for(int i=0;i<N2;i++)s.push_back(char('0'+p.b[i]));return s;}
void normalize(Pair&p){array<int,10>ma{},mb{},rr{};for(int c=0;c<N;c++){ma[p.a[c]]=c;mb[p.b[c]]=c;}for(int i=0;i<N2;i++){p.a[i]=ma[p.a[i]];p.b[i]=mb[p.b[i]];}for(int r=0;r<N;r++)rr[p.a[N*r]]=r;Pair q=p;for(int r=0;r<N;r++)for(int c=0;c<N;c++){p.a[N*r+c]=q.a[N*rr[r]+c];p.b[N*r+c]=q.b[N*rr[r]+c];}}
Pair conjugate(const Pair&p){array<int,4>d{0,1,2,3};shuffle(d.begin(),d.end(),rng);Pair q;for(int r=0;r<N;r++)for(int c=0;c<N;c++){array<int,4>v{r,c,p.a[N*r+c],p.b[N*r+c]};int i=N*v[d[0]]+v[d[1]];q.a[i]=v[d[2]];q.b[i]=v[d[3]];}normalize(q);return q;}
vector<Mask> transversals(const Square&a,const Square*b=nullptr){
 vector<Mask>res;
 function<void(int,int,int,int,Mask)>dfs=[&](int rows,int cols,int s,int t,Mask cells){
  total_transversal_nodes++;
  if(rows==FULL){res.push_back(cells);return;}
  int row=-1,choices=0,best=11;
  for(int r=0;r<N;r++)if(!(rows>>r&1)){
   int v=0;for(int c=0;c<N;c++){int i=N*r+c;if(!(cols>>c&1)&&!(s>>a[i]&1)&&(!b||!(t>>(*b)[i]&1)))v|=1<<c;}
   int z=__builtin_popcount((unsigned)v);if(z<best){best=z;row=r;choices=v;if(z<=1)break;}
  }
  if(!choices)return;
  while(choices){int c=__builtin_ctz((unsigned)choices);choices&=choices-1;int i=N*row+c;dfs(rows|1<<row,cols|1<<c,s|1<<a[i],b?t|1<<(*b)[i]:0,cells|(Mask(1)<<i));}
 };
 dfs(0,0,0,0,0);return res;
}
// Exact residual-two lemma: after N-2 disjoint common transversals, the
// remaining cells have each of the four coordinate values twice. They split
// into two common transversals iff the graph joining equal coordinates is bipartite.
// If not bipartite, N-1 transversals are impossible too: the complement of
// N-1 disjoint common transversals would automatically be the Nth transversal.
struct TwoResult{bool complete=false;array<Mask,2>parts{};vector<int>odd_cycle;};
TwoResult residual_two(const Pair&p,Mask used){
 TwoResult result;array<int,100>color,parent,depth;color.fill(-1);parent.fill(-1);depth.fill(0);
 vector<int>v;for(int i=0;i<N2;i++)if(!(used>>i&1))v.push_back(i);
 if(v.size()!=size_t(2*N))throw runtime_error("Residual-two size");
 auto adjacent=[&](int a,int b){return a/N==b/N||a%N==b%N||p.a[a]==p.a[b]||p.b[a]==p.b[b];};
 for(int root:v)if(color[root]<0){vector<int>q{root};color[root]=0;
  for(size_t k=0;k<q.size();k++){int a=q[k];for(int b:v)if(a!=b&&adjacent(a,b)){
   if(color[b]<0){color[b]=1-color[a];parent[b]=a;depth[b]=depth[a]+1;q.push_back(b);}
   else if(color[b]==color[a]){int x=a,y=b;vector<int>left{x},right{y};while(depth[x]>depth[y]){x=parent[x];left.push_back(x);}while(depth[y]>depth[x]){y=parent[y];right.push_back(y);}while(x!=y){x=parent[x];y=parent[y];left.push_back(x);right.push_back(y);}right.pop_back();reverse(right.begin(),right.end());left.insert(left.end(),right.begin(),right.end());result.odd_cycle=left;return result;}
  }}
 }
 for(int i:v)result.parts[color[i]]|=Mask(1)<<i;
 if(pop(result.parts[0])!=N||pop(result.parts[1])!=N)throw runtime_error("Residual bipartition balance");
 result.complete=true;return result;
}
Eval evaluate(const Pair&p){
 verify(p);evaluated_pairs++;auto tt=transversals(p.a,&p.b);Eval e;e.total=tt.size();
 array<vector<int>,10>groups;for(int j=0;j<(int)tt.size();j++){int c=first(tt[j]&FULL);groups[c].push_back(j);}
 array<int,10>order; iota(order.begin(),order.end(),0);sort(order.begin(),order.begin()+N,[&](int a,int b){return groups[a].size()<groups[b].size();});
 vector<Mask>chosen;
 function<void(int,Mask)>dfs=[&](int d,Mask used){
  if(e.pack_nodes++>=pack_limit){e.packing_complete=false;return;}
  if((int)chosen.size()>e.packing){e.packing=chosen.size();e.chosen=chosen;e.odd_cycle.clear();}
  if(e.packing==N)return;
  if((int)chosen.size()==N-2){auto two=residual_two(p,used);if(two.complete){e.packing=N;e.chosen=chosen;e.chosen.push_back(two.parts[0]);e.chosen.push_back(two.parts[1]);e.odd_cycle.clear();}else if(e.chosen==chosen)e.odd_cycle=two.odd_cycle;return;}
  if(d==N||(int)chosen.size()+N-d<=e.packing)return;
  for(int j:groups[order[d]])if(!(tt[j]&used)){chosen.push_back(tt[j]);dfs(d+1,used|tt[j]);chosen.pop_back();if(!e.packing_complete||e.packing==N)return;}
  dfs(d+1,used);
 };
 dfs(0,0);total_pack_nodes+=e.pack_nodes;return e;
}
vector<Square> mates(const Square&a,const Square&hint,const vector<Mask>&preserved={}){
 auto tt=transversals(a);
 tt.erase(remove_if(tt.begin(),tt.end(),[&](Mask t){for(Mask p:preserved)if(pop(t&p)>1)return true;return false;}),tt.end());vector<Square>result;array<vector<int>,100>at;array<Mask,10>old{};
 for(int i=0;i<N2;i++)old[hint[i]]|=Mask(1)<<i;
 vector<pair<int,uint64_t>>priority(tt.size());
 for(int j=0;j<(int)tt.size();j++){int score=0;for(Mask x:old)score=max(score,pop(x&tt[j]));priority[j]={score,rng()};Mask m=tt[j];while(m){int i=first(m);m&=m-1;at[i].push_back(j);}}
 for(auto&v:at)sort(v.begin(),v.end(),[&](int a,int b){return priority[a]>priority[b];});
 uint64_t nodes=0;vector<int>chosen;
 function<void(Mask)>dfs=[&](Mask rem){
  if(nodes++>=mate_limit||result.size()>=size_t(mate_cap))return;
  if(!rem){Square b{};for(int j:chosen){int val=first(tt[j]&FULL);Mask m=tt[j];while(m){int i=first(m);m&=m-1;b[i]=val;}}if(!latin(b)||!orth(a,b))throw runtime_error("Mate verifier");result.push_back(b);return;}
  int best=-1,n=1000000;Mask m=rem;
  while(m){int i=first(m);m&=m-1;int z=0;for(int j:at[i])if((tt[j]&rem)==tt[j])z++;if(z<n){n=z;best=i;if(z<=1)break;}}
  if(!n)return;
  for(int j:at[best])if((tt[j]&rem)==tt[j]){chosen.push_back(j);dfs(rem^tt[j]);chosen.pop_back();if(nodes>=mate_limit||result.size()>=size_t(mate_cap))return;}
 };
 dfs(ALL);total_mate_nodes+=nodes;return result;
}
// Switch one connected component between two levels of one OA coordinate.
// Each of the other coordinates gives a perfect matching between the20 points.
bool kempe(Pair&p){
 array<array<int,4>,100>v;for(int i=0;i<N2;i++)v[i]={i/N,i%N,p.a[i],p.b[i]};
 vector<pair<int,vector<int>>>moves;
 for(int d=0;d<4;d++)for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){
  vector<int>pts;for(int i=0;i<N2;i++)if(v[i][d]==a||v[i][d]==b)pts.push_back(i);
  array<bool,100>done{};vector<vector<int>>comps;
  for(int i:pts)if(!done[i]){vector<int>q{i};done[i]=true;for(size_t k=0;k<q.size();k++)for(int j:pts)if(!done[j]){bool touch=false;for(int e=0;e<4;e++)if(e!=d&&v[q[k]][e]==v[j][e])touch=true;if(touch){q.push_back(j);done[j]=true;}}comps.push_back(q);}
  if(comps.size()>1)for(size_t z=0;z+1<comps.size();z++)moves.push_back({d,comps[z]});
 }
 if(moves.empty())return false;
 auto mv=moves[pick(moves.size())];int d=mv.first,a=v[mv.second[0]][d],b=-1;for(int i:mv.second)if(v[i][d]!=a)b=v[i][d];if(b<0)throw runtime_error("Kempe component");
 for(int i:mv.second)v[i][d]=a+b-v[i][d];
 for(int z=0;z<N2;z++){auto t=v[z];int i=N*t[0]+t[1];p.a[i]=t[2];p.b[i]=t[3];}normalize(p);verify(p);return true;
}
// A two-symbol cycle trade in one Latin square, preserving its Latin property.
bool latin_trade(Square&s){
 vector<vector<int>>moves;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){
  vector<int>pts;for(int i=0;i<N2;i++)if(s[i]==a||s[i]==b)pts.push_back(i);
  array<bool,100>done{};vector<vector<int>>comps;
  for(int i:pts)if(!done[i]){vector<int>q{i};done[i]=true;for(size_t k=0;k<q.size();k++)for(int j:pts)if(!done[j]&&(q[k]/N==j/N||q[k]%N==j%N)){done[j]=true;q.push_back(j);}comps.push_back(q);}
  if(comps.size()>1)for(size_t z=0;z+1<comps.size();z++)moves.push_back(comps[z]);
 }
 if(moves.empty())return false;
 auto c=moves[pick(moves.size())];int a=s[c[0]],b=-1;for(int i:c)if(s[i]!=a)b=s[i];for(int i:c)s[i]=a+b-s[i];if(!latin(s))throw runtime_error("Latin trade verifier");return true;
}
double quality(const Eval&e){return 100.0*e.packing+min(90.0,10.0*log1p(e.total));}
bool better(const Candidate&a,const Candidate&b){if(a.e.packing!=b.e.packing)return a.e.packing>b.e.packing;return a.e.total>b.e.total;}
void array_json(ostream&o,const Square&s){o<<'[';for(int i=0;i<N2;i++){if(i)o<<',';o<<s[i];}o<<']';}
void candidate_json(ostream&o,const Candidate&c){o<<"{\"packing\":"<<c.e.packing<<",\"common_transversals\":"<<c.e.total<<",\"packing_search_complete\":"<<(c.e.packing_complete?"true":"false")<<",\"A\":";array_json(o,c.p.a);o<<",\"B\":";array_json(o,c.p.b);o<<",\"disjoint_transversals\":[";for(size_t j=0;j<c.e.chosen.size();j++){if(j)o<<',';o<<'[';Mask m=c.e.chosen[j];bool sep=false;while(m){int i=first(m);m&=m-1;if(sep)o<<',';sep=true;o<<i;}o<<']';}if(c.e.packing==N){Square third;for(int j=0;j<N;j++){Mask m=c.e.chosen[j];while(m){int i=first(m);m&=m-1;third[i]=j;}}if(!latin(third)||!orth(c.p.a,third)||!orth(c.p.b,third))throw runtime_error("3MOLS final verifier");o<<"],\"C\":";array_json(o,third);o<<'}';}else{o<<"]";if(!c.e.odd_cycle.empty()){o<<",\"two_remaining_odd_cycle\":[";for(size_t i=0;i<c.e.odd_cycle.size();i++){if(i)o<<',';o<<c.e.odd_cycle[i];}o<<']';}o<<'}';}}
void checkpoint(const string& status="SEARCHING"){
 if(elite.empty())return;
 const string actual_status=elite[0].e.packing==N?"YES_WITNESS":status;
 const string display=actual_status=="YES_WITNESS"?"已驗證構造":actual_status=="SEARCHING"?"搜尋進行中":"未完成任務";
 string tmp=outdir+"/checkpoint.json.tmp";ofstream o(tmp);o<<"{\"order\":10,\"problem\":\"MOLS10-3\",\"global_nonexistence_claim\":false,\"status_display\":\""<<display<<"\",\"resume_semantics\":\"saved population and RNG restart; other counters reset; annealing state and dedup cache not restored\",\"scope\":\"constructive Latin trades plus exact transversal and mate search; not global enumeration\",\"status\":\""<<actual_status<<"\",\"seed\":"<<seed<<",\"elapsed_seconds\":"<<elapsed()<<",\"iterations\":"<<iterations<<",\"evaluated_pairs\":"<<evaluated_pairs<<",\"valid_mutants\":"<<valid_mutants<<",\"transversal_nodes\":"<<total_transversal_nodes<<",\"mate_nodes\":"<<total_mate_nodes<<",\"pack_nodes\":"<<total_pack_nodes<<",\"best\":";candidate_json(o,elite[0]);o<<",\"elite\":[";for(size_t j=0;j<min(size_t(32),elite.size());j++){if(j)o<<',';candidate_json(o,elite[j]);}o<<"]}\n";o.close();filesystem::rename(tmp,outdir+"/checkpoint.json");
 ofstream s(outdir+"/resume.txt.tmp");s<<iterations<<'\n'<<rng<<'\n'<<min(size_t(32),elite.size())<<'\n';for(size_t j=0;j<min(size_t(32),elite.size());j++){for(int x:elite[j].p.a)s<<x;s<<'\n';for(int x:elite[j].p.b)s<<x;s<<'\n';}s.close();filesystem::rename(outdir+"/resume.txt.tmp",outdir+"/resume.txt");
}
bool consider(Pair p,Eval* result=nullptr){normalize(p);string k=key(p);if(seen.find(k)!=seen.end())return false;seen.insert(k);if(seen.size()>2000000)seen.clear();Candidate c{p,evaluate(p)};if(result)*result=c.e;bool improved=elite.empty()||better(c,elite[0]);elite.push_back(c);sort(elite.begin(),elite.end(),better);if(elite.size()>128)elite.resize(128);if(improved){cout<<"{\"event\":\"best\",\"elapsed\":"<<elapsed()<<",\"packing\":"<<c.e.packing<<",\"transversals\":"<<c.e.total<<",\"evaluated\":"<<evaluated_pairs<<"}"<<endl;checkpoint();}return true;}
vector<Pair> read_pairs(istream&f){int n=0;if(!(f>>n)||n<1||n>1000000)throw runtime_error("Invalid seed count");vector<Pair>p;for(int i=0;i<n;i++){string a,b;f>>a>>b;if(a.size()!=size_t(N2)||b.size()!=size_t(N2))throw runtime_error("Seed input");Pair q;for(int j=0;j<N2;j++){q.a[j]=a[j]-'0';q.b[j]=b[j]-'0';}verify(q);p.push_back(q);}return p;}
int main(int argc,char**argv){try{
 double seconds=3600;string input="seeds.txt",resume="",selftest="",audit="";outdir="out";seed=1;
 for(int i=1;i<argc;i++){string s=argv[i];if(i+1==argc)throw runtime_error("Missing argument");string v=argv[++i];if(s=="--seconds")seconds=stod(v);else if(s=="--seed")seed=stoi(v);else if(s=="--input")input=v;else if(s=="--out")outdir=v;else if(s=="--resume")resume=v;else if(s=="--self-test")selftest=v;else if(s=="--audit")audit=v;else if(s=="--mate-nodes")mate_limit=stoull(v);else if(s=="--pack-nodes")pack_limit=stoull(v);else if(s=="--mates")mate_cap=stoi(v);else throw runtime_error("Unknown argument "+s);}
 if(seconds<=0||mate_limit<1||pack_limit<1||mate_cap<1)throw runtime_error("Invalid limits");
 filesystem::create_directories(outdir);started=chrono::steady_clock::now();rng.seed(seed);vector<Pair>seeds;
 if(!selftest.empty()){
  N=5;N2=25;FULL=31;ALL=(Mask(1)<<25)-1;Pair p{};
  for(int r=0;r<N;r++)for(int c=0;c<N;c++){p.a[N*r+c]=(r+c)%N;p.b[N*r+c]=(r+2*c)%N;}
  Candidate c{p,evaluate(p)};if(c.e.packing!=N)throw runtime_error("Positive control failed");
  auto mm=mates(p.a,p.b);if(mm.empty())throw runtime_error("Mate positive control failed");
  ofstream f(selftest);f<<"{\"order\":5,\"status\":\"YES_WITNESS\",\"best\":";candidate_json(f,c);f<<"}\n";
  cout<<"{\"positive_control\":\"PASS\",\"packing\":"<<c.e.packing<<",\"common_transversals\":"<<c.e.total<<"}"<<endl;return 0;
 }

 if(!resume.empty()){ifstream f(resume);if(!f)throw runtime_error("Resume file missing");f>>iterations>>rng;seeds=read_pairs(f);}else{ifstream f(input);if(!f)throw runtime_error("Seed file missing");seeds=read_pairs(f);}
 if(!audit.empty()){
  if(seeds.empty())throw runtime_error("Audit needs a seed");
  Candidate c{seeds[0],evaluate(seeds[0])};
  ofstream f(audit);f<<"{\"order\":10,\"scope\":\"fixed supplied orthogonal pair only\",\"status\":\""<<(c.e.packing==N?"YES_WITNESS":c.e.packing_complete?"RESTRICTED_UNSAT":"UNKNOWN")<<"\",\"best\":";candidate_json(f,c);f<<"}\n";
  cout<<"{\"fixed_pair_audit\":true,\"packing\":"<<c.e.packing<<",\"common_transversals\":"<<c.e.total<<",\"complete\":"<<(c.e.packing_complete?"true":"false")<<"}"<<endl;return 0;
 }
 for(auto p:seeds){if(elapsed()>seconds)break;consider(p);if(elite[0].e.packing==N)break;}
 if(elite.empty())throw runtime_error("No validated seeds");
 Pair current=elite[0].p;Eval current_e=elite[0].e;double next=elapsed()+30;
 while(elapsed()<seconds&&elite[0].e.packing<N){iterations++;Pair base;
  int mode=pick(10);if(mode<3)base=elite[0].p;else if(mode<6)base=elite[pick(min(32,(int)elite.size()))].p;else if(mode<8)base=current;else base=seeds[pick(seeds.size())];
  if(pick(4)==0)base=conjugate(base);
  vector<Pair>proposals;
  if(pick(3)==0){Pair q=base;if(kempe(q))proposals.push_back(q);}
  if(proposals.empty()){
   if(pick(2))swap(base.a,base.b);
   auto oldeval=evaluate(base);
   int count=1+(pick(10)==0?pick(3):0);bool changed=true;for(int t=0;t<count;t++)changed=latin_trade(base.a)&&changed;
   if(changed){vector<Mask> retained;
    if(pick(5)!=0)for(Mask t:oldeval.chosen){int symbols=0;Mask m=t;while(m){int i=first(m);m&=m-1;symbols|=1<<base.a[i];}if(symbols==FULL)retained.push_back(t);}
    if(!retained.empty()&&pick(3)==0)retained.erase(retained.begin()+pick(retained.size()));
    auto ms=mates(base.a,base.b,retained);for(auto b:ms)proposals.push_back(Pair{base.a,b});}
  }
  for(auto q:proposals){normalize(q);Eval e;if(!consider(q,&e))continue;valid_mutants++;double delta=quality(e)-quality(current_e);double temp=35.0+40.0*(1.0-fmod(elapsed(),300.0)/300.0);double u=generate_canonical<double,53>(rng);if(delta>=0||u<exp(delta/temp)){current=q;current_e=e;}if(elite[0].e.packing==N)break;}
  if(elapsed()>=next){checkpoint();cout<<"{\"event\":\"progress\",\"elapsed\":"<<elapsed()<<",\"iterations\":"<<iterations<<",\"evaluated_pairs\":"<<evaluated_pairs<<",\"best_packing\":"<<elite[0].e.packing<<",\"best_transversals\":"<<elite[0].e.total<<",\"transversal_nodes\":"<<total_transversal_nodes<<",\"mate_nodes\":"<<total_mate_nodes<<"}"<<endl;next=elapsed()+30;}
 }
 checkpoint("UNFINISHED_TASK");cout<<"{\"event\":\"finished\",\"elapsed\":"<<elapsed()<<",\"iterations\":"<<iterations<<",\"evaluated_pairs\":"<<evaluated_pairs<<",\"best_packing\":"<<elite[0].e.packing<<",\"global_nonexistence_claim\":false}"<<endl;return 0;
 }catch(const exception&e){cerr<<e.what()<<endl;return 1;}}
