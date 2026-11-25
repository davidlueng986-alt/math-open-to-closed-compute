#include <bits/stdc++.h>
using namespace std;
using U=uint64_t;using I=int64_t;
constexpr int N=40;constexpr U FULL=(1ULL<<N)-1;
mt19937_64 rng;
int pc(U x){return __builtin_popcountll(x);}
int sample(U x){assert(x);int k=rng()%pc(x);while(k--)x&=x-1;return __builtin_ctzll(x);}
struct G{
 array<U,N>a{};
 int deg(int i)const{return pc(a[i]);}
 bool has(int i,int j)const{return (a[i]>>j)&1;}
 void flip(int i,int j){a[i]^=1ULL<<j;a[j]^=1ULL<<i;}
 I count(U p,int k)const{if(k==0)return 1;if(pc(p)<k)return 0;if(k==1)return pc(p);I z=0;while(pc(p)>=k){int i=__builtin_ctzll(p);p&=p-1;z+=count(p&~a[i],k-1);}return z;}
 void edit(int i,int j,I& score){I d=count(FULL&~(a[i]|a[j]|(1ULL<<i)|(1ULL<<j)),8);score+=has(i,j)?d:-d;flip(i,j);}
 bool witness(U p,int k,U&out)const{if(k==0){out=0;return true;}while(pc(p)>=k){int i=sample(p);p^=1ULL<<i;U rest;if(witness(p&~a[i],k-1,rest)){out=rest|(1ULL<<i);return true;}}return false;}
 bool valid()const{for(int i=0;i<N;i++){if(deg(i)>9||has(i,i))return false;for(int j=0;j<N;j++)if(has(i,j)!=has(j,i)||(has(i,j)&&(a[i]&a[j])))return false;}return true;}
 void save(const string&p)const{ofstream f(p);for(int i=0;i<N;i++){for(int j=0;j<N;j++)f<<has(i,j);f<<'\n';}}
 void refill(I&score,int cap){vector<pair<int,int>> edges;for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)if(!has(i,j)&&!(a[i]&a[j])&&deg(i)<9&&deg(j)<9)edges.emplace_back(i,j);shuffle(edges.begin(),edges.end(),rng);for(auto [i,j]:edges)if(cap>0&&deg(i)<9&&deg(j)<9&&!has(i,j)&&!(a[i]&a[j])){edit(i,j,score);--cap;}}
};
G read_seed(const string&path){ifstream f(path);string s;getline(f,s);if(!s.empty()&&s.back()=='\r')s.pop_back();if(s.size()!=125||s[0]-63!=39)throw runtime_error("expected 39-vertex graph6");G g;int b=0;for(int j=0;j<39;j++)for(int i=0;i<j;i++,b++)if(((s[1+b/6]-63)>>(5-b%6))&1)g.flip(i,j);if(!g.valid()||g.count((1ULL<<39)-1,10)!=0)throw runtime_error("seed invalid");return g;}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 rng.seed(stoull(argv[1]));int seconds=stoi(argv[2]);string out=argv[3];G seed=read_seed(argv[4]);
 auto deadline=chrono::steady_clock::now()+chrono::seconds(seconds);
 I baseline=seed.count(FULL,10);G best=seed,g=seed;I bestS=baseline,score=baseline;uint64_t iter=0,accepted=0,restarts=0;
 auto checkpoint=[&](){if(!best.valid()||best.count(FULL,10)!=bestS)throw runtime_error("incremental score mismatch");best.save(out+"/best40.txt");ofstream f(out+"/search.json");f<<"{\"seed\":"<<argv[1]<<",\"iterations\":"<<iter<<",\"accepted\":"<<accepted<<",\"restarts\":"<<restarts<<",\"independent_10_sets\":"<<bestS<<",\"witness\":"<<(bestS==0?"true":"false")<<"}\n";};
 checkpoint();
 while(chrono::steady_clock::now()<deadline&&bestS>0){
   if(iter%1800==0){++restarts;if(restarts%4==0){g=seed;score=baseline;}else{g=best;score=bestS;}g.refill(score,40);}
   U w;if(!g.witness(FULL,10,w)){best=g;bestS=0;break;}
   int u=sample(w),v=sample(w&~(1ULL<<u));G h=g;I hs=score;
   U common=h.a[u]&h.a[v];int mode=rng()%3;
   while(common){int z=sample(common);common^=1ULL<<z;if(mode==0||(mode==2&&rng()%2))h.edit(u,z,hs);else h.edit(v,z,hs);}
   while(h.deg(u)>=9)h.edit(u,sample(h.a[u]),hs);
   while(h.deg(v)>=9)h.edit(v,sample(h.a[v]),hs);
   h.edit(u,v,hs);h.refill(hs,1+rng()%12);
   double phase=double(iter%1800)/1800;
   double scale=(0.012+0.008*(stoull(argv[1])%5))*max<I>(1,bestS);
   double temp=max(0.3,scale*(0.1+2.5*(1-phase)));
   if(hs<=score||generate_canonical<double,53>(rng)<exp(-double(hs-score)/temp)){g=h;score=hs;++accepted;}
   ++iter;
   if(hs<bestS){best=h;bestS=hs;checkpoint();cout<<"iteration "<<iter<<" I10 "<<bestS<<endl;}
   if(iter%1000==0)checkpoint();
 }
 checkpoint();cout<<"final I10 "<<bestS<<" iterations "<<iter<<endl;
}
