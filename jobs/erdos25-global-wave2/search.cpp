#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

// A finite search, never a proof of the unrestricted Erdős problem.
// Every candidate has distinct q | L, one residue per selected q,
// and the original activation n >= q. Full first-kill counts are integers.
using Clock = std::chrono::steady_clock;

long long inverse(long long a, long long m) {
  if (m == 1) return 0;
  long long b=m, u=1, v=0;
  while(b) { long long t=a/b; a-=t*b; std::swap(a,b); u-=t*v; std::swap(u,v); }
  if(a!=1) throw std::runtime_error("CRT inverse does not exist");
  return (u%m+m)%m;
}

struct Model {
  int L, X, k, empty;
  std::vector<int> q,a,owner,hits;
  std::vector<long long> count;
  std::vector<long double> h,logq;
  std::vector<std::vector<int>> gcds,invs,lcms;
  long double HX=0, HB=0, energyMass=0;
  std::vector<std::pair<int,int>> undo;

  Model(int period,int cutoff):L(period),X(cutoff) {
    if(!(1<=X && X<=L)) throw std::runtime_error("require 1 <= X <= L");
    for(int d=2; d<=X; ++d) if(L%d==0) q.push_back(d);
    k=q.size(); empty=k;
    if(k==0) throw std::runtime_error("no moduli");
    a.assign(k,-1); owner.assign(L,empty); count.assign(k+1,0); count[empty]=L;
    h.assign(k+1,0); hits.assign(k+1,0); logq.assign(k+1,0);
    for(int i=0;i<k;++i) logq[i]=std::log((long double)q[i]);
    for(int n=1;n<=X;++n) HX+=1.0L/n;
    gcds.assign(k,std::vector<int>(k)); invs=gcds; lcms=gcds;
    for(int i=0;i<k;++i) for(int j=i+1;j<k;++j) {
      int g=std::gcd(q[i],q[j]); gcds[i][j]=g;
      lcms[i][j]=(q[i]/g)*q[j];
      invs[i][j]=inverse(q[i]/g,q[j]/g);
    }
  }

  void assign(int r,int to,bool record=true) {
    int from=owner[r]; if(from==to) return;
    if(record) undo.emplace_back(r,from);
    --count[from]; ++count[to];
    energyMass+=logq[to]-logq[from];
    int n=r==0?L:r;
    if(n<=X) {
      long double w=1.0L/n;
      if(from<k && q[from]<=n) {h[from]-=w;HB-=w;--hits[from];}
      if(to<k && q[to]<=n) {h[to]+=w;HB+=w;++hits[to];}
    }
    owner[r]=to;
  }

  void change(int i,int residue) {
    undo.clear(); int old=a[i];
    if(old>=0) {
      for(int r=old;r<L;r+=q[i]) if(owner[r]==i) assign(r,empty);
      // Restore the least later matching modulus on the removed cylinder.
      for(int j=i+1;j<k;++j) if(a[j]>=0) {
        int g=gcds[i][j], diff=a[j]-old;
        if(diff%g) continue;
        long long m=q[j]/g;
        long long t=((long long)(diff/g)*invs[i][j])%m; if(t<0)t+=m;
        int first=old+q[i]*t;
        for(int r=first;r<L;r+=lcms[i][j]) if(owner[r]==empty) assign(r,j);
      }
    }
    a[i]=residue;
    if(residue>=0) for(int r=residue;r<L;r+=q[i]) if(owner[r]>i) assign(r,i);
  }

  void rollback(int i,int previous) {
    for(auto it=undo.rbegin();it!=undo.rend();++it) assign(it->first,it->second,false);
    a[i]=previous; undo.clear();
  }

  void rebuild(bool check) {
    std::vector<int> fresh(L,empty);
    for(int i=0;i<k;++i) if(a[i]>=0)
      for(int r=a[i];r<L;r+=q[i]) if(fresh[r]==empty) fresh[r]=i;
    if(check && fresh!=owner) throw std::runtime_error("incremental owner mismatch");
    owner.swap(fresh); std::fill(count.begin(),count.end(),0);
    std::fill(h.begin(),h.end(),0); std::fill(hits.begin(),hits.end(),0); HB=0; energyMass=0;
    for(int r=0;r<L;++r) {
      int i=owner[r]; ++count[i];
      int n=r==0?L:r;
      if(i<k && n<=X && q[i]<=n) {h[i]+=1.0L/n;++hits[i];}
    }
    for(int i=0;i<k;++i) {HB+=h[i];energyMass+=count[i]*logq[i];}
    undo.clear();
  }

  long double beta() const {return 1.0L-(long double)count[empty]/L;}
  long double discrepancy() const {return HB-beta()*HX;}
  long double energy() const {return energyMass/L;}
  long double ratio() const {
    long double d=std::max(0.0L,discrepancy()); return d*d/(HX*(1+energy()));
  }
  long double entropy() const {
    long double out=0;
    for(int i=0;i<k;++i) if(hits[i]>0) {
      if(count[i]<=0) throw std::runtime_error("positive hit in zero Haar cell");
      long double c=h[i]/HX, e=(long double)count[i]/L;
      if(c>e) out+=c*std::log(c/e);
    }
    return out;
  }
  long double objective(const std::string &s) const {
    if(s=="entropy") return entropy();
    // A signed extension gives the annealer a gradient before positive excess.
    if(s=="energy") {long double d=discrepancy();return d*std::abs(d)/(HX*(1+energy()));}
    throw std::runtime_error("unknown objective");
  }
};

void emit(const std::string& path,Model& m,const std::string& objective,
          uint64_t seed,long long steps,int restarts,double seconds) {
  m.rebuild(true);
  std::ofstream f(path); if(!f)throw std::runtime_error("cannot create output");
  f<<std::setprecision(21)<<"{\n  \"schema\": 1,\n  \"status\": \"FINITE_SEARCH_ONLY\",\n";
  f<<"  \"period\": "<<m.L<<", \"cutoff\": "<<m.X<<",\n";
  f<<"  \"objective\": \""<<objective<<"\", \"seed\": "<<seed<<",\n";
  f<<"  \"iterations\": "<<steps<<", \"restarts\": "<<restarts<<", \"seconds\": "<<seconds<<",\n";
  f<<"  \"harmonic_total\": "<<m.HX<<", \"harmonic_deleted\": "<<m.HB<<",\n";
  f<<"  \"haar_union_numerator\": "<<m.L-m.count[m.empty]<<",\n";
  f<<"  \"beta\": "<<m.beta()<<", \"first_kill_energy\": "<<m.energy()<<",\n";
  f<<"  \"discrepancy\": "<<m.discrepancy()<<", \"energy_ratio\": "<<m.ratio()<<",\n";
  f<<"  \"normalized_disjoint_entropy\": "<<m.entropy()<<",\n  \"rules\": [\n";
  bool first=true;
  for(int i=0;i<m.k;++i) if(m.a[i]>=0) {
    if(!first) f<<",\n";
    first=false;
    f<<"    {\"q\": "<<m.q[i]<<", \"a\": "<<m.a[i]
     <<", \"first_kill_count\": "<<m.count[i]<<", \"harmonic_first_kill\": "<<m.h[i]<<"}";
  }
  f<<"\n  ]\n}\n";
}

int main(int argc,char**argv) {
  try {
    if(argc!=8 && argc!=9) throw std::runtime_error("usage: search L X seed seconds entropy|energy output.json maximum_iterations [seed.tsv]");
    int L=std::stoi(argv[1]), X=std::stoi(argv[2]);
    uint64_t seed=std::stoull(argv[3]); double budget=std::stod(argv[4]);
    std::string objective=argv[5],path=argv[6]; long long maxSteps=std::stoll(argv[7]);
    Model m(L,X); std::mt19937_64 rng(seed);
    if(argc==9) {
      std::ifstream in(argv[8]); if(!in)throw std::runtime_error("cannot read seed");
      int modulus,residue;
      while(in>>modulus>>residue) {
        auto it=std::lower_bound(m.q.begin(),m.q.end(),modulus);
        if(it==m.q.end() || *it!=modulus || residue<0 || residue>=modulus)
          throw std::runtime_error("invalid seed rule");
        auto i=it-m.q.begin(); if(m.a[i]>=0)throw std::runtime_error("duplicate seed modulus");
        m.a[i]=residue;
      }
      m.rebuild(false);
    }
    auto uniform=[&](){return std::generate_canonical<double,53>(rng);};
    auto start=Clock::now(); auto elapsed=[&](){return std::chrono::duration<double>(Clock::now()-start).count();};
    long double best=m.objective(objective),current=best;
    std::vector<int> bestA=m.a;
    long long steps=0; int restarts=0; const int epoch=3000;
    while(steps<maxSteps && elapsed()<budget) {
      if(steps%epoch==0) {
        ++restarts;
        if(restarts%4==1) m.a=bestA;
        else for(int i=0;i<m.k;++i) {
          double include=(restarts%4==2)?0.25:((restarts%4==3)?0.7:0.05);
          m.a[i]=uniform()<include ? ((restarts%4==2)?0:rng()%m.q[i]) : -1;
        }
        m.rebuild(false); current=m.objective(objective);
        if(current>best) {best=current;bestA=m.a;}
      }
      int i=rng()%m.k,previous=m.a[i],residue;
      double draw=uniform();
      if(draw<0.2) residue=-1;
      else if(draw<0.32) residue=0;
      else if(draw<0.48 && previous>=0) residue=(previous+1+rng()%std::min(m.q[i],9))%m.q[i];
      else residue=rng()%m.q[i];
      if(residue==previous) {++steps;continue;}
      m.change(i,residue); long double candidate=m.objective(objective);
      double phase=(steps%epoch)/(double)epoch;
      long double temperature=0.03L*std::pow(1e-5L,phase);
      if(candidate>=current || std::log(std::max(uniform(),1e-300))<(candidate-current)/temperature) {
        current=candidate;
        if(candidate>best+1e-15L) {best=candidate;bestA=m.a;}
        m.undo.clear();
      } else m.rollback(i,previous);
      ++steps;
      if(steps%500==0) {m.rebuild(true);current=m.objective(objective);}
    }
    m.a=bestA;m.rebuild(false);emit(path,m,objective,seed,steps,restarts,elapsed());
    std::cout<<std::setprecision(12)<<"L="<<L<<" X="<<X<<" steps="<<steps
             <<" K="<<m.entropy()<<" D="<<m.discrepancy()<<" R="<<m.ratio()<<"\n";
  } catch(const std::exception&e) {std::cerr<<e.what()<<"\n";return 1;}
}
