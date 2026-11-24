#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using Word = uint64_t;
using Wide = unsigned __int128;

constexpr Word scale = Word(1) << 62;
constexpr Word initial_tail = (scale + 2381) / 2382 + 1;
constexpr Word long_q_min = 20'000'000;
constexpr Word long_tail = (scale + long_q_min - 1) / long_q_min + 1;
constexpr Word xlo = (Wide(scale) * 948) / 1000 - 1;
constexpr Word xhi = (Wide(scale) * 1055 + 999) / 1000;

struct Prime { unsigned p; Word lo, hi; };
std::vector<Prime> primes;
std::vector<Word> sums{0};
std::vector<mpz_class> prefix_product{1}, derivatives{0};
std::array<unsigned,59> caps{};
std::array<mpz_class,23> maxprod{}, minprod{};
std::array<Word,23> long_width{};
int compulsory, long_forced, long_end;
mpz_class all_small, optional_product;
std::vector<Word> mandatory_moduli;

void load_word(mpz_class& z, Wide w) {
    if (w<=std::numeric_limits<Word>::max()) {
        mpz_set_ui(z.get_mpz_t(),Word(w));
        return;
    }
    const std::array<Word,2> words{Word(w), Word(w >> 64)};
    mpz_import(z.get_mpz_t(),2,-1,sizeof(Word),0,0,words.data());
}

struct Support {
    Word mass;
    std::array<Word,4> mask{};
    mpz_class product, derivative;
};

struct CoreEnumerator {
    std::vector<Support> out;
    int top = 0;
    std::array<Word,4> mask{};
    std::array<mpz_class,60> product, derivative;

    CoreEnumerator() {
        for (int i=0;i<long_forced;++i) mask[i/64] |= Word(1)<<(i%64);
        product[long_forced] = prefix_product[long_forced];
        derivative[long_forced] = derivatives[long_forced];
    }

    void visit(int start, int depth, Word mass) {
        const int left=58-depth;
        if (start+left>top || mass+sums[start+left]-sums[start]+primes[top].hi<2*scale-long_tail) return;
        if (!left) {
            Support s;
            s.mask=mask;
            s.mask[top/64]|=Word(1)<<(top%64);
            const unsigned p=primes[top].p;
            s.product=product[depth]*p;
            s.derivative=derivative[depth]*p+product[depth];
            const mpz_class scaled=s.derivative*scale/s.product;
            s.mass=scaled.get_ui();
            out.push_back(std::move(s));
            return;
        }
        for (int j=start;j+left<=top;++j) {
            if (mass+sums[j+left]-sums[j]+primes[top].hi<2*scale-long_tail) break;
            const unsigned p=primes[j].p;
            mask[j/64]|=Word(1)<<(j%64);
            product[depth+1]=product[depth]*p;
            derivative[depth+1]=derivative[depth]*p+product[depth];
            visit(j+1,depth+1,mass+primes[j].hi);
            mask[j/64]^=Word(1)<<(j%64);
        }
    }
};

struct Targets {
    std::vector<Support> v;
    std::vector<std::vector<unsigned>> containing;
    std::vector<unsigned> all, bucket;
    Word base = 0;
    static constexpr unsigned shift = 32;
    explicit Targets(std::vector<Support> input) : v(std::move(input)), containing(primes.size()) {
        std::sort(v.begin(),v.end(),[](const Support& a, const Support& b){return a.mass<b.mass;});
        if (!v.empty()) {
            base=v.front().mass>>shift;
            bucket.resize((v.back().mass>>shift)-base+2);
            unsigned pos=0;
            for(unsigned i=0;i<bucket.size();++i) {
                while(pos<v.size() && (v[pos].mass>>shift)<base+i) ++pos;
                bucket[i]=pos;
            }
        }
        for (unsigned i=0;i<v.size();++i) {
            all.push_back(i);
            for (int j=long_forced;j<long_end;++j)
                if ((v[i].mask[j/64]>>(j%64))&1) containing[j].push_back(i);
        }
    }
    bool possibly(Word lo,Word hi) const {
        if (v.empty()||hi<v.front().mass||lo>v.back().mass) return false;
        const auto l=std::max(lo>>shift,base)-base;
        const auto r=std::min((hi>>shift)+1-base,bucket.size()-1);
        return bucket[l]!=bucket[r];
    }
};

struct Counts {
    Word leaves=0, mass=0, valid_anchor=0, short_cases=0, parity=0, small_factor_hits=0;
    Word windows=0, supports=0, candidates=0;
    Counts& operator+=(const Counts& b) {
        leaves+=b.leaves; mass+=b.mass; valid_anchor+=b.valid_anchor; short_cases+=b.short_cases;
        parity+=b.parity; small_factor_hits+=b.small_factor_hits; windows+=b.windows;
        supports+=b.supports; candidates+=b.candidates; return *this;
    }
};

struct Finder {
    const Targets& targets;
    const bool count_only;
    std::array<int,10> a{};
    Counts counts;
    mpz_class D,F,n,C,Cf,L,Lf,K,J,inv,R,V,q,e,g,M,U0,V0,den,num,p;
    std::atomic<bool>& stop;

    Finder(const Targets& t, bool c, std::atomic<bool>& s) : targets(t), count_only(c), stop(s) {}

    void verify(const mpz_class& e0,const mpz_class& q0) {
        if (q0<=2381) return;
        const mpz_class eb=e0*q0;
        const mpz_class numerator=eb-D;
        if (numerator<=0||!mpz_divisible_p(numerator.get_mpz_t(),F.get_mpz_t())) return;
        p=numerator/F;
        if (p<=2381||p==q0||mpz_divisible_p(e0.get_mpz_t(),p.get_mpz_t())) return;
        mpz_class rem=e0, derivative=0;
        std::vector<unsigned> b;
        for (const auto& entry:primes) {
            const unsigned r=entry.p;
            if (!mpz_divisible_ui_p(rem.get_mpz_t(),r)) continue;
            if (mpz_divisible_ui_p(D.get_mpz_t(),r)) return;
            rem/=r;
            b.push_back(r);
            derivative+=e0/r;
        }
        if (rem!=1||b.size()!=49||D*p!=e0+q0*derivative) return;
        ++counts.candidates;
        #pragma omp critical
        {
            std::cout<<"candidate d="<<D<<" p="<<p<<" e="<<e0<<" q="<<q0<<" A=";
            for(int j:a) std::cout<<primes[j].p<<',';
            std::cout<<" B=";
            for(unsigned r:b) std::cout<<r<<',';
            std::cout<<std::endl;
        }
    }

    void at_leaf(Wide d, Wide f, Word low, int in_compulsory, Wide c, Wide fc) {
        ++counts.leaves;
        if (low+10<xlo||low>xhi) return;
        int cutoff=49;
        Word omitted=0;
        for (int j:a) {
            if (j>=cutoff) break;
            ++cutoff;
            omitted+=primes[j].hi;
        }
        if (Wide(low+11)*(sums[cutoff]-omitted+initial_tail)<Wide(scale)*scale) return;
        ++counts.mass;
        for (Word m:mandatory_moduli) if (std::gcd(Word(f%m),m)!=1) return;
        if (count_only) {++counts.valid_anchor; return;}

        // The factor L is the compulsory prefix_product divided by its intersection with d.
        load_word(D,d); load_word(F,f); load_word(C,c); load_word(Cf,fc);
        n=D*D;
        mpz_divexact(L.get_mpz_t(),prefix_product[compulsory].get_mpz_t(),C.get_mpz_t());
        Lf=derivatives[compulsory];
        mpz_submul(Lf.get_mpz_t(),Cf.get_mpz_t(),L.get_mpz_t());
        mpz_divexact(Lf.get_mpz_t(),Lf.get_mpz_t(),C.get_mpz_t());
        K=F*L;
        J=D*L;
        mpz_submul(J.get_mpz_t(),F.get_mpz_t(),Lf.get_mpz_t());
        if (!mpz_invert(inv.get_mpz_t(),J.get_mpz_t(),K.get_mpz_t()))
            throw std::logic_error("noninvertible anchor passed the gcd sieve");
        ++counts.valid_anchor;
        ++counts.short_cases;
        R=n*inv%K;
        if (mpz_odd_p(R.get_mpz_t())) {
            ++counts.parity;
            mpz_gcd(V.get_mpz_t(),R.get_mpz_t(),optional_product.get_mpz_t());
            if (V>=minprod[12+in_compulsory] && V<=maxprod[12+in_compulsory]) {
                q=R/V;
                if (q>2381 && q*V==R && mpz_gcd_ui(nullptr,q.get_mpz_t(),2)==1) {
                    // Any square of a bounded prime would remain in q after the gcd.
                    mpz_gcd(e.get_mpz_t(),q.get_mpz_t(),all_small.get_mpz_t());
                    if (e==1) {
                        ++counts.small_factor_hits;
                        e=L*V;
                        verify(e,q);
                    }
                }
            }
        }

        if (a.back()>=long_end) return;
        Word center=low+Word(Wide(scale)*scale/low);
        const Word err=long_width[12+in_compulsory]+16;
        if (!targets.possibly(center-err,center+16)) return;
        const auto& entries=a.back()<long_forced ? targets.all : targets.containing[a.back()];
        const auto first=std::lower_bound(entries.begin(),entries.end(),center-err,
            [&](unsigned j,Word m){return targets.v[j].mass<m;});
        if (first==entries.end()||targets.v[*first].mass>center+16) return;
        std::array<Word,4> chosen{};
        for (int i:a) chosen[i/64]|=Word(1)<<(i%64);
        U0=n+F*F;
        V0=D*F;
        for (auto it=first;it!=entries.end();++it) {
            const auto& s=targets.v[*it];
            if (s.mass>center+16) break;
            ++counts.windows;
            if ((chosen[0]&~s.mask[0])||(chosen[1]&~s.mask[1])||
                (chosen[2]&~s.mask[2])||(chosen[3]&~s.mask[3])) continue;
            ++counts.supports;
            den=s.product*U0-s.derivative*V0;
            if (den<=0) continue;
            num=s.product*V0+n*n;
            if (!mpz_divisible_p(num.get_mpz_t(),den.get_mpz_t())) continue;
            q=num/den;
            e=s.product/D;
            if (e*q<K*L) continue;
            verify(e,q);
        }
    }

    void visit(int from,int depth,Wide d,Wide f,Word low,int inside,Wide c,Wide fc) {
        const int left=10-depth, end=primes.size();
        if (stop.load(std::memory_order_relaxed)) return;
        if (!left) {at_leaf(d,f,low,inside,c,fc); return;}
        for (int j=from;j+left<=end;++j) {
            const auto& entry=primes[j];
            if (entry.p>caps[59-left]||low+depth+sums[j+left]-sums[j]<xlo) break;
            if (low+entry.lo>xhi) continue;
            a[depth]=j;
            // Maximize the mass by taking the smallest possible remaining d
            // primes and then the smallest available complementary primes.
            int prefix=49;
            Word extra=0;
            for(int i=0;i<10;++i) {
                const int idx=i<=depth?a[i]:j+i-depth;
                if (idx<prefix) ++prefix; else extra+=primes[idx].hi;
            }
            if (sums[prefix]+extra+initial_tail<2*scale) break;
            const unsigned p=entry.p;
            if (j<compulsory) visit(j+1,depth+1,d*p,f*p+d,low+entry.lo,inside+1,c*p,fc*p+c);
            else visit(j+1,depth+1,d*p,f*p+d,low+entry.lo,inside,c,fc);
        }
    }
};

int main(int argc,char** argv) {
    if (argc!=5) throw std::invalid_argument("usage: opposite count|solve SHARD SHARDS SECONDS");
    const bool count_only=std::string(argv[1])=="count";
    if (!count_only&&std::string(argv[1])!="solve") throw std::invalid_argument("invalid mode");
    const int shard=std::stoi(argv[2]),shards=std::stoi(argv[3]),seconds=std::stoi(argv[4]);
    if (shard<0||shard>=shards||seconds<=0) throw std::invalid_argument("invalid configuration");
    std::atomic<bool> stop(false);
    const auto start=std::chrono::steady_clock::now();
    for(unsigned p=2;p<=1190;++p) {
        bool prime=true;
        for(unsigned q=2;q*q<=p;++q) if (p%q==0) {prime=false;break;}
        if (!prime) continue;
        primes.push_back({p,scale/p,(scale+p-1)/p});
        sums.push_back(sums.back()+primes.back().hi);
        derivatives.push_back(derivatives.back()*p+prefix_product.back());
        prefix_product.push_back(prefix_product.back()*p);
        if(p<=157) {
            ++compulsory;
            if (mandatory_moduli.empty()||mandatory_moduli.back()>std::numeric_limits<Word>::max()/p)
                mandatory_moduli.push_back(1);
            mandatory_moduli.back()*=p;
        }
        if(p<=167) ++long_forced;
        if(p<=794) ++long_end;
    }
    all_small=prefix_product.back();
    optional_product=all_small/prefix_product[compulsory];
    mpq_class T=0;
    const mpq_class tiny(1,mpz_class("100000000000000000000"));
    for (int i=0;i<59;++i) {
        const mpq_class x=mpq_class(59-i)/(2-T-mpq_class(1,2382)-tiny);
        const mpz_class y=x.get_num()/x.get_den();
        caps[i]=std::min<unsigned>(1190,y.get_ui());
        T+=mpq_class(1,primes[i].p);
    }
    maxprod[0]=minprod[0]=1;
    for(int i=1;i<=22;++i) {
        maxprod[i]=maxprod[i-1]*caps[59-i];
        minprod[i]=minprod[i-1]*primes[compulsory+i-1].p;
    }
    for(int c=0;c<=10;++c) {
        mpz_class product=prefix_product[compulsory];
        for(int i=0;i<10-c;++i) product*=primes[compulsory+i].p;
        const mpq_class K_min=mpq_class(947,1000)*product;
        if (K_min<=mpq_class(long_q_min)*maxprod[12+c])
            throw std::logic_error("long q arithmetic bound failed");
        const mpq_class range=mpq_class(2)*scale*maxprod[12+c]/K_min;
        const mpz_class n=range.get_num()+range.get_den()-1;
        const mpz_class width=n/range.get_den();
        long_width[12+c]=width.get_ui();
    }
    CoreEnumerator en;
    if (!count_only) {
        for(int top=58;top<long_end;++top) {
            en.top=top;
            en.visit(long_forced,long_forced,sums[long_forced]);
        }
    }
    Targets targets(std::move(en.out));

    std::vector<std::array<int,5>> tasks;
    for(int i=1;i<int(primes.size());++i)
    for(int j=i+1;j<int(primes.size());++j)
    for(int k=j+1;k+6<int(primes.size());++k) {
        const Word partial=scale/2+primes[i].hi+primes[j].hi;
        if(partial+sums[k+7]-sums[k]<xlo) break;
        for (int l=k+1;l+5<int(primes.size());++l) {
            if(partial+primes[k].hi+sums[l+6]-sums[l]<xlo) break;
            tasks.push_back({0,i,j,k,l});
        }
    }
    std::cout<<"tasks="<<tasks.size()<<" large_supports="<<targets.v.size()<<std::endl;
    Counts total;
    unsigned done=0;
    #pragma omp parallel
    {
        Finder engine(targets,count_only,stop);
        #pragma omp for schedule(dynamic,1)
        for(int j=shard;j<int(tasks.size());j+=shards) {
            if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)
                stop.store(true,std::memory_order_relaxed);
            if (stop.load(std::memory_order_relaxed)) continue;
            engine.a[0]=0; engine.a[1]=tasks[j][1];
            engine.a[2]=tasks[j][2]; engine.a[3]=tasks[j][3]; engine.a[4]=tasks[j][4];
            Wide d=1,f=0,c=1,fc=0;
            Word m=0;
            int num=0;
            for(int idx:tasks[j]) {
                const auto& e=primes[idx];
                f=f*e.p+d; d*=e.p;
                m+=e.lo;
                if(idx<compulsory) {fc=fc*e.p+c; c*=e.p; ++num;}
            }
            engine.visit(tasks[j].back()+1,5,d,f,m,num,c,fc);
            #pragma omp atomic update
            ++done;
        }
        #pragma omp critical
        total+=engine.counts;
    }
    std::cout<<"shard="<<shard<<" shards="<<shards<<" done="<<done
             <<" complete="<<(!stop.load())<<" leaves="<<total.leaves<<" mass="<<total.mass
             <<" anchors="<<total.valid_anchor<<" short_cases="<<total.short_cases<<" odd="<<total.parity
             <<" factor_hits="<<total.small_factor_hits<<" windows="<<total.windows
             <<" supports="<<total.supports<<" candidates="<<total.candidates
             <<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
    return stop.load() ? 2 : 0;
}
