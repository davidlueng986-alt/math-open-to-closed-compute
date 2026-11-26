#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int n=299, half=149, bits=151, degree=13, size=1<<degree;
using U=std::uint64_t;
using Sites=std::bitset<n>;
struct Code {
    std::array<U,3> words{};
    void set(int i) {words[i/64] |= U(1)<<(i%64);}
    bool test(int i) const {return (words[i/64]>>(i%64))&1;}
    int byte(int i) const {return (words[i/8]>>(8*(i%8)))&255;}
    int head() const {
        for(int j=2;j>=0;--j) if(words[j]) return 64*j+63-std::countl_zero(words[j]);
        return -1;
    }
    Code& operator^=(const Code& other) {
        for(int i=0;i<3;++i) words[i]^=other.words[i];
        return *this;
    }
};
Code operator^(Code a,const Code& b) {return a^=b;}
struct Word {Sites pos,neg;};
Sites rotate(const Sites& s,int d) {return (s<<d)|(s>>(n-d));}
Sites support(const Word& a) {return a.pos|a.neg;}
Word flip(const Word& a,const Sites& f) {return {a.pos^f,a.neg^f};}
int sum(const Word& a) {return int(a.pos.count())-int(a.neg.count());}
int charge(const Word& a,const Sites& f) {return int((a.pos&f).count())-int((a.neg&f).count());}
int corr(const Word& a,int d) {
    auto x=rotate(a.pos,d),y=rotate(a.neg,d);
    return int((x&a.pos).count()+(y&a.neg).count())-int((x&a.neg).count()+(y&a.pos).count());
}
Sites read_sites() {
    Sites out;
    for(int i=0;i<5;++i) {
        U x;
        if(!(std::cin>>x)) throw std::runtime_error("invalid mask");
        while(x) {out.set(64*i+std::countr_zero(x));x&=x-1;}
    }
    return out;
}
void write_sites(const Sites& s) {
    for(int j=0;j<5;++j) {
        U w=0;
        for(int i=0;i<64 && 64*j+i<n;++i) if(s[64*j+i])w|=U(1)<<i;
        std::cout<<" "<<w;
    }
}
struct Tail {
    std::array<Code,bits> pivots{};
    std::array<Sites,bits> reps{};
    std::array<int,bits> compression{};
    std::array<std::array<unsigned,256>,19> table{};
    int rank=0;
    void add(Code a,Sites f) {
        for(int p=a.head();p>=0;p=a.head()) {
            if(!pivots[p].test(p)) {
                pivots[p]=a;reps[p]=f;++rank;
                return;
            }
            a^=pivots[p];f^=reps[p];
        }
    }
    explicit Tail(const std::array<Word,2>& phases) {
        for(int k=0;k<2;++k) {
            auto s=support(phases[k]);
            if(s.none()||s.count()%2)throw std::runtime_error("unexpected phase support");
            for(int i=0;i<n;++i)if(s[i]) {
                Code c;c.set(half+k);
                for(int d=1;d<=half;++d)if(s[(i+d)%n]!=s[(i+n-d)%n])c.set(d-1);
                add(c,Sites().set(i));
            }
        }
        if(rank!=128)throw std::runtime_error("unexpected augmented rank");
        int l=0;
        for(int i=0;i<bits;++i)if(!pivots[i].test(i))compression[i]=l++;
        for(int i=0;i<bits;++i) {
            Code c;c.set(i);
            for(int j=bits-1;j>=0;--j)if(c.test(j)&&pivots[j].test(j))c^=pivots[j];
            unsigned u=0;
            for(int j=0;j<bits;++j)if(c.test(j))u|=1U<<compression[j];
            table[i/8][1<<(i%8)]=u;
        }
        for(auto& t:table)for(unsigned j=1;j<256;++j)
            if(j&(j-1))t[j]=t[j&(j-1)]^t[j&-j];
    }
    unsigned project(const Code& c) const {
        unsigned u=0;for(int j=0;j<19;++j)u^=table[j][c.byte(j)];
        return u;
    }
    Sites lift(Code c) const {
        Sites s;
        for(int j=bits-1;j>=0;--j)if(c.test(j)) {
            if(!pivots[j].test(j))throw std::runtime_error("nonzero residual");
            c^=pivots[j];s^=reps[j];
        }
        return s;
    }
};
struct Block {
    std::array<Sites,degree> basis;
    std::array<Sites,size> masks;
    std::array<Code,size> raw;
    void init(const Word& original) {
        for(auto& f:basis)f=read_sites();
        std::array<int,half> old;
        for(int d=1;d<=half;++d)old[d-1]=corr(original,d);
        for(unsigned i=1;i<size;++i){
            auto& f=masks[i]=masks[i&(i-1)]^basis[std::countr_zero(i)];
            auto current=flip(original,f);
            for(int d=1;d<=half;++d){
                int v=corr(current,d)-old[d-1];
                if(v%4)throw std::runtime_error("invalid paired-fiber basis");
                if((v/4)&1)raw[i].set(d-1);
            }
        }
    }
    std::vector<Code> polar(const Sites& g,const Sites& p) const {
        std::array<Code,degree> delta{};
        std::vector<Code> out(size);
        if(g.none())return out;
        for(int d=1;d<=half;++d){
            auto e=p&rotate(p,d)&(g^rotate(g,d));
            for(int k=0;k<degree;++k)
                if((e&(basis[k]^rotate(basis[k],d))).count()&1)delta[k].set(d-1);
        }
        for(unsigned i=1;i<size;++i)out[i]=out[i&(i-1)]^delta[std::countr_zero(i)];
        return out;
    }
};
using Counts=std::array<U,7>;
using Margins=std::array<int,13>;
Margins compress(const Word& w) {
    Margins m{};
    for (int i=0;i<n;++i) m[i%13]+=int(w.pos[i])-int(w.neg[i]);
    return m;
}
U quotient_energy(const std::array<Word,2>& front,const std::array<Word,2>& tail) {
    std::array<Margins,4> m{compress(front[0]),compress(front[1]),compress(tail[0]),compress(tail[1])};
    U value=0;
    for (int d=0;d<=6;++d) {
        int q=d?46:-553;
        for (int r=0;r<4;++r) for (int i=0;i<13;++i)
            q+=(r<2?1:2)*m[r][i]*m[r][(i+d)%13];
        value+=(d?2:1)*std::int64_t(q)*q;
    }
    return value;
}
struct Error {int d,e;unsigned projected;};
U record=U(-1);
std::vector<unsigned short> table(1U<<23);
void pair_case(const std::array<Word,4>& original,const std::vector<Block>& blocks,
               int a,int b,int label,const std::array<Sites,3>& g,int radius,Counts& stats){
    ++stats[0];
    auto u=flip(original[0],g[0]),v=flip(original[1],g[1]);
    const std::array<Word,2> front{u,v};
    const std::array<int,2> sums{sum(u),sum(v)-1};
    if(sums[0]%2||sums[1]%2)throw std::runtime_error("unexpected first sum parity");
    const int ar=a/4,br=b/4;
    const bool same=ar==br;
    if(same&&sums[1-ar])return;
    ++stats[1];
    auto last=flip(original[3],g[2]);
    auto z=(original[2].pos&last.pos)|(original[2].neg&last.neg);
    auto w=(original[2].pos&last.neg)|(original[2].neg&last.pos);
    if((z&w).any()||(z|w)!=support(last))throw std::runtime_error("invalid phases");
    const std::array<Word,2> phases{{
        {original[2].pos&z,original[2].neg&z},
        {original[2].pos&w,original[2].neg&w}}};
    Tail reduce(phases);
    Code origin;
    for(int d=1;d<=half;++d){
        int r=corr(u,d)+corr(v,d)+2*corr(phases[0],d)+2*corr(phases[1],d)+2;
        if(r%4)throw std::runtime_error("invalid front/tail mod four");
        if((r/4)&1)origin.set(d-1);
    }
    for(int j=0;j<2;++j)if((sum(phases[j])/2)&1)origin.set(half+j);

    // Move each neutral block from the anchor signs to the selected affine seed.
    auto corr_a=blocks[a].polar(g[ar],support(original[ar]));
    auto corr_b=blocks[b].polar(g[br],support(original[br]));
    std::array<int,size> vals{};
    std::array<unsigned short,size> next{};
    std::array<int,53> sum_counts{};
    // Direct tables retain every collision of the 23-bit tail projection.
    std::vector<unsigned> used;
    for(unsigned i=0;i<size;++i){
        int e=charge(front[br],blocks[b].masks[i]);
        if(!same&&2*e!=sums[br])continue;
        ++sum_counts[e+26];
        unsigned c=reduce.project(blocks[b].raw[i]^corr_b[i]);
        vals[i]=e;
        next[i]=table[c];
        if(!table[c])used.push_back(c);
        table[c]=i+1;
    }
    // Exact C13 forces an even number of errors in each inverse residue class.
    auto qclass=[](int d){int k=d%13;return std::min(k,13-k);};
    std::array<unsigned,half> error_col{};
    for(int d=0;d<half;++d){Code c;c.set(d);error_col[d]=reduce.project(c);}
    std::vector<Error> errors;
    if (radius == 0) {
        errors.push_back({-1,-1,0});
    } else {
        for (int i=0;i<half;++i) for (int j=i+1;j<half;++j)
            if(qclass(i+1)==qclass(j+1)) errors.push_back({i,j,error_col[i]^error_col[j]});
        if (errors.size() != 1573) throw std::runtime_error("unexpected class-even error count");
    }
    for(unsigned i=0;i<size;++i){
        int e=charge(front[ar],blocks[a].masks[i]);
        if(!same&&2*e!=sums[ar])continue;
        int goal=same?sums[ar]/2-e:sums[br]/2;
        if(goal<-26||goal>26||!sum_counts[goal+26])continue;
        stats[2]+=U(sum_counts[goal+26])*errors.size();
        Code c=origin^blocks[a].raw[i]^corr_a[i];
        unsigned t=reduce.project(c);
        for(const auto& err:errors) {
            for(unsigned jj=table[t^err.projected]; jj; jj=next[jj-1]) {
                unsigned j=jj-1;
                if(vals[j]!=goal)continue;
                ++stats[3];
                Code ce;
                if (radius) {ce.set(err.d);ce.set(err.e);}
                auto f=reduce.lift(c^blocks[b].raw[j]^corr_b[j]^ce);
                const std::array<Word,2> tail{flip(phases[0],f&z),flip(phases[1],f&w)};
                if(sum(tail[0])||sum(tail[1]))continue;
                ++stats[4];
                stats[5]+=g[2].any();
                std::array<Sites,2> ff{g[0],g[1]};
                ff[ar]^=blocks[a].masks[i];
                ff[br]^=blocks[b].masks[j];
                U E=quotient_energy({flip(original[0],ff[0]),flip(original[1],ff[1])},tail);
                if(!E)++stats[6];
                if(radius&&E>=record&&E)continue;
                record=E;
                std::cout<<"hit "<<a<<" "<<b<<" "<<label<<" "<<err.d+1<<" "<<err.e+1;
                write_sites(ff[0]);write_sites(ff[1]);write_sites(f);
                std::cout<<"\n";
            }
        }
    }
    for(auto k:used)table[k]=0;

}
} // namespace

int main(int argc,char** argv){
    try{
        if (argc != 2) throw std::runtime_error("specify radius 0 or 2");
        const int radius = std::stoi(argv[1]);
        if (radius != 0 && radius != 2) throw std::runtime_error("unsupported radius");
        std::array<Word,4> a;
        for(auto& w:a)for(int i=0;i<n;++i){
            int v;
            if(!(std::cin>>v))throw std::runtime_error("invalid seed");
            if(v>0)w.pos.set(i);
            if(v<0)w.neg.set(i);
        }
        std::vector<Block> blocks(8);
        for(int j=0;j<8;++j)blocks[j].init(a[j/4]);
        Counts total{};
        for(int i=0;i<28;++i){
            int u,v,m;
            if(!(std::cin>>u>>v>>m))throw std::runtime_error("missing partition");
            Counts stats{};
            for(int j=0;j<m;++j){
                const std::array<Sites,3> g{read_sites(),read_sites(),read_sites()};
                pair_case(a,blocks,u,v,j,g,radius,stats);
            }
            for(int j=0;j<6;++j)total[j]+=stats[j];

        }
        std::cout<<"total";
        for(auto t:total)std::cout<<" "<<t;
        std::cout<<"\n";
    }catch(const std::exception& e){
        std::cerr<<e.what()<<"\n";
        return 1;
    }
}
