#include <algorithm>
#include <array>
#include <bitset>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <utility>
#include <vector>
#include <cassert>

namespace {
constexpr int n=299,lags=149;
using U=std::uint64_t;
using Mask=std::array<U,5>;
using Row=std::array<int,n>;
using Gram=std::array<int,lags>;
using P=std::bitset<n>;

Gram paf(const Row& w,const Mask& m){
    P plus,minus;
    for(int i=0;i<n;i++)if(w[i]){
        const int v=(m[i/64]>>(i%64)&1)?-w[i]:w[i];
        (v>0?plus:minus).set(i);
    }
    Gram result{};
    for(int d=1;d<=lags;d++){
        const auto a=(plus<<d)|(plus>>(n-d));
        const auto b=(minus<<d)|(minus>>(n-d));
        result[d-1]=int((a&plus).count()+(b&minus).count())-int((a&minus).count()+(b&plus).count());
    }
    return result;
}

using Key=unsigned __int128;
struct Local{
    Key charge=0;
    Mask mask{};
    Local& operator+=(const Local& b) {
        charge+=b.charge;
        for(int j=0;j<5;j++)mask[j]^=b.mask[j];
        return *this;
    }
};
using Block=std::vector<Local>;
using Split=std::vector<const Block*>;

template<class Visitor>
void visit(const Split& blocks,std::size_t index,const Local& current,const Visitor& record) {
    if(index==blocks.size()){
        record(current);
        return;
    }
    for(const auto& piece:*blocks[index]){
        Local next=current;
        next+=piece;
        visit(blocks,index+1,next,record);
    }
}

std::vector<Gram> generate(std::istream& input,const Row& source) {
    int size;
    input>>size;
    assert(size>0 && size<=12);
    std::vector<Block> blocks(size);
    for(auto& block:blocks){
        int length;
        input>>length;
        assert(length>1 && length<=8192);
        block.resize(length);
        for(auto& word:block){
            U lo,hi;
            input>>lo>>hi;
            word.charge=Key(lo)+(Key(hi)<<64);
            for(U& v:word.mask)input>>v;
        }
    }
    assert(input);
    U best=std::numeric_limits<U>::max();
    unsigned partition=0;
    for(unsigned mask=0;mask<(1U<<size);mask++){
        U a=1,b=1;
        for(int j=0;j<size;j++)(mask>>j&1?a:b)*=blocks[j].size();
        if(std::max(a,b)>=best)continue;
        best=std::max(a,b);
        partition=(a<=b ? mask : ((1U<<size)-1)^mask);
    }
    Split left,right;
    for(int j=0;j<size;j++)(partition>>j&1?left:right).push_back(&blocks[j]);
    std::vector<Local> first;
    visit(left,0,{},[&](const Local& s){first.push_back(s);});
    std::sort(first.begin(),first.end(),[](const Local& a,const Local& b){return a.charge<b.charge;});
    const auto original=paf(source,{});
    std::vector<Gram> rows;
    visit(right,0,{},[&](const Local& s){
        const auto required=Key{}-s.charge;
        auto j=std::lower_bound(first.begin(),first.end(),required,
                                [](const Local& a,Key want){return a.charge<want;});
        while(j!=first.end()&&j->charge==required){
            Local pair=*j;
            pair+=s;
            const auto actual=paf(source,pair.mask);
            for(int d=0;d<lags;d++)assert((actual[d]-original[d])%4==0);
            rows.push_back(actual);
            ++j;
        }
    });
    return rows;
}

struct Filter{
    int lo=0,hi=0,words=0;
    std::vector<U> accepts;
    std::vector<int> count;
    int index(int x)const{
        if(x<lo||x>hi||(x-lo)%4)return -1;
        return (x-lo)/4;
    }
    Filter(int d,const std::vector<Gram>& b,int bound):words((b.size()+63)/64) {
        const auto less=[d](const Gram& x,const Gram& y){return x[d]<y[d];};
        lo=std::min_element(b.begin(),b.end(),less)->at(d)-bound;
        hi=std::max_element(b.begin(),b.end(),less)->at(d)+bound;
        const int size=(hi-lo)/4+1;
        accepts.assign(std::size_t(size)*words,0);
        std::vector<U> eq(std::size_t(size)*words,0);
        std::vector<int> count_eq(size);
        count.resize(size,0);
        for(std::size_t j=0;j<b.size();j++){
            int k=index(b[j][d]);
            if(k<0)std::exit(17);
            eq[std::size_t(k)*words+j/64] |= U{1}<<(j%64);
            count_eq[k]++;
        }
        for(int i=0;i<size;i++)for(int k=std::max(0,i-bound/4);k<std::min(size,i+bound/4+1);k++){
            count[i]+=count_eq[k];
            for(int j=0;j<words;j++)accepts[std::size_t(i)*words+j]|=eq[std::size_t(k)*words+j];
        }
    }
    const U* set(int k)const{return &accepts[std::size_t(k)*words];}
};

struct Record{
    int raw16=0,exact=0,peak=0,sse=0;
    std::array<int,4> score()const{return {raw16,exact,-peak,-sse};}
};
Record metric(const Gram& a,const Gram& b,const Gram& t){
    Record r{1,1,0,0};
    for(int d=0;d<lags;d++){
        int x=2*(2+a[d]+b[d]+t[d]);
        if(x%8)std::exit(18);
        r.raw16+=4*(x%16==0);
        r.exact+=4*(x==0);
        r.peak=std::max(r.peak,std::abs(x));
        r.sse+=4*x*x;
    }
    return r;
}
}

int main(){
    constexpr int cap=20;
    std::array<Row,2> words;
    for(auto& row:words)for(int& v:row)std::cin>>v;
    int tail_count;
    std::cin>>tail_count;
    assert(tail_count==4);
    std::vector<Gram> tails;
    std::array<Gram,2> original{paf(words[0],{}),paf(words[1],{})};
    for(int j=0;j<tail_count;j++){
        Row s,t;
        for(int& v:s)std::cin>>v;
        for(int& v:t)std::cin>>v;
        Gram combined=paf(s,{}),other=paf(t,{});
        for(int d=0;d<lags;d++){
            combined[d]+=other[d];
            assert((2+combined[d]+original[0][d]+original[1][d])%4==0);
        }
        tails.push_back(combined);
    }
    std::array<std::vector<Gram>,2> cand;
    for(int j=0;j<2;j++)cand[j]=generate(std::cin,words[j]);
    assert(cand[0].size()==21588 && cand[1].size()==82684);
    const std::array<U,4> expected{13,1,2,0};
    std::cout<<"exact signed PAF head sizes "<<cand[0].size()<<" "<<cand[1].size()<<std::endl;
    std::vector<Filter> filters;
    for(int d=0;d<lags;d++)filters.emplace_back(d,cand[1],cap);
    std::vector<U> rows(filters[0].words);
    for(int j=0;j<tail_count;j++){
        U hits=0,small=0,checked=0;
        Record best{-1,0,0,0};
        const auto& tail=tails[j];
        for(std::size_t i=0;i<cand[0].size();i++){
            const auto& a=cand[0][i];
            std::array<std::pair<int,int>,lags> order;
            std::array<int,lags> keys;
            for(int d=0;d<lags;d++){
                const int q=filters[d].index(-2-a[d]-tail[d]);
                if(q<0){order[0]={0,0};break;}
                keys[d]=q;
                order[d]={filters[d].count[q],d};
            }
            if(!order[0].first)continue;
            constexpr int kernel=24;
            std::partial_sort(order.begin(),order.begin()+kernel,order.end());
            if(!order[0].first)continue;
            const int d0=order[0].second;
            const U* start=filters[d0].set(keys[d0]);
            std::copy(start,start+rows.size(),rows.begin());
            bool bad=false;
            for(int k=1;k<kernel;k++){
                const int d=order[k].second;
                const U* g=filters[d].set(keys[d]);
                U have=0;
                for(std::size_t x=0;x<rows.size();x++){rows[x]&=g[x];have|=rows[x];}
                if(!have){bad=true;break;}
            }
            if(bad)continue;
            for(std::size_t x=0;x<rows.size();x++)for(U z=rows[x];z;z&=z-1){
                const unsigned b=64*x+std::countr_zero(z);
                const auto& c=cand[1][b];
                checked++;
                bool ok=true;
                for(int d=0;d<lags;d++)if(std::abs(2+a[d]+c[d]+tail[d])>cap){
                    ok=false;
                    break;
                }
                if(!ok)continue;
                hits++;
                const auto m=metric(a,c,tail);
                small+=m.peak<=32;
                if(m.score()>best.score()){
                    best=m;
                    std::cout<<"record "<<j<<" "<<i<<" "<<b<<" mod16/exact/peak/SSE "
                             <<m.raw16<<" "<<m.exact<<" "<<m.peak<<" "<<m.sse<<std::endl;
                }
            }
        }
        std::cout<<"complete exact fixed tail "<<j<<" conceptual "
                 <<U(cand[0].size())*cand[1].size()<<" shortlisted "<<checked
                 <<" peak40 "<<hits<<" peak32 "<<small<<std::endl;
        assert(hits==expected[j] && small==0);
    }
}
