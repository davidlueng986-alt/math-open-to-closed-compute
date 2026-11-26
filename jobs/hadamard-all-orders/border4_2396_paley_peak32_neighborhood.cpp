#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
constexpr int n=299,h=n/2;
using Word=std::array<int,n>;
using E=std::array<int,h>;
using Mask=std::array<uint64_t,5>;
struct Move{std::array<int,4> sites;Mask support;E delta;};
Word U,V,W;
E error;
std::array<std::array<int,23>,13> ix{};
std::array<std::array<int,h>,n> raw_change{};
std::array<std::array<int,n>,n> folded{};
long long single_checked=0,two_checked=0,six_checked=0,peak24=0;
std::tuple<int,int,int,int> best;

int at(const Mask& a,int i){return (a[i/64]>>(i%64))&1;}
void put(Mask& a,int i){a[i/64]|=1ULL<<(i%64);}
bool overlap(const Mask& a,const Mask& b){for(int i=0;i<5;++i)if(a[i]&b[i])return true;return false;}
std::string repr(Mask a){std::ostringstream s;s<<std::hex<<a[4];for(int j=3;j>=0;--j)s<<std::setfill('0')<<std::setw(16)<<a[j];return s.str();}
Mask neg_bits(const Word& w){Mask p{};for(int i=0;i<n;++i)if(w[i]<0)put(p,i);return p;}
int lag(int a,int b){int d=std::abs(a-b);return std::min(d,n-d)-1;}

template<size_t m> E delta(const std::array<int,m>& F){
    E r{};
    for(const int a:F)for(int d=0;d<h;++d)r[d]+=raw_change[a][d];
    for(int i=0;i<m;++i)for(int j=i+1;j<m;++j)r[folded[F[i]][F[j]]]+=W[F[i]]*W[F[j]];
    return r;
}
std::tuple<int,int,int,int> metrics(const E& r){
    int peak=0,sse=0,odd=0,exact=0;
    for(const int v:r){peak=std::max(peak,std::abs(v));sse+=v*v;odd+=v%2!=0;exact+=v==0;}
    return {peak,256*sse,4*odd,-4*exact};
}
template<size_t m>void test(const E& e,const std::array<int,m>& F,std::string kind){
    for(const int x:e)if(std::abs(x)>std::get<0>(best))return;
    auto s=metrics(e);
    peak24+=std::get<0>(s)<=3;
    if(s>=best)return;
    best=s;
    Word w=W;for(int k:F)w[k]=-w[k];
    auto [p,sse,odd,exact]=s;
    std::cout<<"new "<<kind<<" peak "<<8*p<<" SSE "<<sse<<" mod16 "<<597-odd<<" exact "<<1-exact<<' '<<repr(neg_bits(U))<<' '<<repr(neg_bits(V))<<' '<<repr(neg_bits(w))<<std::endl;
}
int main(int argc,char**argv){
    for(int& x:U)std::cin>>x;for(int& x:V)std::cin>>x;for(int& x:W)std::cin>>x;
    for(int i=0;i<n;++i)ix[i%13][i%23]=i;
    for(int i=0;i<n;++i){
       for(int d=0;d<h;++d)raw_change[i][d]=-W[i]*(W[(i+d+1)%n]+W[(i+n-d-1)%n])/2;
       for(int j=0;j<n;++j)folded[i][j]=lag(i,j);
    }
    for(int d=1;d<=h;++d){
        for(int i=0;i<n;++i)error[d-1]+=U[i]*U[(i+d)%n]+V[i]*V[(i+d)%n]+2*W[i]*W[(i+d)%n];
        if(error[d-1]%8)std::abort();
        error[d-1]/=8;
    }
    best=metrics(error);
    std::vector<Move> rect;
    for(int x=0;x<13;++x)for(int y=x+1;y<13;++y)for(int a=0;a<23;++a)for(int b=a+1;b<23;++b){
        std::array<int,4> F={ix[x][a],ix[x][b],ix[y][a],ix[y][b]};
        if(W[F[0]]!=W[F[3]]||W[F[1]]!=W[F[2]]||W[F[0]]==W[F[1]])continue;
        Move m{F,{},delta(F)};for(int k:F)put(m.support,k);
        rect.push_back(m);
        E e=error;for(int j=0;j<h;++j)e[j]+=m.delta[j];
        ++single_checked;test(e,F,"rect");
    }
    for(int i=0;i<static_cast<int>(rect.size());++i)for(int j=i+1;j<static_cast<int>(rect.size());++j){
        const auto& a=rect[i];const auto& b=rect[j];
        if(overlap(a.support,b.support))continue;
        E e{};
        for(int x:a.sites)for(int y:b.sites)e[folded[x][y]]+=W[x]*W[y];
        for(int d=0;d<h;++d)e[d]+=error[d]+a.delta[d]+b.delta[d];
        std::array<int,8> F;std::copy(a.sites.begin(),a.sites.end(),F.begin());std::copy(b.sites.begin(),b.sites.end(),F.begin()+4);
        ++two_checked;test(e,F,"two-rect");
    }
    for(int x=0;x<13;++x)for(int y=x+1;y<13;++y)for(int z=y+1;z<13;++z)
    for(int a=0;a<23;++a)for(int b=a+1;b<23;++b)for(int c=b+1;c<23;++c){
        std::array<int,3> rows={x,y,z},cols={a,b,c},cut={0,1,2};
        do{
            std::array<int,6> F; bool ok=true;
            for(int i=0;i<3;++i){
                F[2*i]=ix[rows[i]][cols[(cut[i]+1)%3]];
                F[2*i+1]=ix[rows[i]][cols[(cut[i]+2)%3]];
                if(W[F[2*i]]==W[F[2*i+1]]){ok=false;break;}
            }
            if(!ok)continue;
            for(int j=0;j<3;++j){
                int s=0;for(int i=0;i<3;++i)if(cut[i]!=j)s+=W[ix[rows[i]][cols[j]]];
                if(s){ok=false;break;}
            }
            if(!ok)continue;
            E e=delta(F);for(int d=0;d<h;++d)e[d]+=error[d];
            ++six_checked;test(e,F,"six-cycle");
        }while(std::next_permutation(cut.begin(),cut.end()));
    }
    std::cout<<"complete rectangles="<<single_checked<<" pairs="<<two_checked<<" six="<<six_checked<<" peak24="<<peak24<<std::endl;
}
