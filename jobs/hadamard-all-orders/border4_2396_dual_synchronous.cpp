#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace quotient {
using U=std::uint64_t;
constexpr int q=23;
using Profile=std::array<int,2*q>;
using Target=std::array<int,12>;
using Key=std::array<int,3>;
struct Option{std::array<int,4> values;Key key;};
struct Cell{std::vector<int> sites; std::vector<Option> domain; unsigned baseline;};
using Cells=std::array<Cell,12>;
struct Joined{unsigned i,j;Key key;};
Key add(const Key& a,const Key& b){return {a[0]+b[0],a[1]+b[1],a[2]+b[2]};}
Key sub(const Key& a,const Key& b){return {a[0]-b[0],a[1]-b[1],a[2]-b[2]};}
void fill(Profile& p,const Cell& f,unsigned v){
    const auto& vals=f.domain[v].values;
    for(unsigned s=0;s<f.sites.size();s++){
        p[f.sites[s]]=vals[s];p[q+f.sites[s]]=vals[f.sites.size()+s];
    }
}
bool match(const Profile& p,const Target& target){
    for(int d=1;d<=11;d++){
        int a=0;
        for(int s=0;s<q-d;s++)a+=p[s]*p[s+d]+p[q+s]*p[q+s+d];
        for(int s=q-d;s<q;s++)a+=p[s]*p[s+d-q]+p[q+s]*p[q+s+d-q];
        if(a!=target[d])return false;
    }
    return true;
}
int run(){
    constexpr int radius=8;
    Profile p{};
    for(int& x:p)std::cin>>x;
    Target a{};
    Key universe{};
    for(int d=0;d<=11;d++)for(int x=0;x<q;x++)
        a[d]+=p[x]*p[(x+d)%q]+p[q+x]*p[q+(x+d)%q];
    universe[0]=a[0];
    for(int x=0;x<q;x++){universe[1]+=p[x];universe[2]+=p[q+x];}
    Cells cells;
    std::vector<unsigned> big,small;
    std::array<unsigned,12> selected{};
    for(unsigned c=0;c<cells.size();c++){
        auto& f=cells[c];
        unsigned n,e;std::cin>>n;
        f.sites.resize(n);
        for(auto& x:f.sites)std::cin>>x;
        std::cin>>e;f.domain.resize(e);
        if(e>2)big.push_back(c);else small.push_back(c);
        for(unsigned i=0;i<e;i++){
            auto& opt=f.domain[i];
            bool base=true;
            for(unsigned r=0;r<2;r++)for(unsigned j=0;j<n;j++){
                int& v=opt.values[n*r+j];
                std::cin>>v;
                base=base&&(v==p[r*q+f.sites[j]]);
                opt.key[0]+=v*v;opt.key[r+1]+=v;
            }
            if(base)f.baseline=i;
        }
        selected[c]=f.baseline;
    }
    if(!std::cin||big.size()!=4)return 1;
    std::array<std::vector<Joined>,2> decks;
    Key smallest_small{};
    for(unsigned j:small)smallest_small=add(smallest_small,cells[j].domain[cells[j].baseline].key);
    for(int h=0;h<2;h++){
        const auto& l=cells[big[2*h]].domain;
        const auto& r=cells[big[2*h+1]].domain;
        for(unsigned i=0;i<l.size();i++)for(unsigned j=0;j<r.size();j++){
            Key t=add(l[i].key,r[j].key);
            if(t[0]+smallest_small[0]<=universe[0])decks[h].push_back({i,j,t});
        }
    }
    std::map<Key,std::vector<Joined>> table;
    for(const auto& w:decks[0])table[w.key].push_back(w);
    for (unsigned j : small) for (const auto& option : cells[j].domain)
        if (option.key[0] != cells[j].domain[cells[j].baseline].key[0]) return 2;
    U sum=0,passed=0,small_count=0;
    auto rec=[&](auto&& rec,unsigned s,int left,const Key& charge)->void{
        if(s==small.size()) {
            small_count++;
            auto needed=sub(universe,charge);
            for(const auto& r:decks[1]){
                const auto it=table.find(sub(needed,r.key));
                if(it==table.end())continue;
                fill(p,cells[big[2]],r.i);fill(p,cells[big[3]],r.j);
                selected[big[2]]=r.i;selected[big[3]]=r.j;
                for(const auto& l:it->second){
                    ++sum;
                    fill(p,cells[big[0]],l.i);fill(p,cells[big[1]],l.j);
                    if(!match(p,a))continue;
                    selected[big[0]]=l.i;selected[big[1]]=l.j;
                    for (unsigned j=0;j<cells.size();++j)
                        if (selected[j]!=cells[j].baseline)
                            throw std::runtime_error("changed exact C23 profile");
                    ++passed;
                    for(unsigned c:selected)std::cout<<c<<" ";
                    std::cout<<"\n";
                }
            }
            return;
        }
        const auto i=small[s];
        const auto& f=cells[i];
        for(unsigned j=0;j<f.domain.size();j++){
            bool diff=j!=f.baseline;
            if(left<diff)continue;
            fill(p,f,j);selected[i]=j;
            rec(rec,s+1,left-diff,add(charge,f.domain[j].key));
        }
    };
    rec(rec,0,radius,Key{});
    std::cerr<<"small choices "<<small_count<<" aligned diagonal and sums "<<sum
             <<" exact C23 "<<passed<<"\n";
    return !(small_count==256 && sum==340397464 && passed==1);
}
}

namespace gram {
constexpr int n=299,L=149;
using Z=std::int64_t;
using U=std::uint64_t;
using I=__int128;
using Mask=std::array<U,5>;
using Word=std::array<Z,n>;
using V=std::array<Z,4>;
V add(const V& a,const V& b){
    return {a[0]+b[0],a[1]+b[1],a[2]+b[2],a[3]+b[3]};
}
int run(){
    std::array<Word,2> words;
    for(auto& w:words)for(Z& z:w)std::cin>>z;
    int count;
    std::cin>>count;
    if(count!=4)return 1;
    std::array<std::vector<Mask>,4> blocks;
    for(auto& block:blocks){
        unsigned len;std::cin>>len;
        if(len<2||len>63)return 2;
        block.resize(len);
        for(auto& m:block)for(U& x:m)std::cin>>x;
    }
    std::vector<unsigned> all;
    U original=1;for(auto& b:blocks)original*=b.size();
    all.reserve(original);
    for(unsigned i=0;i<blocks[0].size();i++)for(unsigned j=0;j<blocks[1].size();j++)
        for(unsigned a=0;a<blocks[2].size();a++)for(unsigned b=0;b<blocks[3].size();b++)
            all.push_back(i|(j<<6)|(a<<12)|(b<<18));
    for(int k=0;k<L;k++){
        unsigned frequency;
        Z x2,y2,cap;
        Word a,b;
        std::cin>>frequency>>x2>>y2>>cap;
        for(Z& u:a)std::cin>>u;
        for(Z& u:b)std::cin>>u;
        if(!std::cin)return 3;
        V base{};
        for(int s=0;s<n;s++)for(int r=0;r<2;r++){
            base[2*r]+=a[s]*words[r][s];base[2*r+1]+=b[s]*words[r][s];
        }
        std::array<std::vector<V>,4> contribution;
        for(int j=0;j<4;j++)for(const auto& mask:blocks[j]){
            V v{};
            for(int w=0;w<5;w++)for(U z=mask[w];z;z&=z-1){
                const int i=w*64+std::countr_zero(z);
                if(i>=n)return 4;
                for(int r=0;r<2;r++){
                    v[2*r]-=2*words[r][i]*a[i];v[2*r+1]-=2*words[r][i]*b[i];
                }
            }
            contribution[j].push_back(v);
        }
        std::vector<unsigned> pass;
        const I bound=I(cap)*x2*y2;
        for(unsigned code:all){
            V v=base;
            for(int j=0;j<4;j++)v=add(v,contribution[j][code>>(6*j)&63]);
            const I real=I(v[0])*v[0]+I(v[2])*v[2],imag=I(v[1])*v[1]+I(v[3])*v[3];
            if(real*y2+imag*x2<=bound)pass.push_back(code);
        }
        if(pass.size()!=all.size())std::cout<<frequency<<" rejected "<<all.size()-pass.size()
                                          <<" remaining "<<pass.size()<<std::endl;
        all=std::move(pass);
        if(all.empty())break;
    }
    std::cout<<"Projected integer Gram "<<original<<" -> "<<all.size()<<std::endl;
    for(unsigned code:all){
        Mask m{};
        for(int j=0;j<4;j++)for(int w=0;w<5;w++)m[w]^=blocks[j][code>>(6*j)&63][w];
        std::cout<<"survivor";for(U x:m)std::cout<<" "<<x;
        std::cout<<"\n";
    }
    return !(original==1926296 && all.empty());
}
}

int main(int argc, char** argv) {
    if (argc != 2) return 1;
    const std::string_view mode(argv[1]);
    if (mode == "quotient") return quotient::run();
    if (mode == "gram") return gram::run();
    return 1;
}
