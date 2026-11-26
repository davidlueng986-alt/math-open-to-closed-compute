#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <immintrin.h>

using namespace std;
constexpr int p=16, half=12, states=531441;
using Row=array<int,p>;
using Deck=array<int16_t,p>;
using Slot=array<int,9>;
using Profile=array<Slot,p>;
array<Row,24> columns;
vector<Profile> weights;

vector<Deck> build(int first){
    vector<Deck> out;
    out.reserve(states);
    auto walk=[&](auto&& rec,int depth,Deck& deck)->void{
        if(depth<0){out.push_back(deck);return;}
        const auto& v=columns[first+depth];
        for(int j=0;j<p;j++)deck[j]-=v[j];
        for(int q=-1;q<=1;q++){
            rec(rec,depth-1,deck);
            for(int j=0;j<p;j++)deck[j]+=v[j];
        }
        for(int j=0;j<p;j++)deck[j]-=2*v[j];
    };
    Deck w{};
    walk(walk,half-1,w);
    assert(out.size()==states);
    return out;
}

int key(const Deck& v,int s,int phase){
    int out=0;
    for(int j=0;j<4;j++){
        int x=64+phase*v[s+j];
        assert(x>2&&x<125);
        out|=x<<(7*j);
    }
    return out;
}

bool within(int mask,int side_limit,int total_limit){
    return __builtin_popcount(unsigned(mask))<=2*total_limit
        && __builtin_popcount(unsigned(mask)&65535)<=2*side_limit
        && __builtin_popcount(unsigned(mask)>>16)<=2*side_limit;
}

struct Bucket {
    unsigned key=0;
    int head=-1;
};

constexpr unsigned buckets=1<<21;

unsigned locate(const vector<Bucket>& table, unsigned key){
    unsigned slot=(key*2654435761U)>>(32-21);
    while(table[slot].key && table[slot].key!=key)slot=(slot+1)&(buckets-1);
    return slot;
}

int main(){
    for(auto& a:columns)for(int& v:a)cin>>v;
    int nprofiles;
    cin>>nprofiles;
    weights.resize(nprofiles);
    for(auto& a:weights)for(auto& b:a)for(int& v:b)cin>>v;
    assert(cin&&(nprofiles==380||nprofiles==852));
    const auto L=build(0),R=build(half);
    vector<Bucket> table(buckets);
    vector<int> next(states,-1);
    vector<unsigned> touched;
    touched.reserve(states);
    vector<int8_t> side(states);
    for(int t=0;t<states;t++){
        int key=t;
        for(int i=0;i<12;i++){
            int d=key%3;key/=3;
            if(d!=1){side[t]=d-1;break;}
        }
    }
    vector<int> shifts;
    for(int a=-2;a<=2;a++)for(int b=-2;b<=2;b++)
        for(int c=-2;c<=2;c++)for(int d=-2;d<=2;d++)shifts.push_back(a+128*b+16384*c+2097152*d);
    unordered_set<uint64_t> seen;
    uint64_t tested=0, narrow=0,passed=0;
    for(int start:{0,4,8,12}){
        for(unsigned k:touched)table[k]=Bucket{};
        touched.clear();
        for(int i=0;i<states;i++){
            unsigned key_value=key(R[i],start,1);
            unsigned slot=locate(table,key_value);
            if(!table[slot].key){
                table[slot].key=key_value;
                touched.push_back(slot);
            }
            next[i]=table[slot].head;
            table[slot].head=i;
        }
        for(unsigned a=0;a<states;a++){
            if(side[a]<0)continue;
            bool zero=side[a]==0;
            int k=key(L[a],start,-1);
            auto u=_mm256_loadu_si256(reinterpret_cast<const __m256i*>(L[a].data()));
            for(int s:shifts){
                unsigned slot=locate(table,k+s);
                for(int i=table[slot].head;i>=0;i=next[i]){
                    if(zero&&side[i]!=1)continue;
                    tested++;
                    auto v=_mm256_loadu_si256(reinterpret_cast<const __m256i*>(R[i].data()));
                    auto w=_mm256_add_epi16(u,v);
                    auto aw=_mm256_abs_epi16(w);
                    auto m2=_mm256_movemask_epi8(_mm256_cmpgt_epi16(aw,_mm256_set1_epi16(2)));
                    if(!within(m2,2,3))continue;
                    auto m1=_mm256_movemask_epi8(_mm256_cmpgt_epi16(aw,_mm256_set1_epi16(1)));
                    if(!within(m1,4,8))continue;
                    auto m3=_mm256_movemask_epi8(_mm256_cmpgt_epi16(aw,_mm256_set1_epi16(3)));
                    if(!within(m3,1,2))continue;
                    uint64_t id=uint64_t(a)*states+i;
                    if(!seen.insert(id).second)continue;
                    narrow++;
                    Deck d;
                    _mm256_storeu_si256(reinterpret_cast<__m256i*>(d.data()),w);
                    for(int s:{1,-1}){
                        Deck indices;
                        for(int z=0;z<p;z++)indices[z]=4+clamp(s*d[z],-4,4);
                        vector<int> options;
                        for(int z=0;z<nprofiles;z++){
                            const auto& W=weights[z];
                            int sum=0;
                            for(int j=0;j<8;j++)sum+=W[j][indices[j]];
                            if(sum>68)continue;
                            sum=0;
                            for(int j=8;j<p;j++)sum+=W[j][indices[j]];
                            if(sum<=68)options.push_back(z);
                        }
                        if(options.empty())continue;
                        passed++;
                        cout<<"odd "<<a<<' '<<i<<' '<<s;
                        for(int z:options)cout<<' '<<z;
                        cout<<'\n';
                    }
                }
            }
        }
        cerr<<"key "<<start<<" tested "<<tested<<" narrow "<<narrow<<" directions "<<passed<<'\n';
    }
    cout<<"complete "<<tested<<' '<<narrow<<' '<<passed<<'\n';
}
