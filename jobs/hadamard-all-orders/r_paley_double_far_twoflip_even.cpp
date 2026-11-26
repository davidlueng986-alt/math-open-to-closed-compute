#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
constexpr int p=16,half=14,n=1<<half;
using Row=array<int,p>;
using Key=uint64_t;
vector<Row> deck(const array<Row,28>& A,int start){
    vector<Row> R(n);
    for(int i=start;i<start+half;i++)for(int j=0;j<p;j++)R[0][j]-=A[i][j];
    for(unsigned m=1;m<R.size();m++){
        int q=__builtin_ctz(m);
        R[m]=R[m&(m-1)];
        for(int j=0;j<p;j++)R[m][j]+=2*A[start+q][j];
    }
    return R;
}
Key key(const Row& r,int start,int k){
    Key a=0;
    for(int j=0;j<3;j++)a|=Key(k*r[start+j]+256)<<(9*j);
    return a;
}
int main(){
    array<Row,24> A;
    array<Row,28> B;
    for(auto& r:A)for(int& v:r)cin>>v;
    for(auto& r:B)for(int& v:r)cin>>v;
    assert(cin);
    auto l=deck(B,0),r=deck(B,14);
    uint64_t visits=0;
    int valid=0;
    for(int start:{0,3,6,9,12}){
        vector<pair<Key,unsigned>> index;
        for(unsigned k=0;k<r.size();k++)index.emplace_back(key(r[k],start,1),k);
        sort(index.begin(),index.end());
        for(unsigned a=1;a<l.size();a+=2){
            Key raw=key(l[a],start,-1);
            for(int phase=0;phase<8;phase++){
                Key left=raw;
                for(int i=0;i<3;i++){
                    if(phase>>i&1)left+=2ULL<<(9*i);
                    else left-=2ULL<<(9*i);
                }
                for(auto p=lower_bound(index.begin(),index.end(),pair{left,0U});p!=index.end()&&p->first==left;++p){
                    visits++;
                    int f=0,g=0;
                    for(int j=0;j<8;j++){
                       f+=abs(l[a][j]+r[p->second][j])==2;
                       g+=abs(l[a][8+j]+r[p->second][8+j])==2;
                    }
                    if(f>=6&&g>=6){
                        valid++;
                        cout<<"hit "<<a<<" "<<p->second<<" "<<f<<" "<<g<<"\n";
                    }
                }
            }
        }
    }
    cout<<"final visits "<<visits<<" valid "<<valid<<"\n";
}
