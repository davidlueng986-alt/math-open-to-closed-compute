#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
namespace {
using U=std::uint64_t;
using Mask=std::array<U,3>;
struct Site{int index=-1;U syndrome=0;};
struct Record{U key; Mask sites;};
std::array<std::array<Site,23>,13> from;
std::array<std::array<unsigned,13>,13> common{};
std::array<U,7> observed{},zeros{};
std::array<int,6> row{};
std::vector<Record> four,six,eight;
int goal;
void display(const Mask& a){
    for(int i=0;i<130;++i)if(a[i/64]>>(i%64)&1U)std::cout<<" "<<i;
}
void scan_col(int step,unsigned used,U z,Mask m,int first_y=-1){
    if(step==goal){
       ++observed[goal];
       if(!z){
          {std::cout<<"hit "<<2*goal;display(m);std::cout<<"\n";}
          ++zeros[goal];
       }
       if(goal==2)four.push_back({z,m});
       if(goal==3)six.push_back({z,m});
       if(goal==4)eight.push_back({z,m});
       return;
    }
    int j=row[step],k=row[(step+1)%goal];
    unsigned allowed=common[j][k]&~used;
    for(unsigned h=allowed;h;h&=h-1){
        int y=std::countr_zero(h);
        if(goal==2&&step==1&&y<=first_y)continue;
        auto a=from[j][y],b=from[k][y];
        auto n=m;
        n[a.index/64]|=U(1)<<(a.index%64);
        n[b.index/64]|=U(1)<<(b.index%64);
        scan_col(step+1,used|(1U<<y),z^a.syndrome^b.syndrome,n,step?first_y:y);
    }
}
void scan_row(int step,int first,unsigned used){
    if(step==goal){
        if(goal>2&&row[1]>=row[goal-1])return;
        if(common[row[goal-1]][first])scan_col(0,0,0,{});
        return;
    }
    for(int r=first+1;r<13;++r)if(!(used>>r&1)&&common[row[step-1]][r]){
        row[step]=r;
        scan_row(step+1,first,used|(1U<<r));
    }
}
bool disjoint(const Mask&a,const Mask&b){for(int i=0;i<3;++i)if(a[i]&b[i])return false;return true;}
void join(const std::vector<Record>& a,const std::vector<Record>& b,int len,bool same){
    std::unordered_map<U,std::vector<std::size_t>> table;
    for(std::size_t i=0;i<b.size();++i)table[b[i].key].push_back(i);
    U count=0;
    for(std::size_t i=0;i<a.size();++i){
        auto u=table.find(a[i].key);
        if(u==table.end())continue;
        for(auto j:u->second)if((!same||i<j)&&disjoint(a[i].sites,b[j].sites)){
            {
                std::cout<<"union hit "<<len;
                Mask s=a[i].sites;
                for(int k=0;k<3;++k)s[k]|=b[j].sites[k];
                display(s);std::cout<<"\n";
            }
            ++count;
        }
    }
    std::cout<<"union "<<len<<" hits (by decomposition) "<<count<<"\n";
}
}
int main(){
    for(int i=0;i<130;++i){
        int x,y;U z;std::cin>>x>>y>>z;
        if(!std::cin || x<0 || x>=13 || y<0 || y>=23 || from[x][y].index!=-1)return 1;
        from[x][y]={i,z};
    }
    for(int a=0;a<13;++a)for(int b=0;b<13;++b)if(a!=b)
        for(int y=0;y<23;++y)if(from[a][y].index>=0&&from[b][y].index>=0)
            common[a][b]|=1U<<y;
    for(goal=2;goal<=6;++goal){
        for(int a=0;a<13;++a){row[0]=a;scan_row(1,a,1U<<a);}
        std::cout<<"cycles "<<2*goal<<" "<<observed[goal]<<" compatible "<<zeros[goal]<<std::endl;
    }
    join(four,four,8,true);
    join(four,six,10,false);
    join(four,eight,12,false);
    join(six,six,12,true);
    std::unordered_map<U,std::vector<int>> pos;
    for (int h=0;h<int(four.size());++h) pos[four[h].key].push_back(h);
    U count=0;
    for (int i=0;i<int(four.size());++i)for(int j=i+1;j<int(four.size());++j) {
        if(!disjoint(four[i].sites,four[j].sites)) continue;
        auto it=pos.find(four[i].key^four[j].key);
        if(it==pos.end()) continue;
        for(int k:it->second)if(k>j&&disjoint(four[i].sites,four[k].sites)&&disjoint(four[j].sites,four[k].sites)){
            Mask m{};
            for (int h=0;h<3;++h)m[h]=four[i].sites[h]|four[j].sites[h]|four[k].sites[h];
            ++count;
            std::cout<<"union hit 12";display(m);std::cout<<"\n";
        }
    }
    std::cout<<"union three-four hits "<<count<<"\n";
}
