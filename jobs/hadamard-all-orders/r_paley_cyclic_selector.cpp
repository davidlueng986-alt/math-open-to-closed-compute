#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <vector>

constexpr int n=23;
using Word=std::array<int,n>;
using Triple=std::array<int,3>;

int embed(int s){
    constexpr int power[4]={1,7,49,343};
    return (s>0?1:-1)*power[std::abs(s)-1];
}

bool cyclic(const Word& word){
    for(int d=1;d<=11;d++){
        int t=0;
        for(int i=0;i<n;i++){
            int x=word[i],y=word[(i+d)%n];
            t+=(x==y)-(x==-y);
        }
        if(t)return false;
    }
    return true;
}

int main(int argc,char**argv){
    bool three=argc>1;
    std::map<int,std::vector<Triple>> sums;
    for(int a=-4;a<=4;a++)if(a)
    for(int b=-4;b<=4;b++)if(b)
    for(int c=-4;c<=4;c++)if(c)
        sums[embed(a)+embed(b)+embed(c)].push_back({a,b,c});
    int count;std::cin>>count;
    uint64_t examined=0,actual=0;
    for(int z=0;z<count;z++){
        Word w;
        int id;std::cin>>id;
        for(int& v:w)std::cin>>v;
        assert(std::cin&&cyclic(w));
        auto save=[&](int distance){
            examined++;
            if(!cyclic(w))return;
            actual++;
            std::cout<<id<<' '<<distance;
            for(int v:w)std::cout<<' '<<v;
            std::cout<<'\n';
        };
        for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
            const int a=w[i],b=w[j];
            if(a!=b){
                if(a==-b){
                    for(int t=-4;t<=4;t++)if(t&&t!=a){
                        w[i]=t;w[j]=-t;
                        save(2);
                    }
                }else{
                    w[i]=b;w[j]=a;
                    save(2);
                }
                w[i]=a;w[j]=b;
            }
            if(!three)continue;
            for(int k=j+1;k<n;k++){
                const int c=w[k];
                const auto& todo=sums.at(embed(a)+embed(b)+embed(c));
                for(const auto& r:todo){
                    if(a==r[0]||b==r[1]||c==r[2])continue;
                    w[i]=r[0];w[j]=r[1];w[k]=r[2];
                    save(3);
                }
                w[i]=a;w[j]=b;w[k]=c;
            }
        }
    }
    std::cerr<<"sources "<<count<<" checked "<<examined<<" passed "<<actual<<std::endl;
}
