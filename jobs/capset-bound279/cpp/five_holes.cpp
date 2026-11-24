// Independent exhaustive verification of the finite 45-cap graph lemma.
// Compile: g++ -O2 -std=c++17 verify_three_deletion.cpp -o verify_three_deletion
// Run: ./verify_three_deletion cap45_codes.txt
// Input codes use little-endian base-three coordinates. No optimizer is used.
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <vector>

int plus3(int x,int y){int out=0,p=1; for(int k=0;k<5;k++){out+=((x%3+y%3)%3)*p; x/=3;y/=3;p*=3;}return out;}
int minus3(int x,int y){int out=0,p=1; for(int k=0;k<5;k++){out+=((x%3-y%3+3)%3)*p; x/=3;y/=3;p*=3;}return out;}
int main(int argc,char**argv){
    if(argc!=2) return 2;
    std::ifstream in(argv[1]); std::vector<int> A;std::array<bool,243> has{};
    int x;while(in>>x){assert(x>=0&&x<243&&!has[x]);has[x]=true;A.push_back(x);}
    assert(A.size()==45);
    for(int i=0;i<45;i++)for(int j=i+1;j<45;j++)assert(!has[minus3(0,plus3(A[i],A[j]))]);
    std::array<long long,10> hist{};long long cases=0,six_subsets=0;
    for(int d=1;d<243;d++)for(int a:A){
        std::vector<int> V;
        for(int z=0;z<243;z++)if(has[z]&&has[minus3(z,d)]&&z!=a&&z!=plus3(a,d))V.push_back(z);
        assert(V.size()<=9);
        bool edge[9][9]{};
        for(int i=0;i<(int)V.size();i++)for(int j=i+1;j<(int)V.size();j++)
            edge[i][j]=edge[j][i]=has[plus3(a,minus3(V[i],V[j]))]||has[plus3(a,minus3(V[j],V[i]))];
        int alpha=0;
        // Unlike the Python recurrence, inspect pair conflicts directly for every subset.
        for(int mask=0;mask<(1<<(int)V.size());mask++){
            int n=__builtin_popcount((unsigned)mask);bool ok=true;
            for(int i=0;i<(int)V.size()&&ok;i++)if(mask&(1<<i))for(int j=i+1;j<(int)V.size();j++)
                if((mask&(1<<j))&&edge[i][j]){ok=false;break;}
            if(n==6){six_subsets++;assert(!ok);}
            if(ok&&n>alpha)alpha=n;
        }
        assert(alpha<=5);hist[alpha]++;cases++;
    }
    assert(cases==10890&&hist[0]==990&&hist[4]==5400&&hist[5]==4500);
    std::cout<<"{\"status\":\"EXACT_PASS\",\"cases\":"<<cases
             <<",\"all_six_subsets_checked\":"<<six_subsets
             <<",\"independence_number_histogram\":{\"0\":"<<hist[0]<<",\"4\":"<<hist[4]<<",\"5\":"<<hist[5]
             <<"},\"maximum_independence_number\":5}\n";
}
