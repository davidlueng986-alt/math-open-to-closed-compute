#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using I=__int128_t;
using Row=std::array<int,3>;
std::string dec(I x){if(x==0)return "0";bool n=x<0;if(n)x=-x;std::string s;while(x){s.push_back('0'+x%10);x/=10;}if(n)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
Row sorted(Row p){std::sort(p.begin(),p.end());return p;}
bool completion(Row p,int n,bool extra43){
 p=sorted(p);if(p[0]+p[1]+p[2]!=n)return false;
 assert(n>=107&&n<=109);
 const std::vector<Row> f={{n-90,45,45},{n-89,44,45},{n-88,43,45},{n-88,44,44},{n-87,42,45},{n-87,43,44}};
 return std::find(f.begin(),f.end(),p)!=f.end()||(extra43&&n>=108&&p==Row{n-86,43,43});
}
std::vector<Row> rows(int n,bool centered){std::vector<Row> out;for(int x=0;x<=45;x++)for(int y=0;y<=45;y++){int z=n-x-y;if(z<0||z>45)continue;if(centered&&(y-z)%3)continue;out.push_back({x,y,z});}return out;}
I s2(Row p){I s=0;for(int x:p)s+=I(x)*x;return s;}
I s3(Row p){I s=0;for(int x:p)s+=I(x)*x*x;return s;}
// Input per case: total A B C extra43 ng nk nc; globally excluded completed
// sizes; previously excluded global profiles; (size,context profile) pairs;
// eight integer dual coefficients. All grids retain all row/level labels.
int main(){int M,A,B,C,extra,ng,nk,nc;
 while(std::cin>>M>>A>>B>>C>>extra>>ng>>nk>>nc){
  assert(A+B+C==M&&M>=278&&M<=281&&A<=109&&A>=B&&B>=C);
  std::set<int> global;for(int i=0,n;i<ng;i++){std::cin>>n;global.insert(n);}
  std::set<Row> known;for(int i=0;i<nk;i++){Row p;for(int&x:p)std::cin>>x;assert(p[0]+p[1]+p[2]==M);known.insert(sorted(p));}
  std::map<int,std::set<Row>> contexts;for(int i=0,n;i<nc;i++){Row p;std::cin>>n;for(int&x:p)std::cin>>x;assert(p[0]+p[1]+p[2]==M);contexts[n].insert(sorted(p));}
  std::array<I,8> y;for(I&x:y){long long t;std::cin>>t;x=t;}
  auto banned=[&](Row cells,Row parent){int n=cells[0]+cells[1]+cells[2];if(n<107||n>109)return false;bool active=global.count(n);auto it=contexts.find(n);if(it!=contexts.end()&&it->second.count(sorted(parent)))active=true;return active&&completion(cells,n,extra);};
  bool center[3]={false,false,false};int ns[3]={A,B,C},count=0;
  for(int i=0;i<3&&count<2;i++)if(ns[i]%3){center[i]=true;count++;}
  auto ar=rows(A,center[0]),br=rows(B,center[1]),cr=rows(C,center[2]);
  long long raw=0,valid=0;I minimum=I(1)<<120;Row parent{A,B,C};
  for(Row a:ar){if(banned(a,parent))continue;
   for(Row b:br){if(banned(b,parent))continue;
    for(Row c:cr){if(banned(c,parent))continue;raw++;bool ok=true;
     for(int slope=0;slope<3&&ok;slope++){
      Row sums;std::array<Row,3> cells;
      for(int r=0;r<3;r++){cells[r]={a[r],b[(r-slope+3)%3],c[(r-2*slope+6)%3]};sums[r]=cells[r][0]+cells[r][1]+cells[r][2];if(sums[r]>109){ok=false;break;}}
      if(!ok)break;if(known.count(sorted(sums))){ok=false;break;}
      for(Row p:cells)if(banned(p,sums)){ok=false;break;}
     }
     if(!ok)continue;valid++;
     I cross=0;for(int i=0;i<3;i++)for(int j=0;j<3;j++)cross+=I(a[i])*b[j]*c[(6-i-j)%3];
     std::array<I,8> v={1,s2(a),s3(a),s2(b),s3(b),s2(c),s3(c),cross};
     I q=0;for(int k=0;k<8;k++)q+=y[k]*v[k];minimum=std::min(minimum,q);
     if(q<0){std::cerr<<"NEGATIVE_GRID "<<dec(q)<<"\n";return 2;}
    }
   }
  }
  std::array<I,8> t={364,121*I(A)*A+243*A,40*I(A)*A*A+243*I(A)*A+81*A,121*I(B)*B+243*B,40*I(B)*B*B+243*I(B)*B+81*B,121*I(C)*C+243*C,40*I(C)*C*C+243*I(C)*C+81*C,121*I(A)*B*C};
  I dot=0;for(int k=0;k<8;k++)dot+=t[k]*y[k];if(dot>=0||valid==0)return 3;
  std::cout<<"{\"profile\":["<<A<<","<<B<<","<<C<<"],\"target_total\":"<<M<<",\"raw_fully_labelled\":"<<raw<<",\"valid_fully_labelled\":"<<valid<<",\"minimum_slack\":\""<<dec(minimum)<<"\",\"target_dot_dual\":\""<<dec(dot)<<"\",\"status\":\"PASS\"}"<<std::endl;
 }
}
