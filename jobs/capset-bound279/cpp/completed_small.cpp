// Independent exhaustive integer audit of the H-minus-four/five frontier branches.
// Input: A, B, number of deleted antipodal pairs, centroid_zero (0/1), 15 duals.
// No optimizer, saved columns, or discovery-program imports are used.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
using I=std::int64_t;
using Big=__int128_t;
using Row=std::array<int,3>;
void check(bool p){if(!p)throw std::runtime_error("invalid certificate or arithmetic overflow");}
Big add(Big a,Big b){Big c;check(!__builtin_add_overflow(a,b,&c));return c;}
Big mul(Big a,Big b){Big c;check(!__builtin_mul_overflow(a,b,&c));return c;}
Big read_big(){std::string s;std::cin>>s;check(bool(std::cin)&&!s.empty());bool neg=s[0]=='-';Big a=0;
 check(s.size()>std::size_t(neg));
 for(std::size_t i=neg;i<s.size();++i){check(s[i]>='0'&&s[i]<='9');a=add(mul(a,10),s[i]-'0');}
 return neg?mul(a,-1):a;}
std::string decimal(Big a){if(a==0)return "0";bool neg=a<0;if(neg)a=mul(a,-1);std::string s;
 while(a){s+=char('0'+a%10);a/=10;}if(neg)s+='-';std::reverse(s.begin(),s.end());return s;}
int mod(int a){return (a%3+3)%3;}
I square(const Row&r){I s=0;for(I x:r)s+=x*x;return s;}
I cube(const Row&r){I s=0;for(I x:r)s+=x*x*x;return s;}
I moment2(I n){return 364*n+121*n*(n-1);}
I moment3(I n){return 364*n+363*n*(n-1)+40*n*(n-1)*(n-2);}
std::vector<Row> rows(int n,bool centered){std::vector<Row> out;
 for(int x=0;x<=45;++x)for(int y=0;y<=45;++y){int z=n-x-y;
  if(z>=0&&z<=45&&(!centered||mod(y-z)==0))out.push_back({x,y,z});}return out;}
int main(){
 int M,A,B,k,zero,extra43,nk;std::cin>>M>>A>>B>>k>>zero>>extra43>>nk;
 std::vector<Row> known(nk);for(Row&p:known){for(int&x:p)std::cin>>x;std::sort(p.begin(),p.end());check(p[0]+p[1]+p[2]==M);}
 check(bool(std::cin)&&(A==107||A==108)&&B>=87&&B<=109&&k>=0&&k<=2&&(zero==0||zero==1));
 check((k==0)||(k==1&&zero==0)||(k==2&&zero==(A==108)));
 int C=M-A-B,D=112-A;int center=B%3?1:(C%3?2:0);
 std::array<Big,15> dual;for(Big&v:dual)v=read_big();std::string extra;check(!(std::cin>>extra));
 std::vector<std::array<int,4>> hs;
 const std::array<Row,2> complete={Row{22,45,45},Row{40,36,36}};
 for(int typ=0;typ<2;++typ)for(int d0=0;d0<=D;++d0)for(int d1=0;d1<=D-d0;++d1){
  int d2=D-d0-d1;
  if(k==1&&!(d0>=2||(d1>=1&&d2>=1)))continue;
  if(k==2){bool can=false;for(int z=0;z<=4;z+=2)can=can||(d0>=z&&d1>=(4-z)/2&&d2>=(4-z)/2);if(!can)continue;}
  Row h={complete[typ][0]-d0,complete[typ][1]-d1,complete[typ][2]-d2};
  if(h[1]<=h[2])hs.push_back({typ,h[0],h[1],h[2]});
 }
 std::sort(hs.begin(),hs.end());check(std::adjacent_find(hs.begin(),hs.end())==hs.end());
 auto bs=rows(B,center==1),cs=rows(C,center==2);
 I raw=I(hs.size())*bs.size()*cs.size(),valid=0;Big minimum=-1;
 std::set<std::array<I,6>> columns;
 for(std::size_t index=0;index<hs.size();++index){const auto&hh=hs[index];int typ=hh[0];Row h={hh[1],hh[2],hh[3]};
  for(const Row&b:bs)for(const Row&c:cs){bool good=true;
   for(int alpha=0;alpha<3&&good;++alpha){Row sums;for(int r=0;r<3;++r){
    Row pp={h[r],b[mod(r-alpha)],c[mod(r-2*alpha)]};int n=pp[0]+pp[1]+pp[2];sums[r]=n;
    if(n>109){good=false;break;}
    std::sort(pp.begin(),pp.end());
    const std::array<Row,6> forbid={Row{19,45,45},Row{20,44,45},Row{21,43,45},Row{21,44,44},Row{22,42,45},Row{22,43,44}};
    if(std::find(forbid.begin(),forbid.end(),pp)!=forbid.end()){good=false;break;}
    if(extra43&&pp==Row{23,43,43}){good=false;break;}
   }if(good){std::sort(sums.begin(),sums.end());if(std::find(known.begin(),known.end(),sums)!=known.end())good=false;}}
   if(!good)continue;
   I cross=0;for(int i=0;i<3;++i)for(int j=0;j<3;++j)cross+=I(h[i])*b[j]*c[mod(-i-j)];
   std::array<I,15> f={};f[typ]=1;f[2+typ]=h[0];f[4+typ]=I(h[0])*h[0];
   f[6]=I(h[0])*h[0]*h[0];f[7]=square(h);f[8]=cube(h);
   f[9]=square(b);f[10]=cube(b);f[11]=square(c);f[12]=cube(c);f[13]=cross;f[14]=mod(h[1]-h[2])==0;
   Big slack=0;for(int i=0;i<15;++i)slack=add(slack,mul(f[i],dual[i]));
   check(slack>=0);if(minimum<0||slack<minimum)minimum=slack;++valid;
   columns.insert({I(index),f[9],f[10],f[11],f[12],f[13]});
  }
 }
 const I e=112-2*D+2*k;
 const std::array<I,15> target={56,308,1232-11*D,12320-110*D,27104+2*D*D-475*D+18*k,492800+38*D*D-8728*D+144*k,
   13*I(A)*A*A+81*I(A)*A+27*A+81*e*(A+1),moment2(A),moment3(A),moment2(B),moment3(B),
   moment2(C),moment3(C),121*I(A)*B*C,zero?364:121};
 Big total=0;for(int i=0;i<15;++i)total=add(total,mul(target[i],dual[i]));check(total<0&&valid>0);
 std::cout<<"{\"status\":\"PASS\",\"target_total\":"<<M<<",\"A\":"<<A<<",\"B\":"<<B<<",\"C\":"<<C
  <<",\"deleted_antipodal_pairs\":"<<k<<",\"centroid_zero\":"<<zero<<",\"hprofile_count\":"<<hs.size()
  <<",\"raw_labelled_grids\":"<<raw<<",\"valid_labelled_grids\":"<<valid<<",\"distinct_columns\":"<<columns.size()
  <<",\"minimum_slack\":"<<decimal(minimum)<<",\"target_dot_dual\":"<<decimal(total)<<"}\n";
}

