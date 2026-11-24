// Independent exhaustive integer verifier: M=280, A=109 completed after three deletions.
// Input: total A B C center_row(0=none,1=B,2=C) K, followed by K
// labelled histogram rows with multiplicities, then K+5 integer dual coefficients.
// This implementation imports neither the Python enumerator nor its columns.
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
void check(bool p){if(!p)throw std::runtime_error("invalid grid certificate or arithmetic overflow");}
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
 int total,A,B,C,center,K;std::cin>>total>>A>>B>>C>>center>>K;
 check(bool(std::cin)&&total==280&&A==109&&A+B+C==total&&(B>=86&&B<=109)&&center>=0&&center<=2&&K>0&&K<=30);
 if(center==0)check(B%3==0&&C%3==0);else check((center==1?B:C)%3!=0);
 std::vector<Row> hs(K);std::vector<I> mult(K);I count=0;
 for(int i=0;i<K;++i){for(int&x:hs[i])std::cin>>x;std::cin>>mult[i];check(bool(std::cin)&&mult[i]>0&&hs[i][0]+hs[i][1]+hs[i][2]==109&&hs[i][1]<=hs[i][2]&&mod(hs[i][1]-hs[i][2])==0);count+=mult[i];}
 check(count==364);std::vector<Big> dual(K+5);for(Big &v:dual)v=read_big();
 std::string extra;check(!(std::cin>>extra));
 auto bs=rows(B,center==1),cs=rows(C,center==2);
 I admissible=0,raw=I(K)*bs.size()*cs.size();Big minimum=-1;
 std::set<std::array<I,6>> columns;
 for(int t=0;t<K;++t)for(const Row&b:bs)for(const Row&c:cs){const Row&h=hs[t];bool valid=true;
  for(int alpha=0;alpha<3&&valid;++alpha)for(int r=0;r<3;++r)
   if(h[r]+b[mod(r-alpha)]+c[mod(r-2*alpha)]>109){valid=false;break;}
  if(!valid)continue;
  I cross=0;for(int i=0;i<3;++i)for(int j=0;j<3;++j)cross+=I(h[i])*b[j]*c[mod(-i-j)];
  std::array<I,5> values={square(b),cube(b),square(c),cube(c),cross};
  Big slack=dual[t];for(int j=0;j<5;++j)slack=add(slack,mul(dual[K+j],values[j]));
  check(slack>=0);if(minimum<0||slack<minimum)minimum=slack;++admissible;
  columns.insert({t,values[0],values[1],values[2],values[3],values[4]});
 }
 std::array<I,5> moments={moment2(B),moment3(B),moment2(C),moment3(C),121*I(A)*B*C};
 Big target=0;for(int t=0;t<K;++t)target=add(target,mul(dual[t],mult[t]));
 for(int j=0;j<5;++j)target=add(target,mul(dual[K+j],moments[j]));
 check(target<0&&admissible>0);
 std::cout<<"{\"status\":\"PASS\",\"target_total\":"<<total<<",\"anchor\":"<<A<<",\"B\":"<<B<<",\"C\":"<<C
  <<",\"hprofile_classes\":"<<K<<",\"center_row\":"<<center<<",\"raw_labelled_grids\":"<<raw
  <<",\"admissible_grids\":"<<admissible<<",\"distinct_columns\":"<<columns.size()
  <<",\"minimum_slack\":"<<decimal(minimum)<<",\"target_value\":"<<decimal(target)<<"}\n";
}
