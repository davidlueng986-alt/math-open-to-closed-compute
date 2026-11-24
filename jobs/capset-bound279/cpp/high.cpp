// Independent exhaustive integer verifier: M=280, A=110/111/112.
// Input: total A B C center_row(0=none,1=B,2=C) kind(0=single,1=ordinary,2=antipodal),
// then dual coefficients in the hardcoded h-class order below.
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
 int total,A,B,C,center,kind;std::cin>>total>>A>>B>>C>>center>>kind;
 check(bool(std::cin)&&total==280&&A>=110&&A<=112&&A+B+C==total&&B>=C&&B<=109&&C>=0);
 check(center>=0&&center<=2);
 if(center==0)check(B%3==0&&C%3==0);else check((center==1?B:C)%3!=0);
 std::vector<Row> hs;std::vector<I> mult;
 if(A==110&&kind==1){hs={{20,45,45},{21,44,45},{22,43,45},{22,44,44},{38,36,36},{39,35,36},{40,34,36},{40,35,35}};
  mult={2,18,18,18,38,144,63,63};}
 else if(A==110&&kind==2){hs={{20,45,45},{22,44,44},{38,36,36},{40,35,35}};mult={11,45,110,198};}
 else if(A==111&&kind==0){hs={{39,36,36},{40,35,36},{21,45,45},{22,44,45}};mult={110,198,11,45};}
 else if(A==112&&kind==0){hs={{40,36,36},{22,45,45}};mult={308,56};}
 else check(false);
 int K=hs.size();std::vector<Big> dual(K+5);for(Big &v:dual)v=read_big();
 std::string extra;check(!(std::cin>>extra));
 std::set<Row> fingerprints;
 for(Row r:{Row{22,45,45},Row{40,36,36}})
  for(int x=0;x<=2;++x)for(int y=0;y<=2-x;++y)for(int z=0;z<=2-x-y;++z){
   Row d={r[0]-x,r[1]-y,r[2]-z};std::sort(d.begin(),d.end());fingerprints.insert(d);}
 auto bs=rows(B,center==1),cs=rows(C,center==2);
 I admissible=0,raw=I(K)*bs.size()*cs.size();Big minimum=-1;
 std::set<std::array<I,6>> columns;
 for(int t=0;t<K;++t)for(const Row&b:bs)for(const Row&c:cs){const Row&h=hs[t];bool valid=true;
  for(int alpha=0;alpha<3&&valid;++alpha){Row sizes;
   for(int r=0;r<3;++r){Row cells={h[r],b[mod(r-alpha)],c[mod(r-2*alpha)]};sizes[r]=cells[0]+cells[1]+cells[2];
    if(sizes[r]>112){valid=false;break;}
    if(sizes[r]>=110){std::sort(cells.begin(),cells.end());if(!fingerprints.count(cells)){valid=false;break;}}}
   if(valid){std::sort(sizes.begin(),sizes.end());if(sizes[1]>=110)valid=false;}}
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
  <<",\"kind_code\":"<<kind<<",\"center_row\":"<<center<<",\"raw_labelled_grids\":"<<raw
  <<",\"admissible_grids\":"<<admissible<<",\"distinct_columns\":"<<columns.size()
  <<",\"minimum_slack\":"<<decimal(minimum)<<",\"target_value\":"<<decimal(target)<<"}\n";
}
