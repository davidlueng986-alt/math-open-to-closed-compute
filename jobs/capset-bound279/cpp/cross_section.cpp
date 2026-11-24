// Independent integer finite input for the (43,43,c>=22) completion theorem.
// g++ -O2 -std=c++17 verify_cross_section_capacity.cpp -o verify_cross_section_capacity
// ./verify_cross_section_capacity cap18_A2_normalized_codes.txt
// Coordinates use z = 81*s + u, u in F_3^4 encoded little-endian.
#include <algorithm>
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using Map4=std::array<int,81>;
using Vec=std::vector<int>;
int add4[81][81],neg4[81],add5[243][243],neg5[243];
std::array<std::array<int,4>,81>digit4;
std::array<std::array<int,5>,243>digit5;

int addcode(int x,int y,int dim){int s=0,p=1;for(int k=0;k<dim;k++){s+=((x%3+y%3)%3)*p;x/=3;y/=3;p*=3;}return s;}
bool is_cap(const Vec&A,int dim){std::set<int>S(A.begin(),A.end());if(S.size()!=A.size())return false;for(size_t i=0;i<A.size();i++)for(size_t j=i+1;j<A.size();j++){int s=addcode(A[i],A[j],dim);if(S.count(addcode(s,s,dim)))return false;}return true;}
std::vector<Map4> isomorphisms(const Vec&K,const Vec&Dest){
 std::array<bool,81>has{};for(int z:Dest)has[z]=true;
 std::set<int>src(K.begin(),K.end());assert(src.count(0)&&src.count(1)&&src.count(3)&&src.count(9)&&src.count(27));
 std::vector<Map4>result;
 for(int o:Dest)for(int p:Dest)if(p!=o)for(int q:Dest)if(q!=o&&q!=p)for(int r:Dest)if(r!=o&&r!=p&&r!=q)for(int s:Dest)if(s!=o&&s!=p&&s!=q&&s!=r){
  int cols[4]={add4[p][neg4[o]],add4[q][neg4[o]],add4[r][neg4[o]],add4[s][neg4[o]]};int mult[4][3];
  for(int k=0;k<4;k++){mult[k][0]=0;mult[k][1]=cols[k];mult[k][2]=neg4[cols[k]];}
  bool ok=true;for(int z:K){int y=o;for(int k=0;k<4;k++)y=add4[y][mult[k][digit4[z][k]]];if(!has[y]){ok=false;break;}}
  if(!ok)continue;Map4 map;std::set<int>images;
  for(int z=0;z<81;z++){int y=o;for(int k=0;k<4;k++)y=add4[y][mult[k][digit4[z][k]]];map[z]=y;images.insert(y);}
  if(images.size()==81)result.push_back(map);
 }
 return result;
}
int cube855_count(const Vec&K){
 int cubes=0;
 for(int f=1;f<81;f++){
  int first=0;for(int j=0;j<4;j++)if(digit4[f][j]){first=digit4[f][j];break;}if(first!=1)continue;
  std::array<Vec,3>parts;
  for(int z:K){int t=0;for(int j=0;j<4;j++)t+=digit4[f][j]*digit4[z][j];parts[t%3].push_back(z);}
  std::array<int,3>sizes={(int)parts[0].size(),(int)parts[1].size(),(int)parts[2].size()};std::sort(sizes.begin(),sizes.end());
  if(sizes!=std::array<int,3>{5,5,8})continue;
  Vec V;for(auto&part:parts)if(part.size()==8)V=part;
  std::set<int>setV(V.begin(),V.end());bool cube=false;int origin=V[0];
  for(int i=1;i<8&&!cube;i++)for(int j=i+1;j<8&&!cube;j++)for(int k=j+1;k<8&&!cube;k++){
   int e[3]={add4[V[i]][neg4[origin]],add4[V[j]][neg4[origin]],add4[V[k]][neg4[origin]]};std::set<int>image;
   for(int mask=0;mask<8;mask++){int z=origin;for(int t=0;t<3;t++)if(mask&(1<<t))z=add4[z][e[t]];image.insert(z);}
   if(image==setV)cube=true;
  }
  if(cube)cubes++;
 }
 return cubes;
}
int main(int argc,char**argv){
 assert(argc==2);
 for(int x=0;x<81;x++){int w=x;for(int k=0;k<4;k++){digit4[x][k]=w%3;w/=3;}neg4[x]=addcode(x,x,4);for(int y=0;y<81;y++)add4[x][y]=addcode(x,y,4);}
 for(int x=0;x<243;x++){int w=x;for(int k=0;k<5;k++){digit5[x][k]=w%3;w/=3;}neg5[x]=addcode(x,x,5);for(int y=0;y<243;y++)add5[x][y]=addcode(x,y,5);}
 std::ifstream in(argv[1]);Vec A,K,L;int s,u;while(in>>s>>u){assert(s>=0&&s<3&&u>=0&&u<81);A.push_back(81*s+u);if(s==1)K.push_back(u);if(s==2)L.push_back(u);}
 std::sort(A.begin(),A.end());assert(A.size()==45&&K.size()==18&&L.size()==18&&is_cap(A,5));
 assert(cube855_count(K)==1&&cube855_count(L)==1);
 // Identify the selected section's 882A2 class without choosing an unverified chart.
 int dirs189=0,dirsA2=0,dirsA1=0;
 for(int f=1;f<243;f++){
  int pivot=-1;for(int j=0;j<5;j++)if(digit5[f][j]){pivot=j;break;}if(digit5[f][pivot]!=1)continue;
  std::array<Vec,3>parts;
  for(int z:A){int t=0;for(int j=0;j<5;j++)t+=digit5[f][j]*digit5[z][j];parts[t%3].push_back(z);}
  std::array<int,3>sizes={(int)parts[0].size(),(int)parts[1].size(),(int)parts[2].size()};std::sort(sizes.begin(),sizes.end());if(sizes!=std::array<int,3>{9,18,18})continue;
  dirs189++;int kind=-1;
  for(auto&part:parts)if(part.size()==18){Vec projected;for(int z:part){int v=0,p=1;for(int j=0;j<5;j++)if(j!=pivot){v+=digit5[z][j]*p;p*=3;}projected.push_back(v);}int k=cube855_count(projected);assert(k==0||k==1);if(kind<0)kind=k;else assert(kind==k);}
  if(kind==1)dirsA2++;else dirsA1++;
 }
 assert(dirs189==55&&dirsA2==45&&dirsA1==10);
 const auto G=isomorphisms(K,K),Pmaps=isomorphisms(K,L);assert(G.size()==16&&Pmaps.size()==16);const auto&P=Pmaps[0];
 // Explicit orientation reversal of the normalized 45-cap, used in completeness.
 int reversers=0;
 for(auto&g:Pmaps)for(int v=0;v<81;v++){Vec image;for(int z:A){int t=z/81,x=z%81;int sh=t==1?0:t==2?v:neg4[v];image.push_back(81*((3-t)%3)+add4[g[x]][sh]);}std::sort(image.begin(),image.end());if(image==A)reversers++;}
 assert(reversers==8);
 std::set<Vec>extensions;
 std::map<Vec,Map4>partners;
 for(auto&g:G)for(int v=0;v<81;v++){
  Vec E;for(int z:A){int t=z/81,x=z%81;int sh=t==1?0:t==2?v:neg4[v];E.push_back(81*t+add4[g[x]][sh]);}std::sort(E.begin(),E.end());extensions.insert(E);
  Vec Btop;for(int x:L)Btop.push_back(add4[g[x]][v]);std::sort(Btop.begin(),Btop.end());
  Map4 Q;for(int x=0;x<81;x++)Q[x]=add4[g[P[x]]][v];partners.emplace(Btop,Q);
 }
 assert(extensions.size()==162&&partners.size()==162);
 std::array<std::set<Vec>,2>allB;std::array<std::map<int,int>,2>capacity_hist,n4hist;std::array<int,2>reflections{};
 for(int orientation=0;orientation<2;orientation++)for(auto&entry:partners)for(auto&E:extensions){
  const auto&Q=entry.second;Vec B;for(int z:E){int t=z/81;if(orientation)t=(3-t)%3;B.push_back(81*t+Q[z%81]);}std::sort(B.begin(),B.end());assert(is_cap(B,5));assert(allB[orientation].insert(B).second);
  std::array<int,243>repr{};for(int a:A)for(int b:B)repr[add5[a][b]]++;
  int reflection_sum=-1;for(int z=0;z<243;z++)if(repr[z]==45){assert(reflection_sum<0);reflection_sum=z;}
  if(reflection_sum>=0){
   Vec reflected;for(int a:A)reflected.push_back(add5[reflection_sum][neg5[a]]);std::sort(reflected.begin(),reflected.end());assert(reflected==B);
   std::map<int,int>rh;for(int r:repr)rh[r]++;assert((rh==std::map<int,int>{{0,22},{9,220},{45,1}}));reflections[orientation]++;
  }
  Vec costs;for(int z=0;z<243;z++)if(repr[z]<=4)costs.push_back(repr[z]);n4hist[orientation][costs.size()]++;std::sort(costs.begin(),costs.end());
  Vec degreeA,degreeB;
  for(int a:A){int degree=0;for(int b:B)if(repr[add5[a][b]]<=4)degree++;degreeA.push_back(degree);}
  for(int b:B){int degree=0;for(int a:A)if(repr[add5[a][b]]<=4)degree++;degreeB.push_back(degree);}
  std::sort(degreeA.begin(),degreeA.end(),std::greater<int>());std::sort(degreeB.begin(),degreeB.end(),std::greater<int>());
  int budget=degreeA[0]+degreeA[1]+degreeB[0]+degreeB[1];int total=0,upper=0;
  for(int c:costs){if(total+c>budget)break;total+=c;upper++;}
  if(reflection_sum<0){assert(upper<=(orientation?9:10));capacity_hist[orientation][upper]++;}else assert(upper==22);
 }
 assert(allB[0].size()==26244&&allB[1].size()==26244&&reflections[0]==81&&reflections[1]==0);
 std::cout<<"{\"status\":\"EXACT_PASS\",\"normalized_45cap_size\":45,\"aut18_count\":16,\"isom18_count\":16,\"orientation_reversers\":8,\"A2_directions\":45,\"A1_directions\":10,\"extensions\":162,\"partners\":162,\"completed_pairs_per_orientation\":26244,\"horizontal_reflections\":81,\"diagonal_reflections\":0,\"nonreflection_capacity_histograms\":[";
 for(int orientation=0;orientation<2;orientation++){if(orientation)std::cout<<",";std::cout<<"{";bool first=true;for(auto[k,v]:capacity_hist[orientation]){if(!first)std::cout<<",";first=false;std::cout<<"\""<<k<<"\":"<<v;}std::cout<<"}";}
 std::cout<<"]}\n";
}
