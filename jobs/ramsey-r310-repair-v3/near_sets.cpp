#include <iostream>
#include <cstdint>
#include <cstdlib>
using namespace std;
using U=uint64_t;
U a[40]; int s[10],cap;
void go(int first,int k,int used,U m){
 if(k==10){cout<<used;for(int i:s)cout<<' '<<i;cout<<'\n';return;}
 for(int j=first;j<=40-(10-k);j++){
  int t=used+__builtin_popcountll(a[j]&m);
  if(t<=cap){s[k]=j;go(j+1,k+1,t,m|(1ULL<<j));}
 }
}
int main(int argc,char**argv){cap=atoi(argv[1]);char c;for(int i=0;i<40;i++)for(int j=0;j<40;j++){if(!(cin>>c)||(c!='0'&&c!='1'))return 2;if(c=='1')a[i]|=1ULL<<j;}go(0,0,0,0);}
