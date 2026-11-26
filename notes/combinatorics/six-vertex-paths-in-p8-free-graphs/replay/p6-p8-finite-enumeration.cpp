// Exact connected P8-free graph census by canonical augmentation; C++17.
// Graphs represented by bit rows; order <= 16 ensures 120-bit keys.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Key=unsigned __int128;
constexpr int MAX=16;
using Adj=array<int,MAX>;
struct KeyHash{ size_t operator()(Key x)const noexcept {
    auto mix=[](uint64_t a){a=(a^(a>>30))*0xbf58476d1ce4e5b9ULL;a=(a^(a>>27))*0x94d049bb133111ebULL;return a^(a>>31);};
    return mix(uint64_t(x))^mix(uint64_t(x>>64)+0x9e3779b97f4a7c15ULL);
}};
string keytext(Key x){if(!x)return "0";string s;while(x){s+=char('0'+x%10);x/=10;}reverse(s.begin(),s.end());return s;}
int bit(int i){return 1<<i;}
int pc(int x){return __builtin_popcount(unsigned(x));}
int first(int x){return __builtin_ctz(unsigned(x));}
Adj decode(Key k,int n){Adj G{};int e=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,e++)if(k>>e&1){G[i]|=bit(j);G[j]|=bit(i);}return G;}
struct Canon{
 const Adj& G;int n;
 using Col=array<int,MAX>;
 Key encode(Col c){int p[MAX];for(int i=0;i<n;i++)p[c[i]]=i;Key k=0;int e=0;
   for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,e++)if(G[p[i]]&bit(p[j]))k|=Key(1)<<e;
   return k;}
 Key refine(Col c,int colors){
  while(true){
    array<array<int,MAX+1>,MAX>s{};
    for(int i=0;i<n;i++){s[i][0]=c[i];for(int h=G[i];h;h&=h-1)s[i][1+c[first(h)]]++;}
    int order[MAX];iota(order,order+n,0);sort(order,order+n,[&](int a,int b){return s[a]<s[b];});
    Col d{};int z=0;for(int i=0;i<n;i++){if(i&&s[order[i]]!=s[order[i-1]])z++;d[order[i]]=z;}
    c=d;if(z+1==colors)break;colors=z+1;
  }
  if(colors==n)return encode(c);
  array<int,MAX> size{};for(int i=0;i<n;i++)size[c[i]]++;
  int cell=-1;for(int j=0;j<colors;j++)if(size[j]>1&&(cell<0||size[j]<size[cell]))cell=j;
  Key best=~Key(0);int used=0;
  for(int i=0;i<n;i++)if(c[i]==cell){
    bool twin=false;for(int h=used;h;h&=h-1){int j=first(h);if(!((G[i]^G[j])&~(bit(i)|bit(j)))){twin=true;break;}}
    if(twin)continue;
    used|=bit(i);Col d=c;d[i]=colors;best=min(best,refine(d,colors+1));
  }
  return best;
 }
 Key key(){return refine({},1);}
};
vector<int> bads(const Adj&G,int n){
 int V=(1<<n)-1;vector<int>E(V+1,0);vector<int>B(n,0);
 for(int S=1;S<=V;S++){
   int q=pc(S);if(q>7)continue;
   if(q==1)E[S]=S;
   else for(int h=S;h;h&=h-1){int i=first(h);if(E[S^bit(i)]&G[i])E[S]|=bit(i);}
   if(q==7)for(int h=E[S];h;h&=h-1){int a=first(h);B[a]|=bit(a);}
 }
 // Process each unordered pair of disjoint support masks with size sum 7.
 for(int S=1;S<V;S++)if(E[S]&&pc(S)<=3){
   int U=V^S;for(int T=U;T;T=(T-1)&U)if(pc(T)==7-pc(S)&&E[T]){
     for(int h=E[S];h;h&=h-1)B[first(h)]|=E[T];
     for(int h=E[T];h;h&=h-1)B[first(h)]|=E[S];
   }
 }
 return B;
}
int count6(const Adj&G,int n){
 int V=(1<<n)-1;vector<array<int,MAX>> D(V+1);int sum=0;
 for(int S=1;S<=V;S++){
   int j=pc(S);if(j>6)continue;
   for(int h=S;h;h&=h-1){int i=first(h);int c=(j==1);
     for(int T=(S^bit(i))&G[i];T;T&=T-1)c+=D[S^bit(i)][first(T)];
     D[S][i]=c;if(j==6)sum+=c;}
 }
 assert(sum%2==0);return sum/2;
}
int main(int argc,char**argv){
 int last=argc>1?atoi(argv[1]):10;assert(last>=1&&last<=MAX);
 unordered_set<Key,KeyHash> C{0};array<int,MAX+1> exact{},opt{};
 const int base[]={0,1,1,2,6,21,112,853};
 for(int n=1;n<=last;n++){
   int best=-1,num=0;Key rep=0;
   for(Key k:C){int x=count6(decode(k,n),n);if(x>best){best=x;num=0;rep=k;}
     if(x==best){num++;rep=min(rep,k);}}
   exact[n]=best;opt[n]=best;
   for(int a=1;a<n;a++)opt[n]=max(opt[n],exact[a]+opt[n-a]);
   cout<<n<<" connected "<<C.size()<<" maximum "<<best<<" extremals "<<num<<" rep-key "<<keytext(rep)<<" arbitrary "<<opt[n]<<endl;
   if(n<=7)assert(C.size()==unsigned(base[n]));
   if(n==last)break;
   unordered_set<Key,KeyHash> next;
   for(Key k:C){Adj G=decode(k,n);vector<int>B=bads(G,n);int V=(1<<n)-1;
     for(int S=1;S<=V;S++){
       bool good=true;for(int h=S;h;h&=h-1)if(B[first(h)]&S){good=false;break;}
       if(!good)continue;
       Adj H=G;H[n]=S;for(int h=S;h;h&=h-1)H[first(h)]|=bit(n);
       next.insert(Canon{H,n+1}.key());
     }
   }
   C=move(next);
 }
}
