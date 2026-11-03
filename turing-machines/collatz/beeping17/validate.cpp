// Independent direct simulator; checks the literal compact transition table.
// g++ -O3 -std=c++17 validate.cpp -o validate && ./validate
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
const string TEXT="1RL0RB_1LC1RB_0LK0LD_1RE1LD_0RF0RB_0LG0LG_1LH1LG_0RA0RI_1RJ1RI_1RF1RF_0RA1LK_0LM0LM_0LN1LM_1RO1LN_0RA0RP_0RQ1RP_1RL1RQ";
struct Tr{int w,d,q;};
array<array<Tr,2>,17> parse(){array<array<Tr,2>,17>a{};int p=0;for(int s=0;s<17;s++){for(int r=0;r<2;r++){a[s][r]={TEXT[p]-'0',TEXT[p+1]=='R'?1:-1,TEXT[p+2]-'A'};p+=3;}if(s<16&&TEXT[p++]!='_')throw runtime_error("parse");}return a;}
auto T=parse();
const int OFF=2048,SIZE=40000;
vector<uint8_t> conf(int n,int v,int K){
 if(n<1||v<1||v>K||n+2>=OFF||K+2>=SIZE-OFF)throw runtime_error("bounds");
 vector<uint8_t>a(SIZE,0);for(int i=-n;i<-1;i++)a[OFF+i]=1;
 for(int i=0;i<K;i++)a[OFF+i]=(i!=v-1);return a;
}
void step(vector<uint8_t>&t,int &h,int&s,uint64_t &beeps){
 if(s==14)++beeps;Tr e=T[s][t[h]];t[h]=e.w;h+=e.d;s=e.q;
 if(h<1||h>=SIZE-1)throw runtime_error("tape capacity exceeded");
}
uint64_t checked_steps=0;int cases=0;
void test(int n,int v,int K){
 auto t=conf(n,v,K);int h=OFF,s=0;uint64_t b=0,steps=0;
 do{step(t,h,s,b);if(++steps>10000000)throw runtime_error("macro timeout");}while(s!=0);
 int nn=v==1?n+1:n, vv=v==1?n+1:(v%2?(3*v+1)/2:v/2),kk=max(K,vv);
 if(h!=OFF||t!=conf(nn,vv,kk)||b!=(v==1?n:0)){
  cerr<<"FAILED n="<<n<<" v="<<v<<" K="<<K<<" h="<<h-OFF<<" beeps="<<b<<endl;
  throw runtime_error("macro mismatch");
 }
 checked_steps+=steps;cases++;
}
int main(){try{
 for(int n=1;n<=32;n++)for(int v=1;v<=128;v++)for(int K:{v,v+1,v+7,2*v,512})test(n,v,K);
 mt19937 rng(20261023);for(int j=0;j<256;j++){int n=1+rng()%512,v=1+rng()%1000;test(n,v,v+rng()%2048);}
 cout<<"Macro cases: "<<cases<<"; transitions: "<<checked_steps<<"; all passed\n";
 // End-to-end: compare each completed macro to an independent arithmetic model.
 vector<uint8_t> tape(SIZE,0);int h=OFF,s=0,n=1,v=1,K=1;uint64_t beeps=0,last=0,macros=0;
 uint64_t expected_beeps=0;const uint64_t LIMIT=200000000;
 for(uint64_t t=1;t<=LIMIT;t++){
  step(tape,h,s,beeps);
  if(s==0){
   if(v==1){expected_beeps+=n;++n;v=n;}else v=v%2?(3*v+1)/2:v/2;
   K=max(K,v);++macros;
   if(h!=OFF||tape!=conf(n,v,K)||beeps!=expected_beeps)throw runtime_error("blank trace mismatch");
   last=t;
  }
 }
 cout<<"Blank trace steps: "<<LIMIT<<"; checked macros: "<<macros<<"; completed inputs: "<<n-1<<"; beeps: "<<beeps<<"; current input: "<<n<<"; last checkpoint value: "<<v<<"; last checkpoint time: "<<last<<"\n";
}catch(const exception&e){cerr<<e.what()<<'\n';return 1;}}
