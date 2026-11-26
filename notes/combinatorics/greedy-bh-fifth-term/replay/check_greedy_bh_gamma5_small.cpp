// Exact finite validation from forbidden signed coefficient budgets; C++17.
#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
using namespace std;
using I=long long;
struct Replay{
 int h; I g[4],cap; vector<bool> forbidden;
 Replay(int h):h(h),g{1,h+1,I(h)*h+h+1,I(h)*h*((h+3)/2)+(3*h+2)/2},
    cap(I(h)*g[3]+1),forbidden(cap+1){}
 void rec(int i,int pos,int neg,I s){
    if(i==4){
       if(s<=g[3])return;
       const int a=max<I>(1,(s+cap-1)/cap);
       const int b=min<I>(neg+1,s/(g[3]+1));
       for(int r=a;r<=b;r++)if(s%r==0)forbidden[s/r]=true;
       return;
    }
    for(int d=-neg;d<=pos;d++)
       rec(i+1,pos-max(d,0),neg+min(d,0),s+d*g[i]);
 }
 I solve(){rec(0,h,h-1,0);I x=g[3]+1;while(x<=cap&&forbidden[x])x++;assert(x<=cap);return x;}
};
I formula(int h){
 I x=h;
 I p[6]{5*x*x*x+8*x*x+7*x+6,5*x*x*x+7*x*x+7*x+9,4*x*x*x+10*x*x+6*x+4,
         7*x*x*x+5*x*x+9*x+3,6*x*x*x+6*x*x+8*x+8,6*x*x*x+6*x*x+8*x+6};
 assert((2*x*x*x*x+p[h%6])%6==0);
 return (2*x*x*x*x+p[h%6])/6;
}
int main(int argc,char**argv){
 int n=argc>1?stoi(argv[1]):59;
 for(int h=1;h<=n;h++){
    I x=Replay(h).solve(), p=formula(h);
    cout<<h<<' '<<x<<' '<<p<<(x==p?"":" EXCEPTION")<<endl;
 }
}
