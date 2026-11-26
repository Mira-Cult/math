#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
using namespace std;
int main(){for(int h=1;h<60;++h){
 int H=h+1,B=h*H+1,K=(h+3)/2,R=h/2,C=K*B-(K-1)*H+R;
 int L=max(C+1,(h*h*h*(h+4)+7)/8), U=h*C+1;
 vector<int> diff(U-L+2);
 for(int r=1;r<=h&&r*L<=h*C;++r)
 for(int c=-(h-r);c<=h;++c)
 for(int b=-(h-r+min(c,0));b<=h-max(c,0);++b)
 for(int a=-(h-r+min(c,0)+min(b,0));a<=h-max(c,0)-max(b,0);++a){
    int P=h-max(c,0)-max(b,0)-max(a,0);
    int N=h-r+min(c,0)+min(b,0)+min(a,0);
    int base=c*C+b*B+a*H;
    if(base+P<r*L || base-N>r*U)continue;
    int l=max(r*L,base-N),u=min(r*U,base+P);
    l=(l+r-1)/r;u/=r;
    if(l<=u){++diff[l-L];--diff[u-L+1];}
 }
 int h6=h%6,k=h/6; constexpr int off[6][4]={{0,0,0,1},{0,1,0,2},{1,1,0,1},{2,0,1,3},{3,0,1,2},{3,1,1,5}};
 int f=(4*k+off[h6][0])*C+(k+off[h6][1])*B+(k+off[h6][2])*H+k*(h6%2?5:1)+off[h6][3];
 int acc=0;bool hit=false;for(int x=L;x<=U;++x)if((acc+=diff[x-L])==0){
   hit=true;assert(h==4 ? x==153 && f==172 : x==f);cout<<h<<" "<<x<<" "<<f<<" "<<(x==f?"OK":"EXCEPTION")<<"\n";break;}
 assert(hit);
}}
