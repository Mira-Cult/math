/* Complete ternary-function checks for integer_forest_logsobolev.md.
 * Exact: Walsh numerators, full support, pairwise/forest recognition, counts.
 * Floating-point diagnostics only: entropy ratios and the reported maximizer.
 * Compile: cc -O3 scan_ternary_integer_forests.c -lm -o /tmp/fei-ternary-scan
 * Run: /tmp/fei-ternary-scan 4
 * Parameter range 1..4; n=4 enumerates all 3^16 truth tables.
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
int forest(int *a,int n){
 int par[6];for(int i=0;i<n;i++)par[i]=i;
 for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
  long r=a[0]*a[(1<<i)|(1<<j)],d=a[1<<i]*a[1<<j];
  for(int s=0;s<(1<<n);s++)if(!(s&(1<<i))&&!(s&(1<<j))){
   if((long)a[s]*a[s|(1<<i)|(1<<j)]*d != (long)a[s|(1<<i)]*a[s|(1<<j)]*r)return 0;
  }
  if(r!=d){int u=i,v=j;while(par[u]!=u)u=par[u];while(par[v]!=v)v=par[v];if(u==v)return 0;par[u]=v;}
 }
 return 1;
}
int main(int argc,char **argv){
 int n=argc>1?atoi(argv[1]):4; if(n<1||n>4){fprintf(stderr,"n must be between 1 and 4\n");return 2;} int N=1<<n;uint64_t cases=1;for(int i=0;i<N;i++)cases*=3;
 int bits[64];for(int s=0;s<N;s++)bits[s]=__builtin_popcount(s);
 double lg[4097];for(int i=1;i<=4096;i++)lg[i]=log2(i);
 uint64_t ct=0;double best=0,bestnorm=0;uint64_t bestid=0,bestnormid=0;int maxodd=0;
 for(uint64_t k=0;k<cases;k++){
  int a[64];uint64_t t=k;for(int j=0;j<N;j++){a[j]=t%3-1;t/=3;}
  for(int h=1;h<N;h*=2)for(int i=0;i<N;i+=2*h)for(int j=0;j<h;j++){int u=a[i+j],v=a[i+j+h];a[i+j]=u+v;a[i+j+h]=u-v;}
  int ok=1;for(int j=0;j<N;j++){if(!a[j]){ok=0;break;}if(a[j]<0)a[j]=-a[j];}
  if(!ok||!forest(a,n))continue;
  ct++;double h=0,ii=0,z=0;for(int s=0;s<N;s++){double w=a[s]*a[s];h+=w*(2*n-lg[a[s]*a[s]]);ii+=bits[s]*w;z+=w;int q=a[s];while(q%2==0)q/=2;if(q>maxodd)maxodd=q;}
  if(ii && h/ii>best){best=h/ii;bestid=k;}
  double hn=h-z*(2*n-log2(z));if(ii && hn/ii>bestnorm){bestnorm=hn/ii;bestnormid=k;}
 }
 printf("n %d cases %llu forests %llu maxodd %d best_raw %.17g id %llu best_norm %.17g id %llu\n",n,(unsigned long long)cases,(unsigned long long)ct,maxodd,best,(unsigned long long)bestid,bestnorm,(unsigned long long)bestnormid);
}
