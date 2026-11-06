/* Independent bit-packed literal bounded executor. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct {int w,d,q,m,set;} Row;
static void fail(const char *s){fprintf(stderr,"%s\n",s);exit(1);}
int main(int argc,char **argv){
 if(argc!=3)fail("table and limit required");FILE*f=fopen(argv[1],"r");if(!f)fail("open failed");
 char line[1024],key[64];int states=0,start=0,beep=-1;Row *table=NULL;
 while(fgets(line,sizeof line,f)){
  if(!strncmp(line,"#!",2)){int n;if(sscanf(line+2,"%63s %d",key,&n)==2){if(!strcmp(key,"states"))states=n;else if(!strcmp(key,"start"))start=n;else if(!strcmp(key,"beep"))beep=n;}continue;}
  int q,b,w,t,m=0;char d;int n=sscanf(line,"%d %d %d %c %d %d",&q,&b,&w,&d,&t,&m);if(n<0)continue;
  if(n!=5&&n!=6)fail("bad row");if(q<0||q>=states||b<0||b>1||w<0||w>1||t<0||t>=states||(d!='L'&&d!='R'))fail("invalid row");
  if(!table){table=calloc((size_t)states*2,sizeof(Row));if(!table)fail("allocation");}if(table[2*q+b].set)fail("duplicate row");table[2*q+b]=(Row){w,d=='R'?1:-1,t,m,1};
 }
 fclose(f);if(!table)fail("empty table");for(int i=0;i<states*2;i++)if(!table[i].set)fail("missing row");
 uint64_t limit=strtoull(argv[2],NULL,10),*tape=calloc(64,sizeof(uint64_t));size_t words=64;int q=start,first=1;int64_t head=0,min=0,max=0;if(!tape)fail("allocation");
 printf("{\"events\":[");
 for(uint64_t step=1;step<=limit;step++){
  uint64_t index=head>=0?2*(uint64_t)head:2*(uint64_t)(-head)-1;size_t word=(size_t)(index/64);unsigned bit=(unsigned)(index%64);
  if(word>=words){size_t old=words;while(word>=words)words*=2;uint64_t*next=realloc(tape,words*sizeof(uint64_t));if(!next)fail("allocation");tape=next;memset(tape+old,0,(words-old)*sizeof(uint64_t));}
  int read=(int)((tape[word]>>bit)&1);Row r=table[2*q+read];int event=r.m||(beep>=0&&q==beep);
  if(r.w)tape[word]|=UINT64_C(1)<<bit;else tape[word]&=~(UINT64_C(1)<<bit);head+=r.d;q=r.q;if(head<min)min=head;if(head>max)max=head;
  if(event){if(!first)putchar(',');first=0;printf("%" PRIu64,step);}
 }
 printf("],\"steps\":%" PRIu64 ",\"state\":%d,\"head\":%" PRId64 ",\"ones\":[",limit,q,head);first=1;
 for(int64_t p=min;p<=max;p++){uint64_t index=p>=0?2*(uint64_t)p:2*(uint64_t)(-p)-1;if(index/64<words&&((tape[index/64]>>(index%64))&1)){if(!first)putchar(',');first=0;printf("%" PRId64,p);}}
 puts("]}");free(tape);free(table);return 0;
}
