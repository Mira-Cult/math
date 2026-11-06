/* Independent finite literal audit: a centered, bit-packed two-way tape.
 * No compiler or register semantics. The input is a canonical beeper-v1 table
 * already accepted by shared/machine.py; this reader checks its emitted order.
 * Host bounds limit this audit, not the mathematical machine. */
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

typedef struct { int write, delta, target; } Row;
static void fail(const char *s) { fprintf(stderr,"%s\n",s); exit(1); }
static void *allocate(size_t n,size_t width) {
    if (width && n>SIZE_MAX/width) fail("audit allocation overflow");
    void *p=calloc(n,width); if(!p) fail("audit allocation failed"); return p;
}
static uint64_t number(const char *s) {
    if(!*s || *s=='-') fail("invalid audit bound");
    errno=0; char *end; unsigned long long v=strtoull(s,&end,10);
    if(errno || *end) fail("invalid audit bound");
    return (uint64_t)v;
}
static void header(FILE *f,const char *key,char *value) {
    char line[256],got[64],extra;
    if(!fgets(line,sizeof(line),f) ||
       sscanf(line,"#! %63s %63s %c",got,value,&extra)!=2 || strcmp(got,key))
        fail("noncanonical header");
}

int main(int argc,char **argv) {
    if(argc<3 || argc>5) fail("usage: literal_bitset TABLE LIMIT [EVENTS] [STOP_STATE]");
    FILE *f=fopen(argv[1],"r"); if(!f) fail("cannot read table");
    char value[64];
    header(f,"format",value); if(strcmp(value,"beeper-v1")) fail("format");
    header(f,"states",value); uint64_t wide_n=number(value);
    if(!wide_n || wide_n>INT_MAX/2) fail("audit state inventory bound");
    int n=(int)wide_n;
    header(f,"start",value); uint64_t initial=number(value);
    header(f,"beep",value); uint64_t marked=number(value);
    if(initial>=wide_n || marked>=wide_n) fail("distinguished state");
    header(f,"blank",value); if(strcmp(value,"0")) fail("blank");
    header(f,"head",value); if(strcmp(value,"0")) fail("initial head");
    Row *rows=allocate(2*(size_t)n,sizeof(Row));
    char line[256];
    for(int s=0;s<n;s++) for(int bit=0;bit<2;bit++) {
        int q,b,w,t; char direction,extra;
        if(!fgets(line,sizeof(line),f) ||
           sscanf(line,"%d %d %d %c %d %c",&q,&b,&w,&direction,&t,&extra)!=5 ||
           q!=s || b!=bit || (w!=0 && w!=1) ||
           (direction!='L' && direction!='R') || t<0 || t>=n)
            fail("noncanonical or invalid row");
        rows[2*s+bit]=(Row){w,direction=='L'?-1:1,t};
    }
    if(fgets(line,sizeof(line),f)) fail("trailing table data");
    fclose(f);
    uint64_t limit=number(argv[2]),wanted=argc>3?number(argv[3]):0;
    if(limit>INT64_MAX/4) fail("audit transition bound too large");
    int stop=-1;
    if(argc>4 && strcmp(argv[4],"-1")) {
        uint64_t v=number(argv[4]); if(v>=wide_n) fail("stop state"); stop=(int)v;
    }
    size_t words=128;
    uint64_t *tape=allocate(words,sizeof(uint64_t));
    int64_t origin=-4096,head=0;
    int state=(int)initial;
    uint64_t step=0,*events=allocate(16,sizeof(uint64_t));
    size_t event_count=0,event_capacity=16;
    while(step<limit && state!=stop) {
        int64_t coordinate=head-origin;
        if(coordinate<0 || (uint64_t)coordinate>=64*(uint64_t)words) {
            if(words>SIZE_MAX/(2*sizeof(uint64_t)) || words>INT64_MAX/256)
                fail("audit tape bound exceeded");
            size_t larger=words*2,offset=(larger-words)/2;
            uint64_t *grown=allocate(larger,sizeof(uint64_t));
            memcpy(grown+offset,tape,words*sizeof(uint64_t)); free(tape);
            tape=grown;origin-=INT64_C(64)*(int64_t)offset;words=larger;
            coordinate=head-origin;
            if(coordinate<0 || (uint64_t)coordinate>=64*(uint64_t)words)
                fail("tape growth invariant");
        }
        size_t word=(size_t)(coordinate/64);
        uint64_t mask=UINT64_C(1)<<((unsigned)coordinate&63);
        int bit=(tape[word]&mask)!=0;
        Row r=rows[2*state+bit];
        if(state==(int)marked) {
            if(event_count==event_capacity) {
                if(event_capacity>SIZE_MAX/(2*sizeof(uint64_t))) fail("audit event bound exceeded");
                size_t larger=event_capacity*2;
                uint64_t *grown=allocate(larger,sizeof(uint64_t));
                memcpy(grown,events,event_count*sizeof(uint64_t));free(events);
                events=grown;event_capacity=larger;
            }
            events[event_count++]=step+1;
        }
        if(r.write)tape[word]|=mask;else tape[word]&=~mask;
        head+=r.delta;state=r.target;step++;
        if(wanted && event_count>=wanted) break;
    }
    printf("{\"steps\":%" PRIu64 ",\"state\":%d,\"head\":%" PRId64 ",\"beeps\":[",step,state,head);
    for(size_t i=0;i<event_count;i++)printf("%s%" PRIu64,i?",":"",events[i]);
    printf("],\"ones\":["); int comma=0;
    for(size_t word=0;word<words;word++) for(unsigned bit=0;bit<64;bit++)
        if((tape[word]>>bit)&1) {
            printf("%s%" PRId64,comma?",":"",origin+INT64_C(64)*(int64_t)word+bit);comma=1;
        }
    printf("]}\n");
    free(rows);free(tape);free(events);return 0;
}
