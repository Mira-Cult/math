// Deterministic discovery and exact final acceptance of finite prime-line squares.
// The separate verifier imports none of this search implementation.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;
using i64 = std::int64_t;
using u128 = __uint128_t;

static void need(bool ok, const char* what) {
    if (!ok) throw std::runtime_error(what);
}
static constexpr u32 MAX_ORDER = 1999;
static constexpr u64 BASE_SEED = 0x535544455f465231ULL;
static constexpr u64 STEP = 0x9e3779b97f4a7c15ULL;

struct RNG {
    u64 state;
    u64 next() {
        u64 z = (state += STEP);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        return z ^ (z >> 31);
    }
    u32 below(u32 bound) { need(bound > 0, "positive random index bound"); return next() % bound; }
};

struct Primes {
    std::vector<unsigned char> flags;
    std::vector<u32> pool;
    u64 probable_calls = 0, exact_calls = 0, divisions = 0;
    Primes() {
        u32 count = MAX_ORDER*MAX_ORDER;
        u32 bound = 20*(count+1);
        for (;;) {
            flags.assign(bound+1, 1); flags[0] = flags[1] = 0;
            for (u32 p=2; u64(p)*p<=bound; ++p) if (flags[p])
                for (u32 q=p*p; q<=bound; q+=p) flags[q]=0;
            pool.clear(); pool.reserve(count);
            for (u32 p=3; p<=bound && pool.size()<count; p+=2)
                if (flags[p]) pool.push_back(p);
            if (pool.size()==count) break;
            need(bound < 1000000000, "sieve search bound"); bound*=2;
        }
    }
    static u64 power(u64 a, u64 b, u64 m) {
        u64 result=1;
        while (b) { if (b&1) result=u128(result)*a%m; a=u128(a)*a%m; b>>=1; }
        return result;
    }
    bool probable(u64 x) {
        ++probable_calls;
        if (x<flags.size()) return flags[x];
        if (!(x&1)) return false;
        for (u32 p: {3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97})
            if (x%p==0) return false;
        u64 d=x-1; u32 s=0; while (!(d&1)) { d>>=1; ++s; }
        for (u64 base: {2ULL,3ULL}) {
            u64 a=power(base,d,x);
            if (a==1 || a==x-1) continue;
            bool ok=false;
            for (u32 r=1;r<s;++r) { a=u128(a)*a%x; if (a==x-1) { ok=true; break; } }
            if (!ok) return false;
        }
        return true; // Discovery only: final acceptance calls exact().
    }
    bool exact(u64 x) {
        ++exact_calls;
        if (x<flags.size()) return flags[x];
        if (!(x&1)) return false;
        for (u32 p: pool) {
            if (u64(p)*p>x) return true;
            ++divisions;
            if (x%p==0) return false;
        }
        throw std::runtime_error("trial-prime pool insufficient");
    }
};

struct Square {
    u32 n;
    std::vector<u32> a;
    std::vector<i64> row,col;
    std::array<i64,2> diag{};
    std::vector<std::pair<u32,u32>> swaps;
    Square(u32 order,const std::vector<u32>& pool,u64 seed):n(order),a(pool.begin(),pool.begin()+order*order) {
        RNG rng{seed};
        for (u32 i=a.size()-1;i>0;--i) std::swap(a[i],a[rng.below(i+1)]);
        recompute();
    }
    bool off(u32 r,u32 c) const { return r!=c && r+c!=n-1; }
    void recompute() {
        row.assign(n,0); col.assign(n,0); diag={0,0};
        for (u32 r=0;r<n;++r) for (u32 c=0;c<n;++c) {
            u32 v=a[r*n+c]; row[r]+=v;col[c]+=v;
            if (r==c) diag[0]+=v;
            if (r+c==n-1) diag[1]+=v;
        }
    }
    void exchange(u32 a0,u32 b0) {
        need(a0<a.size() && b0<a.size() && a0!=b0,"distinct valid swap indices");
        u32 ar=a0/n,ac=a0%n,br=b0/n,bc=b0%n;
        i64 d=i64(a[b0])-a[a0];
        row[ar]+=d;row[br]-=d;col[ac]+=d;col[bc]-=d;
        if(ar==ac)diag[0]+=d;
        if(br==bc)diag[0]-=d;
        if(ar+ac==n-1)diag[1]+=d;
        if(br+bc==n-1)diag[1]-=d;
        std::swap(a[a0],a[b0]);swaps.emplace_back(a0,b0);
    }
    bool exact_check(Primes& primes) {
        auto rr=row,cc=col;auto dd=diag;recompute();
        need(row==rr && col==cc && diag==dd,"incremental sums equal fresh sums");
        for (i64 v:row) if (!primes.exact(v)) return false;
        for (i64 v:col) if (!primes.exact(v)) return false;
        for (i64 v:diag) if (!primes.exact(v)) return false;
        return true;
    }
};

static bool repair_diagonal(Square& s,Primes& p,RNG& rng,u32 which) {
    if (p.probable(s.diag[which])) return true;
    for (u32 trial=0;trial<100000;++trial) {
        u32 r=rng.below(s.n); if(r==s.n/2)continue;
        u32 c=which?s.n-1-r:r, a=r*s.n+c,b=rng.below(s.n*s.n);
        if (!s.off(b/s.n,b%s.n))continue;
        i64 next=s.diag[which]+i64(s.a[b])-s.a[a];
        if (p.probable(next)) {s.exchange(a,b);return true;}
    }
    return false;
}

static bool repair_axis(Square& s,Primes& p,RNG& rng,bool columns) {
    auto& sums=columns?s.col:s.row;
    std::vector<u32> bad;std::vector<int> where(s.n,-1);
    for(u32 i=0;i<s.n;++i)if(!p.probable(sums[i])) {where[i]=bad.size();bad.push_back(i);}
    auto remove=[&](u32 v) {
        need(where[v]>=0,"remove an actually bad line");
        u32 pos=where[v],last=bad.back();bad[pos]=last;where[last]=pos;bad.pop_back();where[v]=-1;
    };
    while(!bad.empty()) {
        u32 selected=bad.back();bool repaired=false;
        for(u32 trial=0;trial<100000;++trial) {
            u32 other=bad.size()>1?bad[rng.below(bad.size()-1)]:rng.below(s.n);
            if(other==selected)continue;
            u32 shared=rng.below(s.n);
            u32 ar=columns?shared:selected,ac=columns?selected:shared;
            u32 br=columns?shared:other,bc=columns?other:shared;
            if(!s.off(ar,ac)||!s.off(br,bc))continue;
            u32 a=ar*s.n+ac,b=br*s.n+bc;i64 d=i64(s.a[b])-s.a[a];
            if(!p.probable(sums[selected]+d))continue;
            bool other_prime=p.probable(sums[other]-d);
            if(where[other]<0 && !other_prime)continue;
            s.exchange(a,b);remove(selected);
            if(where[other]>=0 && other_prime)remove(other);
            repaired=true;break;
        }
        if(!repaired)return false;
    }
    return true;
}

static void put32(std::ostream& out,u32 x) {for(int j=0;j<4;++j)out.put(char((x>>(8*j))&255));}
static void put64(std::ostream& out,u64 x) {for(int j=0;j<8;++j)out.put(char((x>>(8*j))&255));}
static void record(std::ostream& out,u32 n,u64 seed,const std::array<u32,5>& counts,const Square& s) {
    put32(out,n);put64(out,seed);for(u32 count:counts)put32(out,count);
    for(auto [a,b]:s.swaps) {put32(out,a);put32(out,b);}need(bool(out),"certificate output write");
}

static void generate(u32 maximum,const std::string& path) {
    need(maximum>=1 && maximum<=MAX_ORDER && maximum%2,"bounded odd maximum");
    Primes p;std::ofstream out(path,std::ios::binary);need(bool(out),"open certificate output");
    out.write("SUDEFR01",8);put32(out,1);put32(out,maximum);put32(out,(maximum+1)/2);
    auto start=std::chrono::steady_clock::now();
    for(u32 n=1;n<=maximum;n+=2) {
        bool success=false;u64 old_prob=p.probable_calls,old_div=p.divisions;
        for(u32 attempt=0;attempt<1000;++attempt) {
            u64 seed=BASE_SEED^n^(u64(attempt)*STEP);Square s(n,p.pool,seed);RNG rng{seed};
            // Reproduce precisely the RNG state after the initial permutation.
            for(u32 i=n*n-1;i>0;--i)rng.below(i+1);
            std::array<u32,5> counts{};
            if(n==3) {
                std::vector<u32> target(p.pool.begin(),p.pool.begin()+9);
                do {
                    std::array<u64,8> sums{};
                    for(u32 r=0;r<3;++r)for(u32 c=0;c<3;++c) {
                        u32 v=target[3*r+c];sums[r]+=v;sums[3+c]+=v;
                        if(r==c)sums[6]+=v;
                        if(r+c==2)sums[7]+=v;
                    }
                    if(std::all_of(sums.begin(),sums.end(),[&](u64 x){return p.exact(x);}))break;
                } while(std::next_permutation(target.begin(),target.end()));
                for(u32 i=0;i<9;++i)if(s.a[i]!=target[i]) {
                    auto j=std::find(s.a.begin()+i+1,s.a.end(),target[i]);need(j!=s.a.end(),"three witness permutation");
                    s.exchange(i,j-s.a.begin());
                }
                counts[0]=s.swaps.size();
            } else if(n>1) {
                if(!repair_diagonal(s,p,rng,0))continue;
                counts[1]=s.swaps.size();
                if(!repair_diagonal(s,p,rng,1))continue;
                counts[2]=s.swaps.size()-counts[1];
                if(!repair_axis(s,p,rng,false))continue;
                counts[3]=s.swaps.size()-counts[1]-counts[2];
                if(!repair_axis(s,p,rng,true))continue;
                counts[4]=s.swaps.size()-counts[1]-counts[2]-counts[3];
            }
            if(!s.exact_check(p))continue;
            record(out,n,seed,counts,s);out.flush();success=true;
            double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
            std::cout<<"{\"n\":"<<n<<",\"attempt\":"<<attempt<<",\"seed\":"<<seed
                     <<",\"swaps\":"<<s.swaps.size()<<",\"probable_calls\":"<<(p.probable_calls-old_prob)
                     <<",\"exact_divisions\":"<<(p.divisions-old_div)<<",\"seconds\":"<<seconds<<"}\n"<<std::flush;
            break;
        }
        need(success,"first missing odd order: restart budget exhausted");
    }
}

int main(int argc,char** argv) {
    try {
        need(argc==4 && std::string(argv[1])=="generate","usage: generate ODD_MAX CERTIFICATE");
        std::string raw=argv[2];
        need(!raw.empty() && raw.size()<=4,"canonical bounded maximum");
        u32 maximum=0;
        for(char c:raw) {
            need(c>='0' && c<='9',"decimal maximum");
            maximum=10*maximum+u32(c-'0');
        }
        need(std::to_string(maximum)==raw,"no padded maximum");
        generate(maximum,argv[3]);
    } catch(const std::exception& ex) {std::cerr<<"FAIL: "<<ex.what()<<"\n";return 2;}
    return 0;
}
