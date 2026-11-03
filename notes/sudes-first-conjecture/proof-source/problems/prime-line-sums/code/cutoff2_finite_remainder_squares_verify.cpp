// Standalone exact certificate replay. No search code or probable-prime test.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using U32 = std::uint32_t;
using U64 = std::uint64_t;
static_assert(sizeof(U32)==4 && sizeof(U64)==8);

static void insist(bool condition,const char* message) {
    if(!condition)throw std::runtime_error(message);
}
static U32 read32(std::istream& input) {
    U32 value=0;
    for(unsigned j=0;j<4;++j) {
        int byte=input.get();insist(byte>=0,"truncated 32-bit field");
        value|=U32(byte)<<(8*j);
    }
    return value;
}
static U64 read64(std::istream& input) {
    U64 low=read32(input),high=read32(input);
    return low+(high<<32);
}
static U64 next_word(U64& state) {
    state+=UINT64_C(0x9e3779b97f4a7c15);
    U64 word=state;
    word=(word^(word>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    word=(word^(word>>27))*UINT64_C(0x94d049bb133111eb);
    return word^(word>>31);
}
static bool ordinary(U32 n,U32 position) {
    U32 r=position/n,c=position%n;
    return r!=c && r+c!=n-1;
}

struct ExactPrimeSource {
    U32 limit;
    std::vector<unsigned char> odd;
    std::vector<U32> pool,trial;
    U64 tests=0,divisions=0,upper_sum;
    explicit ExactPrimeSource(U32 maximum) {
        U32 required=maximum*maximum;
        limit=20*(required+1);
        for(;;) {
            odd.assign(limit/2+1,1);odd[0]=0;
            for(U32 p=3;U64(p)*p<=limit;p+=2)if(odd[p/2])
                for(U32 multiple=p*p;multiple<=limit;multiple+=2*p)odd[multiple/2]=0;
            pool.clear();pool.reserve(required);
            for(U32 candidate=3;candidate<=limit && pool.size()<required;candidate+=2)
                if(odd[candidate/2])pool.push_back(candidate);
            if(pool.size()==required)break;
            insist(limit<1000000000,"finite sieve bound exceeded");limit*=2;
        }
        insist(!pool.empty() && pool[0]==3,"prescribed pool begins with 3");
        upper_sum=U64(maximum)*pool.back();
        bool sufficient=false;
        // At maximum=1 the sieve alone covers every admissible line sum.
        if(upper_sum<=limit)sufficient=true;
        for(U32 p:pool) {
            trial.push_back(p);
            if(U64(p)*p>upper_sum){sufficient=true;break;}
        }
        insist(sufficient,"exact trial-prime list reaches square-root bound");
    }
    bool prime(U64 value) {
        ++tests;
        insist(value<=upper_sum,"line sum inside certified trial-prime range");
        if(value==2)return true;
        if(value<2 || value%2==0)return false;
        if(value<=limit)return odd[value/2];
        for(U32 divisor:trial) {
            if(U64(divisor)*divisor>value)return true;
            ++divisions;
            if(value%divisor==0)return false;
        }
        throw std::runtime_error("trial-division coverage failed");
    }
};

static U32 parse_maximum(const std::string& text) {
    insist(!text.empty() && text.size()<=4,"canonical finite maximum");
    U32 result=0;
    for(char c:text) {
        insist(c>='0' && c<='9',"maximum is a decimal integer");
        result=10*result+U32(c-'0');
    }
    insist(std::to_string(result)==text && result>=1 && result<=1999 && result%2==1,
           "positive odd maximum at most 1999");
    return result;
}

static void verify(const std::string& name,U32 maximum) {
    std::ifstream input(name,std::ios::binary);insist(bool(input),"open certificate");
    std::array<char,8> magic{};input.read(magic.data(),magic.size());
    insist(std::string(magic.data(),magic.size())=="SUDEFR01","fixed certificate format");
    insist(read32(input)==1 && read32(input)==maximum && read32(input)==(maximum+1)/2,
           "complete contiguous odd-order header");
    ExactPrimeSource primes(maximum);
    U64 total_swaps=0,total_cells=0,max_line=0,min_line=std::numeric_limits<U64>::max();
    U64 all_line_total=0;
    std::cout<<"{\"orders\":[";
    for(U32 expected=1;expected<=maximum;expected+=2) {
        U32 n=read32(input);U64 seed=read64(input);
        insist(n==expected,"every consecutive odd order appears exactly once");
        std::array<U32,5> counts{};U64 swaps=0;
        for(U32& count:counts){count=read32(input);swaps+=count;}
        if(n==1)insist(swaps==0,"singleton certificate has no swaps");
        else if(n==3)insist(counts[0]<=8 && swaps==counts[0],
                           "order-three direct-permutation recipe");
        else insist(counts[0]==0 && counts[1]<=1 && counts[2]<=1
                    && counts[3]<=n && counts[4]<=n,"bounded staged swap counts");
        U32 size=n*n;
        std::vector<U32> ranks(size);
        for(U32 j=0;j<size;++j)ranks[j]=j;
        U64 state=seed;
        for(U32 j=size-1;j>0;--j) {
            U32 chosen=next_word(state)%(j+1);
            std::swap(ranks[j],ranks[chosen]);
        }
        for(U32 phase=0;phase<5;++phase)for(U32 step=0;step<counts[phase];++step) {
            U32 a=read32(input),b=read32(input);
            insist(a<size && b<size && a!=b,"distinct bounded swap positions");
            U32 ar=a/n,ac=a%n,br=b/n,bc=b%n;
            if(phase==1 || phase==2) {
                bool designated=phase==1?ar==ac:ar+ac==n-1;
                insist(designated && ar!=n/2 && ordinary(n,b),"one designated diagonal cell and one ordinary cell");
            } else if(phase==3) {
                insist(ac==bc && ar!=br && ordinary(n,a) && ordinary(n,b),
                       "row repair preserves columns and both diagonals");
            } else if(phase==4) {
                insist(ar==br && ac!=bc && ordinary(n,a) && ordinary(n,b),
                       "column repair preserves rows and both diagonals");
            }
            std::swap(ranks[a],ranks[b]);
        }
        std::vector<unsigned char> seen(size,0);
        std::vector<U64> sums(2*n+2,0);
        for(U32 position=0;position<size;++position) {
            U32 rank=ranks[position];
            insist(rank<size && !seen[rank],"exact permutation of prescribed prime ranks");
            seen[rank]=1;
            U32 value=primes.pool[rank],r=position/n,c=position%n;
            sums[r]+=value;sums[n+c]+=value;
            if(r==c)sums[2*n]+=value;
            if(r+c==n-1)sums[2*n+1]+=value;
        }
        U64 local_min=*std::min_element(sums.begin(),sums.end());
        U64 local_max=*std::max_element(sums.begin(),sums.end());
        U64 local_total=0;
        for(U64 value:sums) {
            insist(primes.prime(value),"a freshly recomputed required line sum is composite");
            local_total+=value;
        }
        insist(std::all_of(seen.begin(),seen.end(),[](unsigned char flag){return flag==1;}),
               "every prescribed prime rank used once");
        total_swaps+=swaps;total_cells+=size;all_line_total+=local_total;
        max_line=std::max(max_line,local_max);min_line=std::min(min_line,local_min);
        if(n!=1)std::cout<<',';
        std::cout<<"{\"n\":"<<n<<",\"seed\":"<<seed<<",\"swaps\":"<<swaps
                 <<",\"min_line\":"<<local_min<<",\"max_line\":"<<local_max
                 <<",\"all_line_total\":"<<local_total<<'}';
    }
    insist(input.peek()==std::char_traits<char>::eof(),"no extra or trailing certificate bytes");
    insist(!input.bad(),"certificate read completed without IO error");
    std::cout<<"],\"status\":\"PASS_EXACT_CONTIGUOUS_PRIME_SQUARES\",\"first_order\":1"
             <<",\"last_order\":"<<maximum<<",\"order_count\":"<<(maximum+1)/2
             <<",\"swaps\":"<<total_swaps<<",\"cells\":"<<total_cells
             <<",\"line_count\":"<<primes.tests<<",\"exact_trial_divisions\":"<<primes.divisions
             <<",\"sieve_limit\":"<<primes.limit<<",\"largest_pool_prime\":"<<primes.pool.back()
             <<",\"min_line\":"<<min_line<<",\"max_line\":"<<max_line
             <<",\"all_line_total\":"<<all_line_total<<"}\n";
}

int main(int argc,char** argv) {
    try {
        insist(argc==3,"usage: VERIFY_CERTIFICATE EXPECTED_ODD_MAXIMUM");
        verify(argv[1],parse_maximum(argv[2]));
    } catch(const std::exception& error) {
        std::cerr<<"FAIL: "<<error.what()<<'\n';return 2;
    }
    return 0;
}
