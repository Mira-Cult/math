// Independent exhaustive proof replay. No normalization, pruning, floating point or solver.
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

template<int N, int D>
bool verify(const std::array<std::uint64_t,D+1>& expected) {
    using Set=std::bitset<N>;
    Set blocked;
    blocked.set(0).set(N/6).set(5*N/6);
    std::array<std::uint64_t,D+1> counts{};
    std::vector<int> a, last;
    auto go=[&](auto&& self,Set all,int least,int length)->void {
        ++counts[length];
        if(length==D) return;
        for(int x=least;x<N;++x) {
            Set new_sums=(all<<x)|(all>>(N-x));
            if((new_sums&blocked).any()) continue;
            a.push_back(x);
            if(length+1==D-1) last=a;
            self(self,all|new_sums,x,length+1);
            a.pop_back();
        }
    };
    Set start;start.set(0);
    go(go,start,1,0);
    std::cout<<"N="<<N<<", depth counts:";
    for(auto v:counts)std::cout<<' '<<v;
    std::cout<<"\nlast depth-"<<D-1<<" witness:";
    for(int x:last)std::cout<<' '<<x;
    std::cout<<'\n';
    return counts==expected && counts[D]==0;
}

int main(){
    bool a=verify<36,10>({1,33,510,4448,19628,28638,11702,3608,504,162,0});
    bool b=verify<72,15>({1,69,2310,47804,625336,4499906,12521130,10635864,5026028,2571502,1440768,691444,249260,55472,1776,0});
    return a&&b?EXIT_SUCCESS:EXIT_FAILURE;
}
