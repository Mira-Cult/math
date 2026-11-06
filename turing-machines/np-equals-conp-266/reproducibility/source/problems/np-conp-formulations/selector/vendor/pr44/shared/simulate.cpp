// Independent literal simulator for finite regression runs; no compiler imports.
// Test limits and host integers bound THIS SIMULATOR, never the delivered table.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

struct Row { int w=-1, d=0, q=-1; };
int main(int argc,char**argv) {
  try {
    if(argc<3) throw std::runtime_error("usage: simulator TABLE MAX_STEPS [BEEPS_TO_STOP] [STATE_TO_STOP]");
    std::ifstream in(argv[1]); if(!in) throw std::runtime_error("cannot read table");
    std::map<std::string,std::string> headers;
    std::map<std::pair<int,int>,Row> parsed;
    std::string line;
    while(std::getline(in,line)) {
      if(line.empty() || (line[0]=='#' && line.rfind("#!",0)!=0)) continue;
      std::istringstream ss(line); std::string first; ss>>first;
      if(first=="#!") {
        std::string key,value,extra; ss>>key>>value;
        if(key.empty() || value.empty() || (ss>>extra) || headers.count(key)) throw std::runtime_error("bad header");
        headers[key]=value;
      } else {
        int q=std::stoi(first),b,w,t; std::string d,extra;
        if(!(ss>>b>>w>>d>>t) || (ss>>extra) || q<0 || t<0 || (b!=0&&b!=1) || (w!=0&&w!=1) || (d!="L"&&d!="R")) throw std::runtime_error("bad row");
        if(parsed.count({q,b})) throw std::runtime_error("duplicate row");
        parsed[{q,b}]={w,d=="L"?-1:1,t};
      }
    }
    if(headers.size()!=6 || headers.at("format")!="beeper-v1" || headers.at("blank")!="0" || headers.at("head")!="0") throw std::runtime_error("bad conventions");
    int n=std::stoi(headers.at("states")),q=std::stoi(headers.at("start")),B=std::stoi(headers.at("beep"));
    if(n<=0 || q<0 || q>=n || B<0 || B>=n || parsed.size()!=2*size_t(n)) throw std::runtime_error("bad state inventory");
    std::vector<std::array<Row,2>> rows(n);
    for(int s=0;s<n;s++) for(int b=0;b<2;b++) {
      rows[s][b]=parsed.at({s,b}); if(rows[s][b].q>=n) throw std::runtime_error("unknown target");
    }
    uint64_t limit=std::stoull(argv[2]);
    if(limit>=uint64_t(std::numeric_limits<int64_t>::max()/2)) throw std::runtime_error("finite test limit too large");
    uint64_t want=argc>3?std::stoull(argv[3]):0;
    int stop=argc>4?std::stoi(argv[4]):-1;
    std::vector<uint8_t> plus(4096,0),minus(4096,0);
    int64_t head=0; uint64_t step=0; std::vector<uint64_t> beeps;
    while(step<limit && q!=stop) {
      auto &side=head>=0?plus:minus;
      size_t index=head>=0?size_t(head):size_t(-head-1);
      if(index>=side.size()) side.resize(std::max(side.size()*2,index+1),0);
      Row r=rows[q][side[index]];
      if(q==B) beeps.push_back(step+1);
      side[index]=r.w; head+=r.d; q=r.q; ++step;
      if(want && beeps.size()>=want) break;
    }
    std::cout<<"{\"steps\":"<<step<<",\"state\":"<<q<<",\"head\":"<<head<<",\"beeps\":[";
    for(size_t i=0;i<beeps.size();i++) std::cout<<(i?",":"")<<beeps[i];
    std::cout<<"],\"ones\":["; bool comma=false;
    for(size_t i=minus.size();i>0;--i) if(minus[i-1]) {std::cout<<(comma?",":"")<<-int64_t(i);comma=true;}
    for(size_t i=0;i<plus.size();++i) if(plus[i]) {std::cout<<(comma?",":"")<<i;comma=true;}
    std::cout<<"]}\n";
  } catch(std::exception const&e) {std::cerr<<e.what()<<"\n";return 1;}
}
