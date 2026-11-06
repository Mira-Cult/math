// Literal bounded execution. No compiler, macro stepping, or source evaluator.
#include <array>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
struct Row { int w=-1, d=0, q=-1, mark=0; };
int main(int argc,char**argv) {
 if(argc!=3) throw std::runtime_error("table and transition limit required");
 std::ifstream in(argv[1]); if(!in) throw std::runtime_error("cannot open table");
 std::vector<std::array<Row,2>> rows; std::string line; int states=0,start=0,beep=-1;
 while(std::getline(in,line)) {
  if(line.rfind("#!",0)==0){std::istringstream s(line.substr(2));std::string k;s>>k;if(k=="states")s>>states;else if(k=="start")s>>start;else if(k=="beep")s>>beep;continue;}
  if(line.empty())continue;std::istringstream s(line);int q,b,w,t,m=0;char d;
  if(!(s>>q>>b>>w>>d>>t))throw std::runtime_error("bad row");s>>m;
  if(q<0||q>=states||b<0||b>1||w<0||w>1||t<0||t>=states||(d!='L'&&d!='R'))throw std::runtime_error("invalid row");
  if(rows.empty())rows.resize(states);if(rows[q][b].w!=-1)throw std::runtime_error("duplicate row");rows[q][b]={w,d=='R'?1:-1,t,m};
 }
 if((int)rows.size()!=states)throw std::runtime_error("missing states");for(auto&a:rows)for(auto&r:a)if(r.w<0)throw std::runtime_error("missing row");
 const uint64_t limit=std::stoull(argv[2]);std::deque<unsigned char> tape(1,0);int64_t low=0,head=0;int q=start;
 std::cout<<"{\"events\":[";bool first=true;
 for(uint64_t step=1;step<=limit;++step){if(head<low){tape.push_front(0);--low;}if(head>=low+(int64_t)tape.size())tape.push_back(0);auto r=rows[q][tape[head-low]];bool event=r.mark||(beep>=0&&q==beep);tape[head-low]=r.w;head+=r.d;q=r.q;if(event){if(!first)std::cout<<',';first=false;std::cout<<step;}}
 std::cout<<"],\"steps\":"<<limit<<",\"state\":"<<q<<",\"head\":"<<head<<",\"ones\":[";first=true;
 for(size_t i=0;i<tape.size();++i)if(tape[i]){if(!first)std::cout<<',';first=false;std::cout<<low+(int64_t)i;}
 std::cout<<"]}\n";
}
