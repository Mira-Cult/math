// Independent finite blank-start control. This is not an infinite-run proof.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

struct Row { int write, move, next, event; bool present = false; };

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  std::ifstream in(argv[1]);
  if (!in) return 2;
  std::array<std::array<Row, 2>, 284> table{};
  std::string line, direction;
  int q, read, write, next, event, count = 0;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream row(line);
    if (!(row >> q >> read >> write >> direction >> next >> event) ||
        q < 0 || q >= 284 || read < 0 || read > 1 ||
        write < 0 || write > 1 || next < 0 || next >= 284 ||
        event < 0 || event > 1 || (direction != "L" && direction != "R") ||
        table[q][read].present) return 3;
    table[q][read] = {write, direction == "R" ? 1 : -1, next, event, true};
    ++count;
  }
  if (count != 568) return 3;
  constexpr int offset = 2000000;
  std::vector<unsigned char> tape(2 * offset + 1, 0);
  int state = 0, head = offset;
  for (std::uint64_t t = 0; t <= 60987213; ++t) {
    if (head < 0 || head >= static_cast<int>(tape.size())) return 4;
    const Row &r = table[state][tape[head]];
    if (r.event) {
      if (t != 60987213 || state != 99 || head - offset != -3817) return 5;
      std::cout << "first event: transition " << t << ", state " << state
                << ", head " << head - offset << '\n';
      return 0;
    }
    tape[head] = static_cast<unsigned char>(r.write);
    head += r.move;
    state = r.next;
  }
  return 6;
}
