// Finite regression for the selected marked table, not a Lean proof.
// Start from a wholly blank tape and compare every cell in the bounded array
// with the candidate source-entry configuration. A bounds check rejects any
// run that leaves the array. The full unbounded proof remains open.
#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <string>

struct Row { int write, move, next, event; bool present; };
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  std::ifstream file(argv[1]);
  if (!file) return 2;
  std::array<std::array<Row, 2>, 285> rows{};
  std::string line;
  int state, read, write, next, event, count = 0;
  char move;
  while (std::getline(file, line)) {
    if (line.empty() || line[0] == '#') continue;
    if (std::sscanf(line.c_str(), "%d %d %d %c %d %d", &state, &read,
                    &write, &move, &next, &event) != 6 ||
        state < 0 || state >= 285 || read < 0 || read > 1 ||
        write < 0 || write > 1 || (move != 'L' && move != 'R') ||
        next < 0 || next >= 285 || event < 0 || event > 1 ||
        rows[state][read].present) return 2;
    rows[state][read] = {write, move == 'L' ? -1 : 1, next, event, true};
    ++count;
  }
  if (count != 570) return 2;
  constexpr int origin = 100000;
  std::array<unsigned char, 200000> tape{};
  int q = 0, head = origin;
  std::uint64_t steps = 0, events = 0;
  while (steps < 100000000 && q != 284) {
    if (head < 0 || head >= static_cast<int>(tape.size())) return 3;
    const Row r = rows[q][tape[head]];
    if (!r.present) return 2;
    tape[head] = static_cast<unsigned char>(r.write);
    head += r.move;
    q = r.next;
    events += r.event;
    ++steps;
  }
  if (q != 284 || steps != 89806142 || head != origin - 3818 || events != 0)
    return 1;
  for (int i = 0; i < static_cast<int>(tape.size()); ++i) {
    const int p = i - origin;
    const bool expected = p == -3821 || p == -3820 ||
                          (p >= 3 && p <= 3821 && p % 2 == 1);
    if (static_cast<bool>(tape[i]) != expected) return 1;
  }
  std::cout << "steps=" << steps << " state=" << q << " head=" << head-origin
            << " events=" << events << " bounded_tape_matches=yes\n";
}
