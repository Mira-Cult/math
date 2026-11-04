// Independent bounded literal replay. This is finite evidence, not a proof oracle.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
struct Row { int write, move, next, event; };
int main(int argc, char **argv) {
  if (argc != 2) { std::cerr << "usage: replay events.tm\n"; return 2; }
  std::ifstream input(argv[1]);
  if (!input) return 2;
  std::array<Row, 570> rows{};
  std::string line;
  int count = 0, marks = 0;
  while (std::getline(input, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream fields(line);
    int state, read, write, next, event; char direction; std::string extra;
    if (!(fields >> state >> read >> write >> direction >> next >> event) ||
        (fields >> extra) || count >= 570 || state != count / 2 || read != count % 2 ||
        write < 0 || write > 1 || next < 0 || next >= 285 ||
        (direction != 'L' && direction != 'R') || event < 0 || event > 1) return 2;
    if (event && !(state == 121 && read == 1 && write == 0 && direction == 'L' && next == 1)) return 2;
    rows[count++] = {write, direction == 'L' ? -1 : 1, next, event};
    marks += event;
  }
  if (count != 570 || marks != 1) return 2;
  constexpr int bound = 1000000;
  std::vector<unsigned char> tape(2 * bound + 1, 0);
  int head = 0, state = 0, low = 0, high = 0;
  std::int64_t first = -1, events = 0;
  for (std::int64_t time = 0; time <= 89844409; ++time) {
    if (time == 89806142) {
      // Outside the visited interval every cell is still blank. Ensure the
      // interval covers every cell where the expected tape is nonblank.
      if (low > -3821 || high < 3821) return 3;
      int mismatches = 0;
      for (int x = low; x <= high; ++x) {
        bool expected = x == -3821 || x == -3820 || (3 <= x && x <= 3821 && x % 2 == 1);
        if (bool(tape[bound + x]) != expected) ++mismatches;
      }
      std::cout << "initialization t=" << time << " state=" << state << " head=" << head
                << " range=[" << low << ',' << high << "] cells_mismatch=" << mismatches
                << " events=" << events << '\n';
      if (state != 284 || head != -3818 || mismatches || events) return 3;
    }
    Row row = rows[2 * state + tape[bound + head]];
    if (row.event) {
      if (first < 0) first = time;
      ++events;
      std::cout << "event t=" << time << " state=" << state
                << " read=" << int(tape[bound + head]) << " head=" << head << '\n';
    }
    tape[bound + head] = row.write;
    head += row.move; state = row.next;
    if (head < -bound || head > bound) return 4;
    low = std::min(low, head); high = std::max(high, head);
  }
  std::cout << "first_event=" << first << " events=" << events << '\n';
  return first == 89844409 && events == 1 ? 0 : 5;
}
