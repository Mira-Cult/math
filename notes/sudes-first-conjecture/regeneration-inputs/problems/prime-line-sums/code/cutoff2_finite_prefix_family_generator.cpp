// Exact discovery of finite prime-pair populations; no square cutoff claim.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

int main(int argc, char **argv) {
  if (argc != 7) { std::cerr << "usage: generator output_stem bound Q stages lower upper\n"; return 1; }
  const uint32_t B = std::stoul(argv[2]), Q = std::stoul(argv[3]), stages = std::stoul(argv[4]);
  if (B < 100 || B > 2000000000U || Q < 1 || Q > 200000 || stages < 1 || stages > 30) return 1;
  const std::string stem = argc > 1 ? argv[1] : "/tmp/sude_finite_prefix";
  const uint32_t lower_bound = std::stoul(argv[5]);
  const uint32_t upper_bound = std::stoul(argv[6]);
  if (lower_bound < 44 || lower_bound >= upper_bound || upper_bound > B || (1u << stages) >= upper_bound - lower_bound) return 1;
  std::vector<uint8_t> live((B + 1) / 2, 1);
  live[0] = 0;
  for (uint64_t p = 3; p * p <= B; p += 2)
    if (live[p / 2])
      for (uint64_t x = p * p; x <= B; x += 2 * p) live[x / 2] = 0;
  std::vector<uint32_t> primes;
  for (uint32_t p = 3; p <= B; p += 2)
    if (live[p / 2]) primes.push_back(p);
  for (uint32_t p = 1; p <= 43; p += 2) live[p / 2] = 0;
  std::ofstream csv(stem + ".csv");
  std::ofstream bin(stem + ".bin", std::ios::binary);
  csv << "stage,gap,candidates,chosen_start,first_lower,last_lower,width,sum_lower,min_upper,max_upper,retained\n";
  std::cerr << "odd primes=" << primes.size() << '\n';
  uint64_t count = 0, sum_width2 = 0, max_width = 0, total_coverage = 0;
  for (unsigned j = 0; j < stages; ++j) {
    uint32_t gap = (1u << (j + 1));
    std::vector<uint32_t> cand;
    for (uint32_t p : primes) {
      if (p > upper_bound - gap) break;
      if (p >= lower_bound && p > 43 && live[p / 2] && live[(p + gap) / 2]) cand.push_back(p);
    }
    if (cand.size() < Q) { std::cerr << "insufficient stage " << j << '\n'; return 2; }
    uint32_t best_width = std::numeric_limits<uint32_t>::max();
    size_t best_start = 0;
    for (size_t i = 0; i + Q <= cand.size(); ++i) {
      uint32_t w = cand[i + Q - 1] - cand[i];
      if (w < best_width) { best_width = w; best_start = i; }
    }
    uint64_t sum_lower = 0;
    for (size_t k = best_start; k < best_start + Q; ++k) {
      uint32_t p = cand[k];
      if (!live[p / 2] || !live[(p + gap) / 2]) { std::cerr << "overlap"; return 3; }
      live[p / 2] = live[(p + gap) / 2] = 0;
      sum_lower += p;
      for (unsigned s = 0; s < 32; s += 8) bin.put(static_cast<char>((p >> s) & 255));
    }
    csv << j << ',' << gap << ',' << cand.size() << ',' << best_start << ','
        << cand[best_start] << ',' << cand[best_start + Q - 1] << ',' << best_width << ','
        << sum_lower << ',' << cand[best_start] + gap << ',' << cand[best_start + Q - 1] + gap << ',' << Q << '\n';
    count += 2 * Q; total_coverage += gap;
    sum_width2 += uint64_t(best_width) * best_width;
    max_width = std::max<uint64_t>(max_width, best_width);
    std::cerr << "stage " << j << " gap " << gap << " candidates " << cand.size()
              << " width " << best_width << " entries " << count << '\n';
  }
  std::cerr << "coverage=" << total_coverage << " sum_width2=" << sum_width2
            << " max_width=" << max_width << " variance="
            << 18 * sum_width2 + 4 * max_width * max_width << '\n';
}
