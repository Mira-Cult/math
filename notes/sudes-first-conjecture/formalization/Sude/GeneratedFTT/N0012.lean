import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_631 : Nat.Prime 631 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨631, 3, [(2, 1), (3, 2), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_811 : Nat.Prime 811 := by
  apply nodeValid_prime [2, 3, 5] ⟨811, 3, [(2, 1), (3, 4), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_1097 : Nat.Prime 1097 := by
  apply nodeValid_prime [2, 137] ⟨1097, 3, [(2, 3), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_137
  · decide +kernel

theorem prime_1109 : Nat.Prime 1109 := by
  apply nodeValid_prime [2, 277] ⟨1109, 2, [(2, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_277
  · decide +kernel

theorem prime_1601 : Nat.Prime 1601 := by
  apply nodeValid_prime [2, 5] ⟨1601, 3, [(2, 6), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_2003 : Nat.Prime 2003 := by
  apply nodeValid_prime [2, 7, 11, 13] ⟨2003, 5, [(2, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_2381 : Nat.Prime 2381 := by
  apply nodeValid_prime [2, 5, 7, 17] ⟨2381, 3, [(2, 2), (5, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_2383 : Nat.Prime 2383 := by
  apply nodeValid_prime [2, 3, 397] ⟨2383, 5, [(2, 1), (3, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
  · decide +kernel

theorem prime_2473 : Nat.Prime 2473 := by
  apply nodeValid_prime [2, 3, 103] ⟨2473, 5, [(2, 3), (3, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_2857 : Nat.Prime 2857 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨2857, 11, [(2, 3), (3, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_2887 : Nat.Prime 2887 := by
  apply nodeValid_prime [2, 3, 13, 37] ⟨2887, 5, [(2, 1), (3, 1), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_3023 : Nat.Prime 3023 := by
  apply nodeValid_prime [2, 1511] ⟨3023, 5, [(2, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1511
  · decide +kernel

theorem prime_4007 : Nat.Prime 4007 := by
  apply nodeValid_prime [2, 2003] ⟨4007, 5, [(2, 1), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2003
  · decide +kernel

theorem prime_4051 : Nat.Prime 4051 := by
  apply nodeValid_prime [2, 3, 5] ⟨4051, 10, [(2, 1), (3, 4), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_4201 : Nat.Prime 4201 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨4201, 11, [(2, 3), (3, 1), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_4513 : Nat.Prime 4513 := by
  apply nodeValid_prime [2, 3, 47] ⟨4513, 7, [(2, 5), (3, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_4523 : Nat.Prime 4523 := by
  apply nodeValid_prime [2, 7, 17, 19] ⟨4523, 5, [(2, 1), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_5003 : Nat.Prime 5003 := by
  apply nodeValid_prime [2, 41, 61] ⟨5003, 2, [(2, 1), (41, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_61
  · decide +kernel

theorem prime_5009 : Nat.Prime 5009 := by
  apply nodeValid_prime [2, 313] ⟨5009, 3, [(2, 4), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_313
  · decide +kernel

theorem prime_5557 : Nat.Prime 5557 := by
  apply nodeValid_prime [2, 3, 463] ⟨5557, 2, [(2, 2), (3, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
  · decide +kernel

theorem prime_5711 : Nat.Prime 5711 := by
  apply nodeValid_prime [2, 5, 571] ⟨5711, 19, [(2, 1), (5, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_571
  · decide +kernel

theorem prime_5717 : Nat.Prime 5717 := by
  apply nodeValid_prime [2, 1429] ⟨5717, 2, [(2, 2), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1429
  · decide +kernel

theorem prime_5881 : Nat.Prime 5881 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨5881, 31, [(2, 3), (3, 1), (5, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_6581 : Nat.Prime 6581 := by
  apply nodeValid_prime [2, 5, 7, 47] ⟨6581, 14, [(2, 2), (5, 1), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_6661 : Nat.Prime 6661 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨6661, 6, [(2, 2), (3, 2), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_6737 : Nat.Prime 6737 := by
  apply nodeValid_prime [2, 421] ⟨6737, 3, [(2, 4), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_421
  · decide +kernel

theorem prime_6781 : Nat.Prime 6781 := by
  apply nodeValid_prime [2, 3, 5, 113] ⟨6781, 2, [(2, 2), (3, 1), (5, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_6983 : Nat.Prime 6983 := by
  apply nodeValid_prime [2, 3491] ⟨6983, 5, [(2, 1), (3491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3491
  · decide +kernel

theorem prime_7573 : Nat.Prime 7573 := by
  apply nodeValid_prime [2, 3, 631] ⟨7573, 2, [(2, 2), (3, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
  · decide +kernel

theorem prime_7867 : Nat.Prime 7867 := by
  apply nodeValid_prime [2, 3, 19, 23] ⟨7867, 3, [(2, 1), (3, 2), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_8693 : Nat.Prime 8693 := by
  apply nodeValid_prime [2, 41, 53] ⟨8693, 2, [(2, 2), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_8803 : Nat.Prime 8803 := by
  apply nodeValid_prime [2, 3, 163] ⟨8803, 2, [(2, 1), (3, 3), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
  · decide +kernel

theorem prime_9007 : Nat.Prime 9007 := by
  apply nodeValid_prime [2, 3, 19, 79] ⟨9007, 3, [(2, 1), (3, 1), (19, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_79
  · decide +kernel

theorem prime_9239 : Nat.Prime 9239 := by
  apply nodeValid_prime [2, 31, 149] ⟨9239, 19, [(2, 1), (31, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_149
  · decide +kernel

theorem prime_9533 : Nat.Prime 9533 := by
  apply nodeValid_prime [2, 2383] ⟨9533, 2, [(2, 2), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2383
  · decide +kernel

theorem prime_9949 : Nat.Prime 9949 := by
  apply nodeValid_prime [2, 3, 829] ⟨9949, 2, [(2, 2), (3, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_829
  · decide +kernel

theorem prime_11423 : Nat.Prime 11423 := by
  apply nodeValid_prime [2, 5711] ⟨11423, 5, [(2, 1), (5711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5711
  · decide +kernel

theorem prime_12043 : Nat.Prime 12043 := by
  apply nodeValid_prime [2, 3, 223] ⟨12043, 2, [(2, 1), (3, 3), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
  · decide +kernel

theorem prime_12413 : Nat.Prime 12413 := by
  apply nodeValid_prime [2, 29, 107] ⟨12413, 2, [(2, 2), (29, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_107
  · decide +kernel

theorem prime_12641 : Nat.Prime 12641 := by
  apply nodeValid_prime [2, 5, 79] ⟨12641, 3, [(2, 5), (5, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_13163 : Nat.Prime 13163 := by
  apply nodeValid_prime [2, 6581] ⟨13163, 2, [(2, 1), (6581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6581
  · decide +kernel

theorem prime_14281 : Nat.Prime 14281 := by
  apply nodeValid_prime [2, 3, 5, 7, 17] ⟨14281, 19, [(2, 3), (3, 1), (5, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_14461 : Nat.Prime 14461 := by
  apply nodeValid_prime [2, 3, 5, 241] ⟨14461, 2, [(2, 2), (3, 1), (5, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_14779 : Nat.Prime 14779 := by
  apply nodeValid_prime [2, 3, 821] ⟨14779, 3, [(2, 1), (3, 2), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_821
  · decide +kernel

theorem prime_16229 : Nat.Prime 16229 := by
  apply nodeValid_prime [2, 4057] ⟨16229, 2, [(2, 2), (4057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4057
  · decide +kernel

theorem prime_17387 : Nat.Prime 17387 := by
  apply nodeValid_prime [2, 8693] ⟨17387, 2, [(2, 1), (8693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8693
  · decide +kernel

theorem prime_17389 : Nat.Prime 17389 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨17389, 2, [(2, 2), (3, 3), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_17497 : Nat.Prime 17497 := by
  apply nodeValid_prime [2, 3] ⟨17497, 5, [(2, 3), (3, 7)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_17737 : Nat.Prime 17737 := by
  apply nodeValid_prime [2, 3, 739] ⟨17737, 7, [(2, 3), (3, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_739
  · decide +kernel

theorem prime_18461 : Nat.Prime 18461 := by
  apply nodeValid_prime [2, 5, 13, 71] ⟨18461, 2, [(2, 2), (5, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_24181 : Nat.Prime 24181 := by
  apply nodeValid_prime [2, 3, 5, 13, 31] ⟨24181, 17, [(2, 2), (3, 1), (5, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_27653 : Nat.Prime 27653 := by
  apply nodeValid_prime [2, 31, 223] ⟨27653, 2, [(2, 2), (31, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_223
  · decide +kernel

theorem prime_29741 : Nat.Prime 29741 := by
  apply nodeValid_prime [2, 5, 1487] ⟨29741, 2, [(2, 2), (5, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1487
  · decide +kernel

theorem prime_30293 : Nat.Prime 30293 := by
  apply nodeValid_prime [2, 7573] ⟨30293, 2, [(2, 2), (7573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7573
  · decide +kernel

theorem prime_30757 : Nat.Prime 30757 := by
  apply nodeValid_prime [2, 3, 11, 233] ⟨30757, 5, [(2, 2), (3, 1), (11, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_233
  · decide +kernel

theorem prime_31177 : Nat.Prime 31177 := by
  apply nodeValid_prime [2, 3, 433] ⟨31177, 7, [(2, 3), (3, 2), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_433
  · decide +kernel

theorem prime_36923 : Nat.Prime 36923 := by
  apply nodeValid_prime [2, 18461] ⟨36923, 2, [(2, 1), (18461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18461
  · decide +kernel

theorem prime_37061 : Nat.Prime 37061 := by
  apply nodeValid_prime [2, 5, 17, 109] ⟨37061, 2, [(2, 2), (5, 1), (17, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_109
  · decide +kernel

theorem prime_38651 : Nat.Prime 38651 := by
  apply nodeValid_prime [2, 5, 773] ⟨38651, 2, [(2, 1), (5, 2), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_773
  · decide +kernel

theorem prime_40087 : Nat.Prime 40087 := by
  apply nodeValid_prime [2, 3, 17, 131] ⟨40087, 3, [(2, 1), (3, 2), (17, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_131
  · decide +kernel

theorem prime_40423 : Nat.Prime 40423 := by
  apply nodeValid_prime [2, 3, 6737] ⟨40423, 3, [(2, 1), (3, 1), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6737
  · decide +kernel

theorem prime_43649 : Nat.Prime 43649 := by
  apply nodeValid_prime [2, 11, 31] ⟨43649, 3, [(2, 7), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_53891 : Nat.Prime 53891 := by
  apply nodeValid_prime [2, 5, 17, 317] ⟨53891, 2, [(2, 1), (5, 1), (17, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_317
  · decide +kernel

theorem prime_57191 : Nat.Prime 57191 := by
  apply nodeValid_prime [2, 5, 7, 19, 43] ⟨57191, 7, [(2, 1), (5, 1), (7, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_73847 : Nat.Prime 73847 := by
  apply nodeValid_prime [2, 36923] ⟨73847, 5, [(2, 1), (36923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36923
  · decide +kernel

theorem prime_77659 : Nat.Prime 77659 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨77659, 2, [(2, 1), (3, 1), (7, 1), (43, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_77783 : Nat.Prime 77783 := by
  apply nodeValid_prime [2, 38891] ⟨77783, 5, [(2, 1), (38891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38891
  · decide +kernel

theorem prime_85093 : Nat.Prime 85093 := by
  apply nodeValid_prime [2, 3, 7, 1013] ⟨85093, 2, [(2, 2), (3, 1), (7, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1013
  · decide +kernel

theorem prime_90731 : Nat.Prime 90731 := by
  apply nodeValid_prime [2, 5, 43, 211] ⟨90731, 2, [(2, 1), (5, 1), (43, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_211
  · decide +kernel

theorem prime_94621 : Nat.Prime 94621 := by
  apply nodeValid_prime [2, 3, 5, 19, 83] ⟨94621, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_106123 : Nat.Prime 106123 := by
  apply nodeValid_prime [2, 3, 23, 769] ⟨106123, 2, [(2, 1), (3, 1), (23, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_769
  · decide +kernel

theorem prime_112279 : Nat.Prime 112279 := by
  apply nodeValid_prime [2, 3, 18713] ⟨112279, 3, [(2, 1), (3, 1), (18713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18713
  · decide +kernel

theorem prime_121633 : Nat.Prime 121633 := by
  apply nodeValid_prime [2, 3, 7, 181] ⟨121633, 5, [(2, 5), (3, 1), (7, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_181
  · decide +kernel

theorem prime_127609 : Nat.Prime 127609 := by
  apply nodeValid_prime [2, 3, 13, 409] ⟨127609, 14, [(2, 3), (3, 1), (13, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_409
  · decide +kernel

theorem prime_129193 : Nat.Prime 129193 := by
  apply nodeValid_prime [2, 3, 7, 769] ⟨129193, 5, [(2, 3), (3, 1), (7, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_769
  · decide +kernel

theorem prime_162829 : Nat.Prime 162829 := by
  apply nodeValid_prime [2, 3, 4523] ⟨162829, 2, [(2, 2), (3, 2), (4523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4523
  · decide +kernel

theorem prime_178447 : Nat.Prime 178447 := by
  apply nodeValid_prime [2, 3, 29741] ⟨178447, 3, [(2, 1), (3, 1), (29741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29741
  · decide +kernel

theorem prime_201403 : Nat.Prime 201403 := by
  apply nodeValid_prime [2, 3, 67, 167] ⟨201403, 3, [(2, 1), (3, 2), (67, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_167
  · decide +kernel

theorem prime_229217 : Nat.Prime 229217 := by
  apply nodeValid_prime [2, 13, 19, 29] ⟨229217, 3, [(2, 5), (13, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_268747 : Nat.Prime 268747 := by
  apply nodeValid_prime [2, 3, 47, 953] ⟨268747, 2, [(2, 1), (3, 1), (47, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_953
  · decide +kernel

theorem prime_274121 : Nat.Prime 274121 := by
  apply nodeValid_prime [2, 5, 7, 11, 89] ⟨274121, 6, [(2, 3), (5, 1), (7, 1), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_313003 : Nat.Prime 313003 := by
  apply nodeValid_prime [2, 3, 17389] ⟨313003, 2, [(2, 1), (3, 2), (17389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17389
  · decide +kernel

theorem prime_345853 : Nat.Prime 345853 := by
  apply nodeValid_prime [2, 3, 13, 739] ⟨345853, 6, [(2, 2), (3, 2), (13, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_739
  · decide +kernel

theorem prime_351829 : Nat.Prime 351829 := by
  apply nodeValid_prime [2, 3, 29, 337] ⟨351829, 2, [(2, 2), (3, 2), (29, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_337
  · decide +kernel

theorem prime_367309 : Nat.Prime 367309 := by
  apply nodeValid_prime [2, 3, 19, 179] ⟨367309, 6, [(2, 2), (3, 3), (19, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_179
  · decide +kernel

theorem prime_390703 : Nat.Prime 390703 := by
  apply nodeValid_prime [2, 3, 13, 5009] ⟨390703, 3, [(2, 1), (3, 1), (13, 1), (5009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5009
  · decide +kernel

theorem prime_418981 : Nat.Prime 418981 := by
  apply nodeValid_prime [2, 3, 5, 6983] ⟨418981, 7, [(2, 2), (3, 1), (5, 1), (6983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6983
  · decide +kernel

theorem prime_424493 : Nat.Prime 424493 := by
  apply nodeValid_prime [2, 106123] ⟨424493, 2, [(2, 2), (106123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_106123
  · decide +kernel

theorem prime_424819 : Nat.Prime 424819 := by
  apply nodeValid_prime [2, 3, 7867] ⟨424819, 2, [(2, 1), (3, 3), (7867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7867
  · decide +kernel

theorem prime_538399 : Nat.Prime 538399 := by
  apply nodeValid_prime [2, 3, 7, 4273] ⟨538399, 6, [(2, 1), (3, 2), (7, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4273
  · decide +kernel

theorem prime_597407 : Nat.Prime 597407 := by
  apply nodeValid_prime [2, 281, 1063] ⟨597407, 5, [(2, 1), (281, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_1063
  · decide +kernel

theorem prime_664621 : Nat.Prime 664621 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 53] ⟨664621, 7, [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_675079 : Nat.Prime 675079 := by
  apply nodeValid_prime [2, 3, 59, 1907] ⟨675079, 3, [(2, 1), (3, 1), (59, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_1907
  · decide +kernel

theorem prime_810967 : Nat.Prime 810967 := by
  apply nodeValid_prime [2, 3, 13, 37, 281] ⟨810967, 5, [(2, 1), (3, 1), (13, 1), (37, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_281
  · decide +kernel

theorem prime_1074989 : Nat.Prime 1074989 := by
  apply nodeValid_prime [2, 268747] ⟨1074989, 2, [(2, 2), (268747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_268747
  · decide +kernel

theorem prime_1105651 : Nat.Prime 1105651 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨1105651, 3, [(2, 1), (3, 5), (5, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_1272629 : Nat.Prime 1272629 := by
  apply nodeValid_prime [2, 7, 43, 151] ⟨1272629, 2, [(2, 2), (7, 2), (43, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_151
  · decide +kernel

theorem prime_1275847 : Nat.Prime 1275847 := by
  apply nodeValid_prime [2, 3, 11, 13, 1487] ⟨1275847, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1487
  · decide +kernel

theorem prime_1332893 : Nat.Prime 1332893 := by
  apply nodeValid_prime [2, 11, 30293] ⟨1332893, 2, [(2, 2), (11, 1), (30293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_30293
  · decide +kernel

theorem prime_1407317 : Nat.Prime 1407317 := by
  apply nodeValid_prime [2, 351829] ⟨1407317, 2, [(2, 2), (351829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_351829
  · decide +kernel

theorem prime_1468739 : Nat.Prime 1468739 := by
  apply nodeValid_prime [2, 19, 38651] ⟨1468739, 2, [(2, 1), (19, 1), (38651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_38651
  · decide +kernel

theorem prime_1553381 : Nat.Prime 1553381 := by
  apply nodeValid_prime [2, 5, 101, 769] ⟨1553381, 2, [(2, 2), (5, 1), (101, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_769
  · decide +kernel

theorem prime_1926469 : Nat.Prime 1926469 := by
  apply nodeValid_prime [2, 3, 59, 907] ⟨1926469, 6, [(2, 2), (3, 2), (59, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_907
  · decide +kernel

theorem prime_2042233 : Nat.Prime 2042233 := by
  apply nodeValid_prime [2, 3, 85093] ⟨2042233, 10, [(2, 3), (3, 1), (85093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_85093
  · decide +kernel

theorem prime_2206081 : Nat.Prime 2206081 := by
  apply nodeValid_prime [2, 3, 5, 383] ⟨2206081, 7, [(2, 7), (3, 2), (5, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
  · decide +kernel

theorem prime_2209003 : Nat.Prime 2209003 := by
  apply nodeValid_prime [2, 3, 347, 1061] ⟨2209003, 2, [(2, 1), (3, 1), (347, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
    · exact prime_1061
  · decide +kernel

theorem prime_2464571 : Nat.Prime 2464571 := by
  apply nodeValid_prime [2, 5, 37, 6661] ⟨2464571, 2, [(2, 1), (5, 1), (37, 1), (6661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_6661
  · decide +kernel

theorem prime_2501501 : Nat.Prime 2501501 := by
  apply nodeValid_prime [2, 5, 5003] ⟨2501501, 2, [(2, 2), (5, 3), (5003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5003
  · decide +kernel

theorem prime_3100633 : Nat.Prime 3100633 := by
  apply nodeValid_prime [2, 3, 129193] ⟨3100633, 5, [(2, 3), (3, 1), (129193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_129193
  · decide +kernel

theorem prime_3756037 : Nat.Prime 3756037 := by
  apply nodeValid_prime [2, 3, 313003] ⟨3756037, 2, [(2, 2), (3, 1), (313003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313003
  · decide +kernel

theorem prime_4491161 : Nat.Prime 4491161 := by
  apply nodeValid_prime [2, 5, 112279] ⟨4491161, 3, [(2, 3), (5, 1), (112279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_112279
  · decide +kernel

theorem prime_5775043 : Nat.Prime 5775043 := by
  apply nodeValid_prime [2, 3, 7, 13, 1511] ⟨5775043, 3, [(2, 1), (3, 1), (7, 2), (13, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1511
  · decide +kernel

theorem prime_6067199 : Nat.Prime 6067199 := by
  apply nodeValid_prime [2, 17, 178447] ⟨6067199, 13, [(2, 1), (17, 1), (178447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_178447
  · decide +kernel

theorem prime_7215661 : Nat.Prime 7215661 := by
  apply nodeValid_prime [2, 3, 5, 40087] ⟨7215661, 6, [(2, 2), (3, 2), (5, 1), (40087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_40087
  · decide +kernel

theorem prime_7815793 : Nat.Prime 7815793 := by
  apply nodeValid_prime [2, 3, 162829] ⟨7815793, 5, [(2, 4), (3, 1), (162829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_162829
  · decide +kernel

theorem prime_8280053 : Nat.Prime 8280053 := by
  apply nodeValid_prime [2, 11, 227, 829] ⟨8280053, 2, [(2, 2), (11, 1), (227, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_227
    · exact prime_829
  · decide +kernel

theorem prime_9320287 : Nat.Prime 9320287 := by
  apply nodeValid_prime [2, 3, 1553381] ⟨9320287, 3, [(2, 1), (3, 1), (1553381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1553381
  · decide +kernel

theorem prime_9400073 : Nat.Prime 9400073 := by
  apply nodeValid_prime [2, 11, 37, 2887] ⟨9400073, 3, [(2, 3), (11, 1), (37, 1), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_2887
  · decide +kernel

theorem prime_9691183 : Nat.Prime 9691183 := by
  apply nodeValid_prime [2, 3, 538399] ⟨9691183, 6, [(2, 1), (3, 2), (538399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_538399
  · decide +kernel

theorem prime_9881561 : Nat.Prime 9881561 := by
  apply nodeValid_prime [2, 5, 13, 31, 613] ⟨9881561, 3, [(2, 3), (5, 1), (13, 1), (31, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_613
  · decide +kernel

theorem prime_14319029 : Nat.Prime 14319029 := by
  apply nodeValid_prime [2, 151, 157] ⟨14319029, 2, [(2, 2), (151, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_157
  · decide +kernel

theorem prime_15352433 : Nat.Prime 15352433 := by
  apply nodeValid_prime [2, 109, 8803] ⟨15352433, 5, [(2, 4), (109, 1), (8803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_8803
  · decide +kernel

theorem prime_16409527 : Nat.Prime 16409527 := by
  apply nodeValid_prime [2, 3, 7, 390703] ⟨16409527, 6, [(2, 1), (3, 1), (7, 1), (390703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_390703
  · decide +kernel

theorem prime_21960259 : Nat.Prime 21960259 := by
  apply nodeValid_prime [2, 3, 811, 4513] ⟨21960259, 2, [(2, 1), (3, 1), (811, 1), (4513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
    · exact prime_4513
  · decide +kernel

theorem prime_24497371 : Nat.Prime 24497371 := by
  apply nodeValid_prime [2, 3, 5, 90731] ⟨24497371, 2, [(2, 1), (3, 3), (5, 1), (90731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_90731
  · decide +kernel

theorem prime_24695563 : Nat.Prime 24695563 := by
  apply nodeValid_prime [2, 3, 53, 77659] ⟨24695563, 2, [(2, 1), (3, 1), (53, 1), (77659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_77659
  · decide +kernel

theorem prime_30704867 : Nat.Prime 30704867 := by
  apply nodeValid_prime [2, 15352433] ⟨30704867, 2, [(2, 1), (15352433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15352433
  · decide +kernel

theorem prime_31006331 : Nat.Prime 31006331 := by
  apply nodeValid_prime [2, 5, 3100633] ⟨31006331, 2, [(2, 1), (5, 1), (3100633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3100633
  · decide +kernel

theorem prime_37159163 : Nat.Prime 37159163 := by
  apply nodeValid_prime [2, 1301, 14281] ⟨37159163, 2, [(2, 1), (1301, 1), (14281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1301
    · exact prime_14281
  · decide +kernel

theorem prime_39202633 : Nat.Prime 39202633 := by
  apply nodeValid_prime [2, 3, 7, 77783] ⟨39202633, 5, [(2, 3), (3, 2), (7, 1), (77783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_77783
  · decide +kernel

theorem prime_46437343 : Nat.Prime 46437343 := by
  apply nodeValid_prime [2, 3, 7, 1105651] ⟨46437343, 3, [(2, 1), (3, 1), (7, 1), (1105651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1105651
  · decide +kernel

theorem prime_61684709 : Nat.Prime 61684709 := by
  apply nodeValid_prime [2, 73, 151, 1399] ⟨61684709, 2, [(2, 2), (73, 1), (151, 1), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_151
    · exact prime_1399
  · decide +kernel

theorem prime_68277439 : Nat.Prime 68277439 := by
  apply nodeValid_prime [2, 3, 31, 40787] ⟨68277439, 15, [(2, 1), (3, 3), (31, 1), (40787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_40787
  · decide +kernel

theorem prime_83113411 : Nat.Prime 83113411 := by
  apply nodeValid_prime [2, 3, 5, 19, 43, 3391] ⟨83113411, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (43, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_43
    · exact prime_3391
  · decide +kernel

theorem prime_84910129 : Nat.Prime 84910129 := by
  apply nodeValid_prime [2, 3, 109, 16229] ⟨84910129, 7, [(2, 4), (3, 1), (109, 1), (16229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_16229
  · decide +kernel

theorem prime_87508871 : Nat.Prime 87508871 := by
  apply nodeValid_prime [2, 5, 19, 43, 10711] ⟨87508871, 7, [(2, 1), (5, 1), (19, 1), (43, 1), (10711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_43
    · exact prime_10711
  · decide +kernel

theorem prime_180589327 : Nat.Prime 180589327 := by
  apply nodeValid_prime [2, 3, 2381, 12641] ⟨180589327, 3, [(2, 1), (3, 1), (2381, 1), (12641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2381
    · exact prime_12641
  · decide +kernel

theorem prime_187998593 : Nat.Prime 187998593 := by
  apply nodeValid_prime [2, 1468739] ⟨187998593, 3, [(2, 7), (1468739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1468739
  · decide +kernel

theorem prime_269489383 : Nat.Prime 269489383 := by
  apply nodeValid_prime [2, 3, 79, 199, 2857] ⟨269489383, 3, [(2, 1), (3, 1), (79, 1), (199, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_199
    · exact prime_2857
  · decide +kernel

theorem prime_278648767 : Nat.Prime 278648767 := by
  apply nodeValid_prime [2, 3, 11, 1407317] ⟨278648767, 5, [(2, 1), (3, 2), (11, 1), (1407317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1407317
  · decide +kernel

theorem prime_295826617 : Nat.Prime 295826617 := by
  apply nodeValid_prime [2, 3, 331, 12413] ⟨295826617, 13, [(2, 3), (3, 2), (331, 1), (12413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
    · exact prime_12413
  · decide +kernel

theorem prime_640586897 : Nat.Prime 640586897 := by
  apply nodeValid_prime [2, 109, 367309] ⟨640586897, 3, [(2, 4), (109, 1), (367309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_367309
  · decide +kernel

theorem prime_780892207 : Nat.Prime 780892207 := by
  apply nodeValid_prime [2, 3, 101, 107, 12043] ⟨780892207, 3, [(2, 1), (3, 1), (101, 1), (107, 1), (12043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_107
    · exact prime_12043
  · decide +kernel

theorem prime_1776228367 : Nat.Prime 1776228367 := by
  apply nodeValid_prime [2, 3, 11, 29, 167, 5557] ⟨1776228367, 5, [(2, 1), (3, 1), (11, 1), (29, 1), (167, 1), (5557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_167
    · exact prime_5557
  · decide +kernel

theorem prime_2385704983 : Nat.Prime 2385704983 := by
  apply nodeValid_prime [2, 3, 191, 307, 6781] ⟨2385704983, 3, [(2, 1), (3, 1), (191, 1), (307, 1), (6781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_307
    · exact prime_6781
  · decide +kernel

theorem prime_2581114771 : Nat.Prime 2581114771 := by
  apply nodeValid_prime [2, 3, 5, 13, 2206081] ⟨2581114771, 3, [(2, 1), (3, 2), (5, 1), (13, 1), (2206081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_2206081
  · decide +kernel

theorem prime_2644343719 : Nat.Prime 2644343719 := by
  apply nodeValid_prime [2, 3, 23, 439, 43649] ⟨2644343719, 3, [(2, 1), (3, 1), (23, 1), (439, 1), (43649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_439
    · exact prime_43649
  · decide +kernel

theorem prime_2938738169 : Nat.Prime 2938738169 := by
  apply nodeValid_prime [2, 47, 7815793] ⟨2938738169, 3, [(2, 3), (47, 1), (7815793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_7815793
  · decide +kernel

theorem prime_3918317461 : Nat.Prime 3918317461 := by
  apply nodeValid_prime [2, 3, 5, 5717, 11423] ⟨3918317461, 10, [(2, 2), (3, 1), (5, 1), (5717, 1), (11423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5717
    · exact prime_11423
  · decide +kernel

theorem prime_4064043671 : Nat.Prime 4064043671 := by
  apply nodeValid_prime [2, 5, 199, 2042233] ⟨4064043671, 14, [(2, 1), (5, 1), (199, 1), (2042233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_2042233
  · decide +kernel

theorem prime_7104913469 : Nat.Prime 7104913469 := by
  apply nodeValid_prime [2, 1776228367] ⟨7104913469, 2, [(2, 2), (1776228367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1776228367
  · decide +kernel

theorem prime_8128084817 : Nat.Prime 8128084817 := by
  apply nodeValid_prime [2, 23, 37, 673, 887] ⟨8128084817, 3, [(2, 4), (23, 1), (37, 1), (673, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_673
    · exact prime_887
  · decide +kernel

theorem prime_12251241941 : Nat.Prime 12251241941 := by
  apply nodeValid_prime [2, 5, 7, 87508871] ⟨12251241941, 2, [(2, 2), (5, 1), (7, 1), (87508871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_87508871
  · decide +kernel

theorem prime_23857049831 : Nat.Prime 23857049831 := by
  apply nodeValid_prime [2, 5, 2385704983] ⟨23857049831, 17, [(2, 1), (5, 1), (2385704983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2385704983
  · decide +kernel

theorem prime_35264858029 : Nat.Prime 35264858029 := by
  apply nodeValid_prime [2, 3, 2938738169] ⟨35264858029, 2, [(2, 2), (3, 1), (2938738169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2938738169
  · decide +kernel

theorem prime_72271213589 : Nat.Prime 72271213589 := by
  apply nodeValid_prime [2, 7, 2581114771] ⟨72271213589, 2, [(2, 2), (7, 1), (2581114771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2581114771
  · decide +kernel

theorem prime_73152763553 : Nat.Prime 73152763553 := by
  apply nodeValid_prime [2, 11, 29, 61, 4051] ⟨73152763553, 3, [(2, 5), (11, 1), (29, 2), (61, 1), (4051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_61
    · exact prime_4051
  · decide +kernel

theorem prime_74041624133 : Nat.Prime 74041624133 := by
  apply nodeValid_prime [2, 7, 2644343719] ⟨74041624133, 2, [(2, 2), (7, 1), (2644343719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2644343719
  · decide +kernel

theorem prime_140714287093 : Nat.Prime 140714287093 := by
  apply nodeValid_prime [2, 3, 367, 1811, 5881] ⟨140714287093, 2, [(2, 2), (3, 2), (367, 1), (1811, 1), (5881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_1811
    · exact prime_5881
  · decide +kernel

theorem prime_140714287729 : Nat.Prime 140714287729 := by
  apply nodeValid_prime [2, 3, 7, 43, 659, 14779] ⟨140714287729, 19, [(2, 4), (3, 1), (7, 1), (43, 1), (659, 1), (14779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_659
    · exact prime_14779
  · decide +kernel

theorem prime_140714303413 : Nat.Prime 140714303413 := by
  apply nodeValid_prime [2, 3, 271, 2473, 17497] ⟨140714303413, 5, [(2, 2), (3, 1), (271, 1), (2473, 1), (17497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_2473
    · exact prime_17497
  · decide +kernel

theorem prime_141059428243 : Nat.Prime 141059428243 := by
  apply nodeValid_prime [2, 3, 17, 24181, 57191] ⟨141059428243, 2, [(2, 1), (3, 1), (17, 1), (24181, 1), (57191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_24181
    · exact prime_57191
  · decide +kernel

theorem prime_141059428597 : Nat.Prime 141059428597 := by
  apply nodeValid_prime [2, 3, 3918317461] ⟨141059428597, 2, [(2, 2), (3, 2), (3918317461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3918317461
  · decide +kernel

theorem prime_141059432117 : Nat.Prime 141059432117 := by
  apply nodeValid_prime [2, 35264858029] ⟨141059432117, 2, [(2, 2), (35264858029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35264858029
  · decide +kernel

theorem prime_141405122927 : Nat.Prime 141405122927 := by
  apply nodeValid_prime [2, 239, 295826617] ⟨141405122927, 5, [(2, 1), (239, 1), (295826617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_295826617
  · decide +kernel

theorem prime_141405122959 : Nat.Prime 141405122959 := by
  apply nodeValid_prime [2, 3, 11, 41, 1699, 30757] ⟨141405122959, 6, [(2, 1), (3, 1), (11, 1), (41, 1), (1699, 1), (30757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_1699
    · exact prime_30757
  · decide +kernel

theorem prime_141405137911 : Nat.Prime 141405137911 := by
  apply nodeValid_prime [2, 3, 5, 53, 9881561] ⟨141405137911, 6, [(2, 1), (3, 3), (5, 1), (53, 1), (9881561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_9881561
  · decide +kernel

theorem prime_141751415459 : Nat.Prime 141751415459 := by
  apply nodeValid_prime [2, 263, 269489383] ⟨141751415459, 2, [(2, 1), (263, 1), (269489383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_269489383
  · decide +kernel

theorem prime_141751460273 : Nat.Prime 141751460273 := by
  apply nodeValid_prime [2, 38651, 229217] ⟨141751460273, 3, [(2, 4), (38651, 1), (229217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_38651
    · exact prime_229217
  · decide +kernel

theorem prime_141751461283 : Nat.Prime 141751461283 := by
  apply nodeValid_prime [2, 3, 383, 61684709] ⟨141751461283, 11, [(2, 1), (3, 1), (383, 1), (61684709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_383
    · exact prime_61684709
  · decide +kernel

theorem prime_142098269381 : Nat.Prime 142098269381 := by
  apply nodeValid_prime [2, 5, 7104913469] ⟨142098269381, 2, [(2, 2), (5, 1), (7104913469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7104913469
  · decide +kernel

theorem prime_142098269503 : Nat.Prime 142098269503 := by
  apply nodeValid_prime [2, 3, 7, 137, 24695563] ⟨142098269503, 3, [(2, 1), (3, 1), (7, 1), (137, 1), (24695563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_24695563
  · decide +kernel

theorem prime_142098269581 : Nat.Prime 142098269581 := by
  apply nodeValid_prime [2, 3, 5, 17, 46437343] ⟨142098269581, 2, [(2, 2), (3, 2), (5, 1), (17, 1), (46437343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_46437343
  · decide +kernel

theorem prime_142445698123 : Nat.Prime 142445698123 := by
  apply nodeValid_prime [2, 3, 7, 13, 43, 6067199] ⟨142445698123, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (43, 1), (6067199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_6067199
  · decide +kernel

theorem prime_142445700493 : Nat.Prime 142445700493 := by
  apply nodeValid_prime [2, 3, 829, 14319029] ⟨142445700493, 2, [(2, 2), (3, 1), (829, 1), (14319029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_829
    · exact prime_14319029
  · decide +kernel

theorem prime_142445702911 : Nat.Prime 142445702911 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 2351, 9949] ⟨142445702911, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (2351, 1), (9949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_2351
    · exact prime_9949
  · decide +kernel

theorem prime_142793713219 : Nat.Prime 142793713219 := by
  apply nodeValid_prime [2, 3, 13, 317, 5775043] ⟨142793713219, 2, [(2, 1), (3, 1), (13, 1), (317, 1), (5775043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_317
    · exact prime_5775043
  · decide +kernel

theorem prime_142793735219 : Nat.Prime 142793735219 := by
  apply nodeValid_prime [2, 37061, 1926469] ⟨142793735219, 2, [(2, 1), (37061, 1), (1926469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37061
    · exact prime_1926469
  · decide +kernel

theorem prime_142793736277 : Nat.Prime 142793736277 := by
  apply nodeValid_prime [2, 3, 19, 271, 121633] ⟨142793736277, 5, [(2, 2), (3, 1), (19, 2), (271, 1), (121633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_271
    · exact prime_121633
  · decide +kernel

theorem prime_143142283393 : Nat.Prime 143142283393 := by
  apply nodeValid_prime [2, 3, 83, 4491161] ⟨143142283393, 5, [(2, 7), (3, 1), (83, 1), (4491161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_4491161
  · decide +kernel

theorem prime_143142283681 : Nat.Prime 143142283681 := by
  apply nodeValid_prime [2, 3, 5, 11, 2464571] ⟨143142283681, 7, [(2, 5), (3, 1), (5, 1), (11, 2), (2464571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2464571
  · decide +kernel

theorem prime_143142298987 : Nat.Prime 143142298987 := by
  apply nodeValid_prime [2, 3, 23857049831] ⟨143142298987, 2, [(2, 1), (3, 1), (23857049831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23857049831
  · decide +kernel

theorem prime_143491462019 : Nat.Prime 143491462019 := by
  apply nodeValid_prime [2, 73, 647, 1519039] ⟨143491462019, 2, [(2, 1), (73, 1), (647, 1), (1519039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_647
    · exact prime_1519039
  · decide +kernel

theorem prime_143491464929 : Nat.Prime 143491464929 := by
  apply nodeValid_prime [2, 7, 640586897] ⟨143491464929, 3, [(2, 5), (7, 1), (640586897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_640586897
  · decide +kernel

theorem prime_143491465009 : Nat.Prime 143491465009 := by
  apply nodeValid_prime [2, 3, 29, 1272629] ⟨143491465009, 11, [(2, 4), (3, 5), (29, 1), (1272629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1272629
  · decide +kernel

theorem prime_143841205073 : Nat.Prime 143841205073 := by
  apply nodeValid_prime [2, 43, 499, 418981] ⟨143841205073, 5, [(2, 4), (43, 1), (499, 1), (418981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_499
    · exact prime_418981
  · decide +kernel

theorem prime_143841216791 : Nat.Prime 143841216791 := by
  apply nodeValid_prime [2, 5, 17737, 810967] ⟨143841216791, 43, [(2, 1), (5, 1), (17737, 1), (810967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17737
    · exact prime_810967
  · decide +kernel

theorem prime_143841216989 : Nat.Prime 143841216989 := by
  apply nodeValid_prime [2, 7, 23, 1109, 201403] ⟨143841216989, 2, [(2, 2), (7, 1), (23, 1), (1109, 1), (201403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_1109
    · exact prime_201403
  · decide +kernel

theorem prime_144191519543 : Nat.Prime 144191519543 := by
  apply nodeValid_prime [2, 7, 811, 3023, 4201] ⟨144191519543, 5, [(2, 1), (7, 1), (811, 1), (3023, 1), (4201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_811
    · exact prime_3023
    · exact prime_4201
  · decide +kernel

theorem prime_144191520643 : Nat.Prime 144191520643 := by
  apply nodeValid_prime [2, 3, 13, 739, 2501501] ⟨144191520643, 2, [(2, 1), (3, 1), (13, 1), (739, 1), (2501501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_739
    · exact prime_2501501
  · decide +kernel

theorem prime_144191525707 : Nat.Prime 144191525707 := by
  apply nodeValid_prime [2, 3, 109, 24497371] ⟨144191525707, 2, [(2, 1), (3, 3), (109, 1), (24497371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_24497371
  · decide +kernel

theorem prime_144542424739 : Nat.Prime 144542424739 := by
  apply nodeValid_prime [2, 3, 1097, 21960259] ⟨144542424739, 2, [(2, 1), (3, 1), (1097, 1), (21960259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1097
    · exact prime_21960259
  · decide +kernel

theorem prime_144542426591 : Nat.Prime 144542426591 := by
  apply nodeValid_prime [2, 5, 23, 37, 103, 1601] ⟨144542426591, 17, [(2, 1), (5, 1), (23, 1), (37, 1), (103, 2), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_103
    · exact prime_1601
  · decide +kernel

theorem prime_144542427179 : Nat.Prime 144542427179 := by
  apply nodeValid_prime [2, 72271213589] ⟨144542427179, 2, [(2, 1), (72271213589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_72271213589
  · decide +kernel

theorem prime_144893893663 : Nat.Prime 144893893663 := by
  apply nodeValid_prime [2, 3, 7, 43, 424493] ⟨144893893663, 3, [(2, 1), (3, 4), (7, 2), (43, 1), (424493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_424493
  · decide +kernel

theorem prime_144893894269 : Nat.Prime 144893894269 := by
  apply nodeValid_prime [2, 3, 94621, 127609] ⟨144893894269, 6, [(2, 2), (3, 1), (94621, 1), (127609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_94621
    · exact prime_127609
  · decide +kernel

theorem prime_144893898967 : Nat.Prime 144893898967 := by
  apply nodeValid_prime [2, 3, 40423, 597407] ⟨144893898967, 6, [(2, 1), (3, 1), (40423, 1), (597407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40423
    · exact prime_597407
  · decide +kernel

theorem prime_145245947167 : Nat.Prime 145245947167 := by
  apply nodeValid_prime [2, 3, 11953, 675079] ⟨145245947167, 3, [(2, 1), (3, 2), (11953, 1), (675079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11953
    · exact prime_675079
  · decide +kernel

theorem prime_145245950503 : Nat.Prime 145245950503 := by
  apply nodeValid_prime [2, 3, 31, 780892207] ⟨145245950503, 5, [(2, 1), (3, 1), (31, 1), (780892207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_780892207
  · decide +kernel

theorem prime_145245950791 : Nat.Prime 145245950791 := by
  apply nodeValid_prime [2, 3, 5, 1289, 3756037] ⟨145245950791, 3, [(2, 1), (3, 1), (5, 1), (1289, 1), (3756037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1289
    · exact prime_3756037
  · decide +kernel

theorem prime_145598575601 : Nat.Prime 145598575601 := by
  apply nodeValid_prime [2, 5, 13163, 27653] ⟨145598575601, 3, [(2, 4), (5, 2), (13163, 1), (27653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13163
    · exact prime_27653
  · decide +kernel

theorem prime_145598578963 : Nat.Prime 145598578963 := by
  apply nodeValid_prime [2, 3, 619, 39202633] ⟨145598578963, 13, [(2, 1), (3, 1), (619, 1), (39202633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
    · exact prime_39202633
  · decide +kernel

theorem prime_145598579353 : Nat.Prime 145598579353 := by
  apply nodeValid_prime [2, 3, 1949, 345853] ⟨145598579353, 5, [(2, 3), (3, 3), (1949, 1), (345853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1949
    · exact prime_345853
  · decide +kernel

theorem prime_145951783501 : Nat.Prime 145951783501 := by
  apply nodeValid_prime [2, 3, 5, 73, 1332893] ⟨145951783501, 2, [(2, 2), (3, 1), (5, 3), (73, 1), (1332893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_1332893
  · decide +kernel

theorem prime_145951793413 : Nat.Prime 145951793413 := by
  apply nodeValid_prime [2, 3, 9533, 1275847] ⟨145951793413, 2, [(2, 2), (3, 1), (9533, 1), (1275847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9533
    · exact prime_1275847
  · decide +kernel

theorem prime_145951793443 : Nat.Prime 145951793443 := by
  apply nodeValid_prime [2, 3, 7, 13, 37, 601, 4007] ⟨145951793443, 2, [(2, 1), (3, 2), (7, 1), (13, 1), (37, 1), (601, 1), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_601
    · exact prime_4007
  · decide +kernel

theorem prime_146305526707 : Nat.Prime 146305526707 := by
  apply nodeValid_prime [2, 3, 8128084817] ⟨146305526707, 2, [(2, 1), (3, 2), (8128084817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8128084817
  · decide +kernel

theorem prime_146305527107 : Nat.Prime 146305527107 := by
  apply nodeValid_prime [2, 73152763553] ⟨146305527107, 2, [(2, 1), (73152763553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73152763553
  · decide +kernel

theorem prime_146305572157 : Nat.Prime 146305572157 := by
  apply nodeValid_prime [2, 3, 4064043671] ⟨146305572157, 5, [(2, 2), (3, 2), (4064043671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4064043671
  · decide +kernel

theorem prime_146659938947 : Nat.Prime 146659938947 := by
  apply nodeValid_prime [2, 29, 269, 9400073] ⟨146659938947, 2, [(2, 1), (29, 1), (269, 1), (9400073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_269
    · exact prime_9400073
  · decide +kernel

theorem prime_146659938973 : Nat.Prime 146659938973 := by
  apply nodeValid_prime [2, 3, 179, 68277439] ⟨146659938973, 2, [(2, 2), (3, 1), (179, 1), (68277439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_68277439
  · decide +kernel

theorem prime_146659945631 : Nat.Prime 146659945631 := by
  apply nodeValid_prime [2, 5, 11, 43, 31006331] ⟨146659945631, 11, [(2, 1), (5, 1), (11, 1), (43, 1), (31006331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_31006331
  · decide +kernel

theorem prime_147014899727 : Nat.Prime 147014899727 := by
  apply nodeValid_prime [2, 17, 23, 187998593] ⟨147014899727, 5, [(2, 1), (17, 1), (23, 1), (187998593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_187998593
  · decide +kernel

theorem prime_147014903197 : Nat.Prime 147014903197 := by
  apply nodeValid_prime [2, 3, 7, 19, 30704867] ⟨147014903197, 2, [(2, 2), (3, 2), (7, 1), (19, 1), (30704867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_30704867
  · decide +kernel

theorem prime_147014903293 : Nat.Prime 147014903293 := by
  apply nodeValid_prime [2, 3, 12251241941] ⟨147014903293, 5, [(2, 2), (3, 1), (12251241941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12251241941
  · decide +kernel

theorem prime_147370402057 : Nat.Prime 147370402057 := by
  apply nodeValid_prime [2, 3, 9239, 664621] ⟨147370402057, 10, [(2, 3), (3, 1), (9239, 1), (664621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9239
    · exact prime_664621
  · decide +kernel

theorem prime_147370402447 : Nat.Prime 147370402447 := by
  apply nodeValid_prime [2, 3, 23, 14461, 73847] ⟨147370402447, 3, [(2, 1), (3, 1), (23, 1), (14461, 1), (73847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_14461
    · exact prime_73847
  · decide +kernel

theorem prime_147370436593 : Nat.Prime 147370436593 := by
  apply nodeValid_prime [2, 3, 19, 71, 73, 31177] ⟨147370436593, 11, [(2, 4), (3, 1), (19, 1), (71, 1), (73, 1), (31177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_71
    · exact prime_73
    · exact prime_31177
  · decide +kernel

theorem prime_147726548111 : Nat.Prime 147726548111 := by
  apply nodeValid_prime [2, 5, 53891, 274121] ⟨147726548111, 14, [(2, 1), (5, 1), (53891, 1), (274121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53891
    · exact prime_274121
  · decide +kernel

theorem prime_147726548951 : Nat.Prime 147726548951 := by
  apply nodeValid_prime [2, 5, 317, 9320287] ⟨147726548951, 7, [(2, 1), (5, 2), (317, 1), (9320287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_317
    · exact prime_9320287
  · decide +kernel

theorem prime_147726559061 : Nat.Prime 147726559061 := by
  apply nodeValid_prime [2, 5, 17387, 424819] ⟨147726559061, 2, [(2, 2), (5, 1), (17387, 1), (424819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17387
    · exact prime_424819
  · decide +kernel

theorem prime_148083248141 : Nat.Prime 148083248141 := by
  apply nodeValid_prime [2, 5, 41, 180589327] ⟨148083248141, 3, [(2, 2), (5, 1), (41, 1), (180589327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_180589327
  · decide +kernel

theorem prime_148083248267 : Nat.Prime 148083248267 := by
  apply nodeValid_prime [2, 74041624133] ⟨148083248267, 2, [(2, 1), (74041624133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_74041624133
  · decide +kernel

theorem prime_148083264977 : Nat.Prime 148083264977 := by
  apply nodeValid_prime [2, 109, 84910129] ⟨148083264977, 3, [(2, 4), (109, 1), (84910129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_84910129
  · decide +kernel

theorem prime_148440552047 : Nat.Prime 148440552047 := by
  apply nodeValid_prime [2, 19, 47, 83113411] ⟨148440552047, 5, [(2, 1), (19, 1), (47, 1), (83113411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_83113411
  · decide +kernel

theorem prime_148440578093 : Nat.Prime 148440578093 := by
  apply nodeValid_prime [2, 37, 139, 7215661] ⟨148440578093, 2, [(2, 2), (37, 1), (139, 1), (7215661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_139
    · exact prime_7215661
  · decide +kernel

theorem prime_148440581243 : Nat.Prime 148440581243 := by
  apply nodeValid_prime [2, 4523, 16409527] ⟨148440581243, 2, [(2, 1), (4523, 1), (16409527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4523
    · exact prime_16409527
  · decide +kernel

theorem prime_148798423783 : Nat.Prime 148798423783 := by
  apply nodeValid_prime [2, 3, 853, 9691183] ⟨148798423783, 7, [(2, 1), (3, 2), (853, 1), (9691183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853
    · exact prime_9691183
  · decide +kernel

theorem prime_148798441579 : Nat.Prime 148798441579 := by
  apply nodeValid_prime [2, 3, 89, 278648767] ⟨148798441579, 2, [(2, 1), (3, 1), (89, 1), (278648767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_278648767
  · decide +kernel

theorem prime_148798442081 : Nat.Prime 148798442081 := by
  apply nodeValid_prime [2, 5, 421, 2209003] ⟨148798442081, 3, [(2, 5), (5, 1), (421, 1), (2209003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_421
    · exact prime_2209003
  · decide +kernel

theorem prime_149156873729 : Nat.Prime 149156873729 := by
  apply nodeValid_prime [2, 271, 1074989] ⟨149156873729, 3, [(2, 9), (271, 1), (1074989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_1074989
  · decide +kernel

theorem prime_149156874743 : Nat.Prime 149156874743 := by
  apply nodeValid_prime [2, 9007, 8280053] ⟨149156874743, 5, [(2, 1), (9007, 1), (8280053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9007
    · exact prime_8280053
  · decide +kernel

theorem prime_149156880283 : Nat.Prime 149156880283 := by
  apply nodeValid_prime [2, 3, 223, 37159163] ⟨149156880283, 2, [(2, 1), (3, 2), (223, 1), (37159163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_37159163
  · decide +kernel

end Sude.Lucas.Generated
