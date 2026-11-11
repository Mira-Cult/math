import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0076

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7963 : Nat.Prime 7963 := by
  apply nodeValid_prime [2, 3, 1327] ⟨7963, 5, [(2, 1), (3, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1327
  · decide +kernel

theorem prime_8291 : Nat.Prime 8291 := by
  apply nodeValid_prime [2, 5, 829] ⟨8291, 2, [(2, 1), (5, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_829
  · decide +kernel

theorem prime_14293 : Nat.Prime 14293 := by
  apply nodeValid_prime [2, 3, 397] ⟨14293, 6, [(2, 2), (3, 2), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
  · decide +kernel

theorem prime_14771 : Nat.Prime 14771 := by
  apply nodeValid_prime [2, 5, 7, 211] ⟨14771, 2, [(2, 1), (5, 1), (7, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_211
  · decide +kernel

theorem prime_18181 : Nat.Prime 18181 := by
  apply nodeValid_prime [2, 3, 5, 101] ⟨18181, 2, [(2, 2), (3, 2), (5, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_19139 : Nat.Prime 19139 := by
  apply nodeValid_prime [2, 7, 1367] ⟨19139, 2, [(2, 1), (7, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1367
  · decide +kernel

theorem prime_21163 : Nat.Prime 21163 := by
  apply nodeValid_prime [2, 3, 3527] ⟨21163, 2, [(2, 1), (3, 1), (3527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3527
  · decide +kernel

theorem prime_25169 : Nat.Prime 25169 := by
  apply nodeValid_prime [2, 11, 13] ⟨25169, 3, [(2, 4), (11, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_27449 : Nat.Prime 27449 := by
  apply nodeValid_prime [2, 47, 73] ⟨27449, 3, [(2, 3), (47, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_73
  · decide +kernel

theorem prime_36919 : Nat.Prime 36919 := by
  apply nodeValid_prime [2, 3, 7, 293] ⟨36919, 3, [(2, 1), (3, 2), (7, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_293
  · decide +kernel

theorem prime_48799 : Nat.Prime 48799 := by
  apply nodeValid_prime [2, 3, 2711] ⟨48799, 3, [(2, 1), (3, 2), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2711
  · decide +kernel

theorem prime_49919 : Nat.Prime 49919 := by
  apply nodeValid_prime [2, 11, 2269] ⟨49919, 7, [(2, 1), (11, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2269
  · decide +kernel

theorem prime_67757 : Nat.Prime 67757 := by
  apply nodeValid_prime [2, 13, 1303] ⟨67757, 3, [(2, 2), (13, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1303
  · decide +kernel

theorem prime_70879 : Nat.Prime 70879 := by
  apply nodeValid_prime [2, 3, 11813] ⟨70879, 3, [(2, 1), (3, 1), (11813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11813
  · decide +kernel

theorem prime_79631 : Nat.Prime 79631 := by
  apply nodeValid_prime [2, 5, 7963] ⟨79631, 13, [(2, 1), (5, 1), (7963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7963
  · decide +kernel

theorem prime_82613 : Nat.Prime 82613 := by
  apply nodeValid_prime [2, 19, 1087] ⟨82613, 2, [(2, 2), (19, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1087
  · decide +kernel

theorem prime_87853 : Nat.Prime 87853 := by
  apply nodeValid_prime [2, 3, 7321] ⟨87853, 2, [(2, 2), (3, 1), (7321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7321
  · decide +kernel

theorem prime_99839 : Nat.Prime 99839 := by
  apply nodeValid_prime [2, 49919] ⟨99839, 11, [(2, 1), (49919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49919
  · decide +kernel

theorem prime_105761 : Nat.Prime 105761 := by
  apply nodeValid_prime [2, 5, 661] ⟨105761, 3, [(2, 5), (5, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_661
  · decide +kernel

theorem prime_107581 : Nat.Prime 107581 := by
  apply nodeValid_prime [2, 3, 5, 11, 163] ⟨107581, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_163
  · decide +kernel

theorem prime_112181 : Nat.Prime 112181 := by
  apply nodeValid_prime [2, 5, 71, 79] ⟨112181, 2, [(2, 2), (5, 1), (71, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_79
  · decide +kernel

theorem prime_112429 : Nat.Prime 112429 := by
  apply nodeValid_prime [2, 3, 347] ⟨112429, 6, [(2, 2), (3, 4), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
  · decide +kernel

theorem prime_154291 : Nat.Prime 154291 := by
  apply nodeValid_prime [2, 3, 5, 37, 139] ⟨154291, 3, [(2, 1), (3, 1), (5, 1), (37, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_139
  · decide +kernel

theorem prime_169591 : Nat.Prime 169591 := by
  apply nodeValid_prime [2, 3, 5, 5653] ⟨169591, 6, [(2, 1), (3, 1), (5, 1), (5653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5653
  · decide +kernel

theorem prime_209717 : Nat.Prime 209717 := by
  apply nodeValid_prime [2, 13, 37, 109] ⟨209717, 2, [(2, 2), (13, 1), (37, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_109
  · decide +kernel

theorem prime_224363 : Nat.Prime 224363 := by
  apply nodeValid_prime [2, 112181] ⟨224363, 2, [(2, 1), (112181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_112181
  · decide +kernel

theorem prime_233851 : Nat.Prime 233851 := by
  apply nodeValid_prime [2, 3, 5, 1559] ⟨233851, 2, [(2, 1), (3, 1), (5, 2), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1559
  · decide +kernel

theorem prime_280639 : Nat.Prime 280639 := by
  apply nodeValid_prime [2, 3, 5197] ⟨280639, 6, [(2, 1), (3, 3), (5197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5197
  · decide +kernel

theorem prime_326141 : Nat.Prime 326141 := by
  apply nodeValid_prime [2, 5, 23, 709] ⟨326141, 2, [(2, 2), (5, 1), (23, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_709
  · decide +kernel

theorem prime_357349 : Nat.Prime 357349 := by
  apply nodeValid_prime [2, 3, 97, 307] ⟨357349, 2, [(2, 2), (3, 1), (97, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_307
  · decide +kernel

theorem prime_415153 : Nat.Prime 415153 := by
  apply nodeValid_prime [2, 3, 31] ⟨415153, 5, [(2, 4), (3, 3), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_438517 : Nat.Prime 438517 := by
  apply nodeValid_prime [2, 3, 13, 937] ⟨438517, 5, [(2, 2), (3, 2), (13, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_937
  · decide +kernel

theorem prime_440383 : Nat.Prime 440383 := by
  apply nodeValid_prime [2, 3, 19, 3863] ⟨440383, 3, [(2, 1), (3, 1), (19, 1), (3863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3863
  · decide +kernel

theorem prime_448727 : Nat.Prime 448727 := by
  apply nodeValid_prime [2, 224363] ⟨448727, 5, [(2, 1), (224363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_224363
  · decide +kernel

theorem prime_451933 : Nat.Prime 451933 := by
  apply nodeValid_prime [2, 3, 13, 2897] ⟨451933, 5, [(2, 2), (3, 1), (13, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2897
  · decide +kernel

theorem prime_462899 : Nat.Prime 462899 := by
  apply nodeValid_prime [2, 23, 29, 347] ⟨462899, 2, [(2, 1), (23, 1), (29, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_347
  · decide +kernel

theorem prime_471061 : Nat.Prime 471061 := by
  apply nodeValid_prime [2, 3, 5, 2617] ⟨471061, 2, [(2, 2), (3, 2), (5, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2617
  · decide +kernel

theorem prime_531613 : Nat.Prime 531613 := by
  apply nodeValid_prime [2, 3, 14767] ⟨531613, 2, [(2, 2), (3, 2), (14767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14767
  · decide +kernel

theorem prime_614527 : Nat.Prime 614527 := by
  apply nodeValid_prime [2, 3, 11, 9311] ⟨614527, 3, [(2, 1), (3, 1), (11, 1), (9311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9311
  · decide +kernel

theorem prime_714113 : Nat.Prime 714113 := by
  apply nodeValid_prime [2, 7, 797] ⟨714113, 3, [(2, 7), (7, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_797
  · decide +kernel

theorem prime_1068241 : Nat.Prime 1068241 := by
  apply nodeValid_prime [2, 3, 5, 4451] ⟨1068241, 7, [(2, 4), (3, 1), (5, 1), (4451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4451
  · decide +kernel

theorem prime_1107781 : Nat.Prime 1107781 := by
  apply nodeValid_prime [2, 3, 5, 37, 499] ⟨1107781, 6, [(2, 2), (3, 1), (5, 1), (37, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_499
  · decide +kernel

theorem prime_1150973 : Nat.Prime 1150973 := by
  apply nodeValid_prime [2, 59, 4877] ⟨1150973, 2, [(2, 2), (59, 1), (4877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_4877
  · decide +kernel

theorem prime_1265233 : Nat.Prime 1265233 := by
  apply nodeValid_prime [2, 3, 43, 613] ⟨1265233, 5, [(2, 4), (3, 1), (43, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_613
  · decide +kernel

theorem prime_1490843 : Nat.Prime 1490843 := by
  apply nodeValid_prime [2, 41, 18181] ⟨1490843, 2, [(2, 1), (41, 1), (18181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_18181
  · decide +kernel

theorem prime_1578361 : Nat.Prime 1578361 := by
  apply nodeValid_prime [2, 3, 5, 7, 1879] ⟨1578361, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (1879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1879
  · decide +kernel

theorem prime_1633991 : Nat.Prime 1633991 := by
  apply nodeValid_prime [2, 5, 53, 3083] ⟨1633991, 7, [(2, 1), (5, 1), (53, 1), (3083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_3083
  · decide +kernel

theorem prime_1906321 : Nat.Prime 1906321 := by
  apply nodeValid_prime [2, 3, 5, 13, 47] ⟨1906321, 19, [(2, 4), (3, 1), (5, 1), (13, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_2115221 : Nat.Prime 2115221 := by
  apply nodeValid_prime [2, 5, 105761] ⟨2115221, 2, [(2, 2), (5, 1), (105761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_105761
  · decide +kernel

theorem prime_2297969 : Nat.Prime 2297969 := by
  apply nodeValid_prime [2, 31, 41, 113] ⟨2297969, 3, [(2, 4), (31, 1), (41, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41
    · exact prime_113
  · decide +kernel

theorem prime_2692363 : Nat.Prime 2692363 := by
  apply nodeValid_prime [2, 3, 448727] ⟨2692363, 2, [(2, 1), (3, 1), (448727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_448727
  · decide +kernel

theorem prime_2801509 : Nat.Prime 2801509 := by
  apply nodeValid_prime [2, 3, 157, 1487] ⟨2801509, 6, [(2, 2), (3, 1), (157, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_1487
  · decide +kernel

theorem prime_3731003 : Nat.Prime 3731003 := by
  apply nodeValid_prime [2, 11, 169591] ⟨3731003, 2, [(2, 1), (11, 1), (169591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_169591
  · decide +kernel

theorem prime_3737579 : Nat.Prime 3737579 := by
  apply nodeValid_prime [2, 13, 29, 4957] ⟨3737579, 2, [(2, 1), (13, 1), (29, 1), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_4957
  · decide +kernel

theorem prime_7015531 : Nat.Prime 7015531 := by
  apply nodeValid_prime [2, 3, 5, 233851] ⟨7015531, 3, [(2, 1), (3, 1), (5, 1), (233851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233851
  · decide +kernel

theorem prime_7475159 : Nat.Prime 7475159 := by
  apply nodeValid_prime [2, 3737579] ⟨7475159, 29, [(2, 1), (3737579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3737579
  · decide +kernel

theorem prime_8203963 : Nat.Prime 8203963 := by
  apply nodeValid_prime [2, 3, 13, 17, 23, 269] ⟨8203963, 3, [(2, 1), (3, 1), (13, 1), (17, 1), (23, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_23
    · exact prime_269
  · decide +kernel

theorem prime_8505481 : Nat.Prime 8505481 := by
  apply nodeValid_prime [2, 3, 5, 70879] ⟨8505481, 7, [(2, 3), (3, 1), (5, 1), (70879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_70879
  · decide +kernel

theorem prime_12383149 : Nat.Prime 12383149 := by
  apply nodeValid_prime [2, 3, 41, 25169] ⟨12383149, 2, [(2, 2), (3, 1), (41, 1), (25169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_25169
  · decide +kernel

theorem prime_13190119 : Nat.Prime 13190119 := by
  apply nodeValid_prime [2, 3, 199, 11047] ⟨13190119, 3, [(2, 1), (3, 1), (199, 1), (11047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_11047
  · decide +kernel

theorem prime_16888681 : Nat.Prime 16888681 := by
  apply nodeValid_prime [2, 3, 5, 43, 1091] ⟨16888681, 7, [(2, 3), (3, 2), (5, 1), (43, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_1091
  · decide +kernel

theorem prime_20346061 : Nat.Prime 20346061 := by
  apply nodeValid_prime [2, 3, 5, 7, 193, 251] ⟨20346061, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (193, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_193
    · exact prime_251
  · decide +kernel

theorem prime_24367087 : Nat.Prime 24367087 := by
  apply nodeValid_prime [2, 3, 17, 79631] ⟨24367087, 3, [(2, 1), (3, 2), (17, 1), (79631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_79631
  · decide +kernel

theorem prime_26680439 : Nat.Prime 26680439 := by
  apply nodeValid_prime [2, 1609, 8291] ⟨26680439, 7, [(2, 1), (1609, 1), (8291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1609
    · exact prime_8291
  · decide +kernel

theorem prime_26895251 : Nat.Prime 26895251 := by
  apply nodeValid_prime [2, 5, 107581] ⟨26895251, 2, [(2, 1), (5, 3), (107581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107581
  · decide +kernel

theorem prime_27835127 : Nat.Prime 27835127 := by
  apply nodeValid_prime [2, 11, 1265233] ⟨27835127, 5, [(2, 1), (11, 1), (1265233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1265233
  · decide +kernel

theorem prime_32664311 : Nat.Prime 32664311 := by
  apply nodeValid_prime [2, 5, 7, 17, 27449] ⟨32664311, 7, [(2, 1), (5, 1), (7, 1), (17, 1), (27449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_27449
  · decide +kernel

theorem prime_39094087 : Nat.Prime 39094087 := by
  apply nodeValid_prime [2, 3, 571, 11411] ⟨39094087, 3, [(2, 1), (3, 1), (571, 1), (11411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
    · exact prime_11411
  · decide +kernel

theorem prime_40424243 : Nat.Prime 40424243 := by
  apply nodeValid_prime [2, 131, 154291] ⟨40424243, 2, [(2, 1), (131, 1), (154291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_154291
  · decide +kernel

theorem prime_44856989 : Nat.Prime 44856989 := by
  apply nodeValid_prime [2, 11, 47, 109, 199] ⟨44856989, 2, [(2, 2), (11, 1), (47, 1), (109, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_109
    · exact prime_199
  · decide +kernel

theorem prime_45859267 : Nat.Prime 45859267 := by
  apply nodeValid_prime [2, 3, 29, 87853] ⟨45859267, 2, [(2, 1), (3, 2), (29, 1), (87853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_87853
  · decide +kernel

theorem prime_56258777 : Nat.Prime 56258777 := by
  apply nodeValid_prime [2, 7, 137, 7333] ⟨56258777, 3, [(2, 3), (7, 1), (137, 1), (7333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_7333
  · decide +kernel

theorem prime_63319427 : Nat.Prime 63319427 := by
  apply nodeValid_prime [2, 2027, 15619] ⟨63319427, 2, [(2, 1), (2027, 1), (15619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2027
    · exact prime_15619
  · decide +kernel

theorem prime_64139849 : Nat.Prime 64139849 := by
  apply nodeValid_prime [2, 101, 163, 487] ⟨64139849, 3, [(2, 3), (101, 1), (163, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_163
    · exact prime_487
  · decide +kernel

theorem prime_122881351 : Nat.Prime 122881351 := by
  apply nodeValid_prime [2, 3, 5, 67, 12227] ⟨122881351, 3, [(2, 1), (3, 1), (5, 2), (67, 1), (12227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_12227
  · decide +kernel

theorem prime_132311077 : Nat.Prime 132311077 := by
  apply nodeValid_prime [2, 3, 521, 21163] ⟨132311077, 2, [(2, 2), (3, 1), (521, 1), (21163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_21163
  · decide +kernel

theorem prime_137970473 : Nat.Prime 137970473 := by
  apply nodeValid_prime [2, 97, 177797] ⟨137970473, 3, [(2, 3), (97, 1), (177797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_177797
  · decide +kernel

theorem prime_140348347 : Nat.Prime 140348347 := by
  apply nodeValid_prime [2, 3, 23, 31, 53, 619] ⟨140348347, 2, [(2, 1), (3, 1), (23, 1), (31, 1), (53, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_31
    · exact prime_53
    · exact prime_619
  · decide +kernel

theorem prime_185507851 : Nat.Prime 185507851 := by
  apply nodeValid_prime [2, 3, 5, 11, 112429] ⟨185507851, 2, [(2, 1), (3, 1), (5, 2), (11, 1), (112429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_112429
  · decide +kernel

theorem prime_202664173 : Nat.Prime 202664173 := by
  apply nodeValid_prime [2, 3, 16888681] ⟨202664173, 2, [(2, 2), (3, 1), (16888681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16888681
  · decide +kernel

theorem prime_283881343 : Nat.Prime 283881343 := by
  apply nodeValid_prime [2, 3, 89, 531613] ⟨283881343, 3, [(2, 1), (3, 1), (89, 1), (531613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_531613
  · decide +kernel

theorem prime_312515479 : Nat.Prime 312515479 := by
  apply nodeValid_prime [2, 3, 11, 1578361] ⟨312515479, 3, [(2, 1), (3, 2), (11, 1), (1578361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1578361
  · decide +kernel

theorem prime_371361847 : Nat.Prime 371361847 := by
  apply nodeValid_prime [2, 3, 41, 43, 35107] ⟨371361847, 3, [(2, 1), (3, 1), (41, 1), (43, 1), (35107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_43
    · exact prime_35107
  · decide +kernel

theorem prime_564977599 : Nat.Prime 564977599 := by
  apply nodeValid_prime [2, 3, 449, 209717] ⟨564977599, 3, [(2, 1), (3, 1), (449, 1), (209717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
    · exact prime_209717
  · decide +kernel

theorem prime_813842441 : Nat.Prime 813842441 := by
  apply nodeValid_prime [2, 5, 20346061] ⟨813842441, 3, [(2, 3), (5, 1), (20346061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20346061
  · decide +kernel

theorem prime_883956581 : Nat.Prime 883956581 := by
  apply nodeValid_prime [2, 5, 13, 941, 3613] ⟨883956581, 2, [(2, 2), (5, 1), (13, 1), (941, 1), (3613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_941
    · exact prime_3613
  · decide +kernel

theorem prime_1133682887 : Nat.Prime 1133682887 := by
  apply nodeValid_prime [2, 7, 37, 277, 7901] ⟨1133682887, 5, [(2, 1), (7, 1), (37, 1), (277, 1), (7901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_277
    · exact prime_7901
  · decide +kernel

theorem prime_1135525373 : Nat.Prime 1135525373 := by
  apply nodeValid_prime [2, 283881343] ⟨1135525373, 2, [(2, 2), (283881343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_283881343
  · decide +kernel

theorem prime_1462728203 : Nat.Prime 1462728203 := by
  apply nodeValid_prime [2, 13, 56258777] ⟨1462728203, 2, [(2, 1), (13, 1), (56258777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_56258777
  · decide +kernel

theorem prime_1672578367 : Nat.Prime 1672578367 := by
  apply nodeValid_prime [2, 3, 307, 727, 1249] ⟨1672578367, 6, [(2, 1), (3, 1), (307, 1), (727, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_727
    · exact prime_1249
  · decide +kernel

theorem prime_3470236249 : Nat.Prime 3470236249 := by
  apply nodeValid_prime [2, 3, 17, 8505481] ⟨3470236249, 11, [(2, 3), (3, 1), (17, 1), (8505481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8505481
  · decide +kernel

theorem prime_4010403203 : Nat.Prime 4010403203 := by
  apply nodeValid_prime [2, 13, 251, 614527] ⟨4010403203, 2, [(2, 1), (13, 1), (251, 1), (614527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_251
    · exact prime_614527
  · decide +kernel

theorem prime_4607696647 : Nat.Prime 4607696647 := by
  apply nodeValid_prime [2, 3, 7, 79, 462899] ⟨4607696647, 19, [(2, 1), (3, 2), (7, 1), (79, 1), (462899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_462899
  · decide +kernel

theorem prime_7534960273 : Nat.Prime 7534960273 := by
  apply nodeValid_prime [2, 3, 7, 7475159] ⟨7534960273, 5, [(2, 4), (3, 2), (7, 1), (7475159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7475159
  · decide +kernel

theorem prime_8020806407 : Nat.Prime 8020806407 := by
  apply nodeValid_prime [2, 4010403203] ⟨8020806407, 5, [(2, 1), (4010403203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4010403203
  · decide +kernel

theorem prime_11458294871 : Nat.Prime 11458294871 := by
  apply nodeValid_prime [2, 5, 11, 9043, 11519] ⟨11458294871, 14, [(2, 1), (5, 1), (11, 1), (9043, 1), (11519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_9043
    · exact prime_11519
  · decide +kernel

theorem prime_16126392511 : Nat.Prime 16126392511 := by
  apply nodeValid_prime [2, 3, 5, 31, 1259, 4591] ⟨16126392511, 6, [(2, 1), (3, 2), (5, 1), (31, 1), (1259, 1), (4591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1259
    · exact prime_4591
  · decide +kernel

theorem prime_36139273243 : Nat.Prime 36139273243 := by
  apply nodeValid_prime [2, 3, 149, 40424243] ⟨36139273243, 13, [(2, 1), (3, 1), (149, 1), (40424243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_40424243
  · decide +kernel

theorem prime_37058180023 : Nat.Prime 37058180023 := by
  apply nodeValid_prime [2, 3, 31, 714113] ⟨37058180023, 5, [(2, 1), (3, 3), (31, 2), (714113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_714113
  · decide +kernel

theorem prime_42201931543 : Nat.Prime 42201931543 := by
  apply nodeValid_prime [2, 3, 71, 353, 280639] ⟨42201931543, 5, [(2, 1), (3, 1), (71, 1), (353, 1), (280639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_353
    · exact prime_280639
  · decide +kernel

theorem prime_42468946111 : Nat.Prime 42468946111 := by
  apply nodeValid_prime [2, 3, 5, 19, 53, 8221] ⟨42468946111, 3, [(2, 1), (3, 3), (5, 1), (19, 2), (53, 1), (8221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_53
    · exact prime_8221
  · decide +kernel

theorem prime_46172542331 : Nat.Prime 46172542331 := by
  apply nodeValid_prime [2, 5, 103, 449, 99839] ⟨46172542331, 2, [(2, 1), (5, 1), (103, 1), (449, 1), (99839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_449
    · exact prime_99839
  · decide +kernel

theorem prime_70284563389 : Nat.Prime 70284563389 := by
  apply nodeValid_prime [2, 3, 13, 71, 2115221] ⟨70284563389, 2, [(2, 2), (3, 2), (13, 1), (71, 1), (2115221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_2115221
  · decide +kernel

theorem prime_109217044021 : Nat.Prime 109217044021 := by
  apply nodeValid_prime [2, 3, 5, 7, 593, 438517] ⟨109217044021, 13, [(2, 2), (3, 1), (5, 1), (7, 1), (593, 1), (438517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_593
    · exact prime_438517
  · decide +kernel

theorem prime_120566165017 : Nat.Prime 120566165017 := by
  apply nodeValid_prime [2, 3, 11, 233, 541, 3623] ⟨120566165017, 5, [(2, 3), (3, 1), (11, 1), (233, 1), (541, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_233
    · exact prime_541
    · exact prime_3623
  · decide +kernel

theorem prime_161433854269 : Nat.Prime 161433854269 := by
  apply nodeValid_prime [2, 3, 83, 10973, 14771] ⟨161433854269, 6, [(2, 2), (3, 1), (83, 1), (10973, 1), (14771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_10973
    · exact prime_14771
  · decide +kernel

theorem prime_196796779117 : Nat.Prime 196796779117 := by
  apply nodeValid_prime [2, 3, 7, 37, 63319427] ⟨196796779117, 2, [(2, 2), (3, 1), (7, 1), (37, 1), (63319427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_63319427
  · decide +kernel

theorem prime_329026596443 : Nat.Prime 329026596443 := by
  apply nodeValid_prime [2, 443, 371361847] ⟨329026596443, 2, [(2, 1), (443, 1), (371361847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_371361847
  · decide +kernel

theorem prime_971666149721 : Nat.Prime 971666149721 := by
  apply nodeValid_prime [2, 5, 7, 3470236249] ⟨971666149721, 3, [(2, 3), (5, 1), (7, 1), (3470236249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3470236249
  · decide +kernel

theorem prime_972688600973 : Nat.Prime 972688600973 := by
  apply nodeValid_prime [2, 11, 157, 6421, 21929] ⟨972688600973, 3, [(2, 2), (11, 1), (157, 1), (6421, 1), (21929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_157
    · exact prime_6421
    · exact prime_21929
  · decide +kernel

theorem prime_980894597321 : Nat.Prime 980894597321 := by
  apply nodeValid_prime [2, 5, 11, 202664173] ⟨980894597321, 3, [(2, 3), (5, 1), (11, 2), (202664173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_202664173
  · decide +kernel

theorem prime_981923635019 : Nat.Prime 981923635019 := by
  apply nodeValid_prime [2, 1571, 312515479] ⟨981923635019, 2, [(2, 1), (1571, 1), (312515479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1571
    · exact prime_312515479
  · decide +kernel

theorem prime_986047082459 : Nat.Prime 986047082459 := by
  apply nodeValid_prime [2, 107, 4607696647] ⟨986047082459, 2, [(2, 1), (107, 1), (4607696647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_4607696647
  · decide +kernel

theorem prime_1924993537681 : Nat.Prime 1924993537681 := by
  apply nodeValid_prime [2, 3, 5, 8020806407] ⟨1924993537681, 19, [(2, 4), (3, 1), (5, 1), (8020806407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8020806407
  · decide +kernel

theorem prime_1924993538329 : Nat.Prime 1924993538329 := by
  apply nodeValid_prime [2, 3, 7, 11458294871] ⟨1924993538329, 17, [(2, 3), (3, 1), (7, 1), (11458294871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11458294871
  · decide +kernel

theorem prime_1924993542127 : Nat.Prime 1924993542127 := by
  apply nodeValid_prime [2, 3, 283, 1133682887] ⟨1924993542127, 3, [(2, 1), (3, 1), (283, 1), (1133682887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1133682887
  · decide +kernel

theorem prime_1927025346383 : Nat.Prime 1927025346383 := by
  apply nodeValid_prime [2, 7841, 122881351] ⟨1927025346383, 5, [(2, 1), (7841, 1), (122881351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7841
    · exact prime_122881351
  · decide +kernel

theorem prime_1927025346581 : Nat.Prime 1927025346581 := by
  apply nodeValid_prime [2, 5, 109, 883956581] ⟨1927025346581, 2, [(2, 2), (5, 1), (109, 1), (883956581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_883956581
  · decide +kernel

theorem prime_1927025361197 : Nat.Prime 1927025361197 := by
  apply nodeValid_prime [2, 13, 37058180023] ⟨1927025361197, 2, [(2, 2), (13, 1), (37058180023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37058180023
  · decide +kernel

theorem prime_1929058628929 : Nat.Prime 1929058628929 := by
  apply nodeValid_prime [2, 3, 257, 39094087] ⟨1929058628929, 14, [(2, 6), (3, 1), (257, 1), (39094087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_39094087
  · decide +kernel

theorem prime_1929058629301 : Nat.Prime 1929058629301 := by
  apply nodeValid_prime [2, 3, 5, 11, 48799] ⟨1929058629301, 2, [(2, 2), (3, 3), (5, 2), (11, 4), (48799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_48799
  · decide +kernel

theorem prime_1929058640273 : Nat.Prime 1929058640273 := by
  apply nodeValid_prime [2, 120566165017] ⟨1929058640273, 3, [(2, 4), (120566165017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120566165017
  · decide +kernel

theorem prime_1931093376451 : Nat.Prime 1931093376451 := by
  apply nodeValid_prime [2, 3, 5, 7, 41, 44856989] ⟨1931093376451, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (41, 1), (44856989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_44856989
  · decide +kernel

theorem prime_1931093433383 : Nat.Prime 1931093433383 := by
  apply nodeValid_prime [2, 1709, 564977599] ⟨1931093433383, 5, [(2, 1), (1709, 1), (564977599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1709
    · exact prime_564977599
  · decide +kernel

theorem prime_1931093439413 : Nat.Prime 1931093439413 := by
  apply nodeValid_prime [2, 451933, 1068241] ⟨1931093439413, 2, [(2, 2), (451933, 1), (1068241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_451933
    · exact prime_1068241
  · decide +kernel

theorem prime_1933129567051 : Nat.Prime 1933129567051 := by
  apply nodeValid_prime [2, 3, 5, 11, 167, 7015531] ⟨1933129567051, 3, [(2, 1), (3, 1), (5, 2), (11, 1), (167, 1), (7015531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_167
    · exact prime_7015531
  · decide +kernel

theorem prime_1933129602559 : Nat.Prime 1933129602559 := by
  apply nodeValid_prime [2, 3, 7, 11, 457, 435997] ⟨1933129602559, 3, [(2, 1), (3, 2), (7, 2), (11, 1), (457, 1), (435997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_457
    · exact prime_435997
  · decide +kernel

theorem prime_1933129604027 : Nat.Prime 1933129604027 := by
  apply nodeValid_prime [2, 653, 19139, 77339] ⟨1933129604027, 2, [(2, 1), (653, 1), (19139, 1), (77339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_653
    · exact prime_19139
    · exact prime_77339
  · decide +kernel

theorem prime_1935167099953 : Nat.Prime 1935167099953 := by
  apply nodeValid_prime [2, 3, 1499, 26895251] ⟨1935167099953, 5, [(2, 4), (3, 1), (1499, 1), (26895251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1499
    · exact prime_26895251
  · decide +kernel

theorem prime_1935167101321 : Nat.Prime 1935167101321 := by
  apply nodeValid_prime [2, 3, 5, 16126392511] ⟨1935167101321, 19, [(2, 3), (3, 1), (5, 1), (16126392511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16126392511
  · decide +kernel

theorem prime_1935167200367 : Nat.Prime 1935167200367 := by
  apply nodeValid_prime [2, 59, 1999, 8203963] ⟨1935167200367, 5, [(2, 1), (59, 1), (1999, 1), (8203963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_1999
    · exact prime_8203963
  · decide +kernel

theorem prime_1937206250753 : Nat.Prime 1937206250753 := by
  apply nodeValid_prime [2, 37, 89, 2297969] ⟨1937206250753, 3, [(2, 8), (37, 1), (89, 1), (2297969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_89
    · exact prime_2297969
  · decide +kernel

theorem prime_1937206251229 : Nat.Prime 1937206251229 := by
  apply nodeValid_prime [2, 3, 161433854269] ⟨1937206251229, 2, [(2, 2), (3, 1), (161433854269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_161433854269
  · decide +kernel

theorem prime_1937206286339 : Nat.Prime 1937206286339 := by
  apply nodeValid_prime [2, 853, 1135525373] ⟨1937206286339, 2, [(2, 1), (853, 1), (1135525373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_853
    · exact prime_1135525373
  · decide +kernel

theorem prime_1939246777903 : Nat.Prime 1939246777903 := by
  apply nodeValid_prime [2, 3, 7, 46172542331] ⟨1939246777903, 29, [(2, 1), (3, 1), (7, 1), (46172542331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_46172542331
  · decide +kernel

theorem prime_1939246779359 : Nat.Prime 1939246779359 := by
  apply nodeValid_prime [2, 7, 227, 1871, 326141] ⟨1939246779359, 7, [(2, 1), (7, 1), (227, 1), (1871, 1), (326141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
    · exact prime_1871
    · exact prime_326141
  · decide +kernel

theorem prime_1939246830797 : Nat.Prime 1939246830797 := by
  apply nodeValid_prime [2, 11, 17, 37, 47, 1490843] ⟨1939246830797, 3, [(2, 2), (11, 1), (17, 1), (37, 1), (47, 1), (1490843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_37
    · exact prime_47
    · exact prime_1490843
  · decide +kernel

theorem prime_1941288837601 : Nat.Prime 1941288837601 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 457, 8719] ⟨1941288837601, 34, [(2, 5), (3, 1), (5, 2), (7, 1), (29, 1), (457, 1), (8719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_457
    · exact prime_8719
  · decide +kernel

theorem prime_1941288850979 : Nat.Prime 1941288850979 := by
  apply nodeValid_prime [2, 23, 42201931543] ⟨1941288850979, 2, [(2, 1), (23, 1), (42201931543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_42201931543
  · decide +kernel

theorem prime_1941288852497 : Nat.Prime 1941288852497 := by
  apply nodeValid_prime [2, 7, 23, 269, 2801509] ⟨1941288852497, 5, [(2, 4), (7, 1), (23, 1), (269, 1), (2801509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_269
    · exact prime_2801509
  · decide +kernel

theorem prime_1943332298393 : Nat.Prime 1943332298393 := by
  apply nodeValid_prime [2, 5297, 45859267] ⟨1943332298393, 3, [(2, 3), (5297, 1), (45859267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5297
    · exact prime_45859267
  · decide +kernel

theorem prime_1943332299443 : Nat.Prime 1943332299443 := by
  apply nodeValid_prime [2, 971666149721] ⟨1943332299443, 2, [(2, 1), (971666149721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_971666149721
  · decide +kernel

theorem prime_1945377201947 : Nat.Prime 1945377201947 := by
  apply nodeValid_prime [2, 972688600973] ⟨1945377201947, 2, [(2, 1), (972688600973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_972688600973
  · decide +kernel

theorem prime_1945377202589 : Nat.Prime 1945377202589 := by
  apply nodeValid_prime [2, 887, 6637, 82613] ⟨1945377202589, 2, [(2, 2), (887, 1), (6637, 1), (82613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_887
    · exact prime_6637
    · exact prime_82613
  · decide +kernel

theorem prime_1945377223987 : Nat.Prime 1945377223987 := by
  apply nodeValid_prime [2, 3, 7, 227, 571, 357349] ⟨1945377223987, 2, [(2, 1), (3, 1), (7, 1), (227, 1), (571, 1), (357349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_227
    · exact prime_571
    · exact prime_357349
  · decide +kernel

theorem prime_1947423540809 : Nat.Prime 1947423540809 := by
  apply nodeValid_prime [2, 19, 617, 3023, 6869] ⟨1947423540809, 3, [(2, 3), (19, 1), (617, 1), (3023, 1), (6869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_617
    · exact prime_3023
    · exact prime_6869
  · decide +kernel

theorem prime_1947423544337 : Nat.Prime 1947423544337 := by
  apply nodeValid_prime [2, 9829, 12383149] ⟨1947423544337, 3, [(2, 4), (9829, 1), (12383149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9829
    · exact prime_12383149
  · decide +kernel

theorem prime_1947423608951 : Nat.Prime 1947423608951 := by
  apply nodeValid_prime [2, 5, 35159, 1107781] ⟨1947423608951, 7, [(2, 1), (5, 2), (35159, 1), (1107781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_35159
    · exact prime_1107781
  · decide +kernel

theorem prime_1949471408519 : Nat.Prime 1949471408519 := by
  apply nodeValid_prime [2, 53, 139, 132311077] ⟨1949471408519, 13, [(2, 1), (53, 1), (139, 1), (132311077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_139
    · exact prime_132311077
  · decide +kernel

theorem prime_1949471409103 : Nat.Prime 1949471409103 := by
  apply nodeValid_prime [2, 3, 7, 29, 32664311] ⟨1949471409103, 10, [(2, 1), (3, 1), (7, 3), (29, 1), (32664311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_32664311
  · decide +kernel

theorem prime_1949471453519 : Nat.Prime 1949471453519 := by
  apply nodeValid_prime [2, 79, 3307, 3731003] ⟨1949471453519, 7, [(2, 1), (79, 1), (3307, 1), (3731003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_3307
    · exact prime_3731003
  · decide +kernel

theorem prime_1951520753971 : Nat.Prime 1951520753971 := by
  apply nodeValid_prime [2, 3, 5, 19, 41, 27835127] ⟨1951520753971, 2, [(2, 1), (3, 2), (5, 1), (19, 1), (41, 1), (27835127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_27835127
  · decide +kernel

theorem prime_1951520755123 : Nat.Prime 1951520755123 := by
  apply nodeValid_prime [2, 3, 36139273243] ⟨1951520755123, 2, [(2, 1), (3, 3), (36139273243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36139273243
  · decide +kernel

theorem prime_1951520760421 : Nat.Prime 1951520760421 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 367, 1150973] ⟨1951520760421, 17, [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (367, 1), (1150973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_367
    · exact prime_1150973
  · decide +kernel

theorem prime_1953571520843 : Nat.Prime 1953571520843 := by
  apply nodeValid_prime [2, 97, 157, 64139849] ⟨1953571520843, 2, [(2, 1), (97, 1), (157, 1), (64139849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_157
    · exact prime_64139849
  · decide +kernel

theorem prime_1953571521107 : Nat.Prime 1953571521107 := by
  apply nodeValid_prime [2, 23, 42468946111] ⟨1953571521107, 2, [(2, 1), (23, 1), (42468946111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_42468946111
  · decide +kernel

theorem prime_1953571532657 : Nat.Prime 1953571532657 := by
  apply nodeValid_prime [2, 73, 1672578367] ⟨1953571532657, 3, [(2, 4), (73, 1), (1672578367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1672578367
  · decide +kernel

theorem prime_1955623765243 : Nat.Prime 1955623765243 := by
  apply nodeValid_prime [2, 3, 7, 251, 185507851] ⟨1955623765243, 2, [(2, 1), (3, 1), (7, 1), (251, 1), (185507851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_251
    · exact prime_185507851
  · decide +kernel

theorem prime_1955623873061 : Nat.Prime 1955623873061 := by
  apply nodeValid_prime [2, 5, 11, 13, 59, 2399, 4831] ⟨1955623873061, 3, [(2, 2), (5, 1), (11, 1), (13, 1), (59, 1), (2399, 1), (4831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_59
    · exact prime_2399
    · exact prime_4831
  · decide +kernel

theorem prime_1955623873331 : Nat.Prime 1955623873331 := by
  apply nodeValid_prime [2, 5, 415153, 471061] ⟨1955623873331, 6, [(2, 1), (5, 1), (415153, 1), (471061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_415153
    · exact prime_471061
  · decide +kernel

theorem prime_1957677451651 : Nat.Prime 1957677451651 := by
  apply nodeValid_prime [2, 3, 5, 19, 107, 389, 5501] ⟨1957677451651, 3, [(2, 1), (3, 2), (5, 2), (19, 1), (107, 1), (389, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_107
    · exact prime_389
    · exact prime_5501
  · decide +kernel

theorem prime_1957677461941 : Nat.Prime 1957677461941 := by
  apply nodeValid_prime [2, 3, 5, 577, 2039, 27733] ⟨1957677461941, 6, [(2, 2), (3, 1), (5, 1), (577, 1), (2039, 1), (27733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_577
    · exact prime_2039
    · exact prime_27733
  · decide +kernel

theorem prime_1957677461981 : Nat.Prime 1957677461981 := by
  apply nodeValid_prime [2, 5, 41, 181, 13190119] ⟨1957677461981, 2, [(2, 2), (5, 1), (41, 1), (181, 1), (13190119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_181
    · exact prime_13190119
  · decide +kernel

theorem prime_1959732597929 : Nat.Prime 1959732597929 := by
  apply nodeValid_prime [2, 7, 43, 813842441] ⟨1959732597929, 3, [(2, 3), (7, 1), (43, 1), (813842441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_813842441
  · decide +kernel

theorem prime_1959732598253 : Nat.Prime 1959732598253 := by
  apply nodeValid_prime [2, 11, 13, 101, 1811, 18731] ⟨1959732598253, 3, [(2, 2), (11, 1), (13, 1), (101, 1), (1811, 1), (18731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_101
    · exact prime_1811
    · exact prime_18731
  · decide +kernel

theorem prime_1959732598493 : Nat.Prime 1959732598493 := by
  apply nodeValid_prime [2, 53, 67, 137970473] ⟨1959732598493, 2, [(2, 2), (53, 1), (67, 1), (137970473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_67
    · exact prime_137970473
  · decide +kernel

theorem prime_1961789194367 : Nat.Prime 1961789194367 := by
  apply nodeValid_prime [2, 29, 241, 140348347] ⟨1961789194367, 5, [(2, 1), (29, 1), (241, 1), (140348347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_241
    · exact prime_140348347
  · decide +kernel

theorem prime_1961789194643 : Nat.Prime 1961789194643 := by
  apply nodeValid_prime [2, 980894597321] ⟨1961789194643, 2, [(2, 1), (980894597321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_980894597321
  · decide +kernel

theorem prime_1961789202493 : Nat.Prime 1961789202493 := by
  apply nodeValid_prime [2, 3, 7, 14293, 1633991] ⟨1961789202493, 2, [(2, 2), (3, 1), (7, 1), (14293, 1), (1633991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14293
    · exact prime_1633991
  · decide +kernel

theorem prime_1963847265283 : Nat.Prime 1963847265283 := by
  apply nodeValid_prime [2, 3, 7, 827, 2692363] ⟨1963847265283, 5, [(2, 1), (3, 2), (7, 2), (827, 1), (2692363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_827
    · exact prime_2692363
  · decide +kernel

theorem prime_1963847270039 : Nat.Prime 1963847270039 := by
  apply nodeValid_prime [2, 981923635019] ⟨1963847270039, 7, [(2, 1), (981923635019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_981923635019
  · decide +kernel

theorem prime_1963847270167 : Nat.Prime 1963847270167 := by
  apply nodeValid_prime [2, 3, 113, 431, 701, 9587] ⟨1963847270167, 3, [(2, 1), (3, 1), (113, 1), (431, 1), (701, 1), (9587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_431
    · exact prime_701
    · exact prime_9587
  · decide +kernel

theorem prime_1965906704173 : Nat.Prime 1965906704173 := by
  apply nodeValid_prime [2, 3, 53, 7019, 440383] ⟨1965906704173, 2, [(2, 2), (3, 1), (53, 1), (7019, 1), (440383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_7019
    · exact prime_440383
  · decide +kernel

theorem prime_1965906704833 : Nat.Prime 1965906704833 := by
  apply nodeValid_prime [2, 3, 7, 1462728203] ⟨1965906704833, 5, [(2, 6), (3, 1), (7, 1), (1462728203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1462728203
  · decide +kernel

theorem prime_1965906792379 : Nat.Prime 1965906792379 := by
  apply nodeValid_prime [2, 3, 109217044021] ⟨1965906792379, 2, [(2, 1), (3, 2), (109217044021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109217044021
  · decide +kernel

theorem prime_1967967774893 : Nat.Prime 1967967774893 := by
  apply nodeValid_prime [2, 7, 70284563389] ⟨1967967774893, 3, [(2, 2), (7, 1), (70284563389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_70284563389
  · decide +kernel

theorem prime_1967967775691 : Nat.Prime 1967967775691 := by
  apply nodeValid_prime [2, 5, 7, 1423, 4409, 4481] ⟨1967967775691, 2, [(2, 1), (5, 1), (7, 1), (1423, 1), (4409, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1423
    · exact prime_4409
    · exact prime_4481
  · decide +kernel

theorem prime_1967967791171 : Nat.Prime 1967967791171 := by
  apply nodeValid_prime [2, 5, 196796779117] ⟨1967967791171, 2, [(2, 1), (5, 1), (196796779117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_196796779117
  · decide +kernel

theorem prime_1970030247821 : Nat.Prime 1970030247821 := by
  apply nodeValid_prime [2, 5, 163, 317, 1906321] ⟨1970030247821, 3, [(2, 2), (5, 1), (163, 1), (317, 1), (1906321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_317
    · exact prime_1906321
  · decide +kernel

theorem prime_1970030249777 : Nat.Prime 1970030249777 := by
  apply nodeValid_prime [2, 31, 163, 24367087] ⟨1970030249777, 3, [(2, 4), (31, 1), (163, 1), (24367087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_163
    · exact prime_24367087
  · decide +kernel

theorem prime_1970030254883 : Nat.Prime 1970030254883 := by
  apply nodeValid_prime [2, 36919, 26680439] ⟨1970030254883, 2, [(2, 1), (36919, 1), (26680439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_36919
    · exact prime_26680439
  · decide +kernel

theorem prime_1972094164423 : Nat.Prime 1972094164423 := by
  apply nodeValid_prime [2, 3, 89, 607, 1699, 3581] ⟨1972094164423, 5, [(2, 1), (3, 1), (89, 1), (607, 1), (1699, 1), (3581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_607
    · exact prime_1699
    · exact prime_3581
  · decide +kernel

theorem prime_1972094164919 : Nat.Prime 1972094164919 := by
  apply nodeValid_prime [2, 986047082459] ⟨1972094164919, 7, [(2, 1), (986047082459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_986047082459
  · decide +kernel

theorem prime_1972094181259 : Nat.Prime 1972094181259 := by
  apply nodeValid_prime [2, 3, 17, 433, 659, 67757] ⟨1972094181259, 3, [(2, 1), (3, 1), (17, 1), (433, 1), (659, 1), (67757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_433
    · exact prime_659
    · exact prime_67757
  · decide +kernel

theorem prime_1974159578659 : Nat.Prime 1974159578659 := by
  apply nodeValid_prime [2, 3, 329026596443] ⟨1974159578659, 7, [(2, 1), (3, 1), (329026596443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_329026596443
  · decide +kernel

theorem prime_1974159591527 : Nat.Prime 1974159591527 := by
  apply nodeValid_prime [2, 131, 7534960273] ⟨1974159591527, 5, [(2, 1), (131, 1), (7534960273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_7534960273
  · decide +kernel

theorem prime_1974159591727 : Nat.Prime 1974159591727 := by
  apply nodeValid_prime [2, 3, 7, 83, 20663, 27407] ⟨1974159591727, 3, [(2, 1), (3, 1), (7, 1), (83, 1), (20663, 1), (27407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_20663
    · exact prime_27407
  · decide +kernel

end Sude.Lucas.Generated
