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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2237 : Nat.Prime 2237 := by
  apply nodeValid_prime [2, 13, 43] ⟨2237, 2, [(2, 2), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_2749 : Nat.Prime 2749 := by
  apply nodeValid_prime [2, 3, 229] ⟨2749, 6, [(2, 2), (3, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
  · decide +kernel

theorem prime_3371 : Nat.Prime 3371 := by
  apply nodeValid_prime [2, 5, 337] ⟨3371, 2, [(2, 1), (5, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_337
  · decide +kernel

theorem prime_3407 : Nat.Prime 3407 := by
  apply nodeValid_prime [2, 13, 131] ⟨3407, 5, [(2, 1), (13, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_131
  · decide +kernel

theorem prime_3967 : Nat.Prime 3967 := by
  apply nodeValid_prime [2, 3, 661] ⟨3967, 6, [(2, 1), (3, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_661
  · decide +kernel

theorem prime_4651 : Nat.Prime 4651 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨4651, 3, [(2, 1), (3, 1), (5, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_4987 : Nat.Prime 4987 := by
  apply nodeValid_prime [2, 3, 277] ⟨4987, 2, [(2, 1), (3, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
  · decide +kernel

theorem prime_5273 : Nat.Prime 5273 := by
  apply nodeValid_prime [2, 659] ⟨5273, 3, [(2, 3), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_659
  · decide +kernel

theorem prime_6469 : Nat.Prime 6469 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨6469, 2, [(2, 2), (3, 1), (7, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_6599 : Nat.Prime 6599 := by
  apply nodeValid_prime [2, 3299] ⟨6599, 13, [(2, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3299
  · decide +kernel

theorem prime_8039 : Nat.Prime 8039 := by
  apply nodeValid_prime [2, 4019] ⟨8039, 11, [(2, 1), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4019
  · decide +kernel

theorem prime_8353 : Nat.Prime 8353 := by
  apply nodeValid_prime [2, 3, 29] ⟨8353, 5, [(2, 5), (3, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_12421 : Nat.Prime 12421 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨12421, 7, [(2, 2), (3, 3), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_12589 : Nat.Prime 12589 := by
  apply nodeValid_prime [2, 3, 1049] ⟨12589, 2, [(2, 2), (3, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1049
  · decide +kernel

theorem prime_12619 : Nat.Prime 12619 := by
  apply nodeValid_prime [2, 3, 701] ⟨12619, 2, [(2, 1), (3, 2), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_701
  · decide +kernel

theorem prime_12703 : Nat.Prime 12703 := by
  apply nodeValid_prime [2, 3, 29, 73] ⟨12703, 3, [(2, 1), (3, 1), (29, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_73
  · decide +kernel

theorem prime_13591 : Nat.Prime 13591 := by
  apply nodeValid_prime [2, 3, 5, 151] ⟨13591, 3, [(2, 1), (3, 2), (5, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
  · decide +kernel

theorem prime_14669 : Nat.Prime 14669 := by
  apply nodeValid_prime [2, 19, 193] ⟨14669, 2, [(2, 2), (19, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_193
  · decide +kernel

theorem prime_15131 : Nat.Prime 15131 := by
  apply nodeValid_prime [2, 5, 17, 89] ⟨15131, 2, [(2, 1), (5, 1), (17, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_89
  · decide +kernel

theorem prime_16931 : Nat.Prime 16931 := by
  apply nodeValid_prime [2, 5, 1693] ⟨16931, 2, [(2, 1), (5, 1), (1693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1693
  · decide +kernel

theorem prime_17909 : Nat.Prime 17909 := by
  apply nodeValid_prime [2, 11, 37] ⟨17909, 2, [(2, 2), (11, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_18773 : Nat.Prime 18773 := by
  apply nodeValid_prime [2, 13, 19] ⟨18773, 2, [(2, 2), (13, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_19207 : Nat.Prime 19207 := by
  apply nodeValid_prime [2, 3, 11, 97] ⟨19207, 5, [(2, 1), (3, 2), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_20899 : Nat.Prime 20899 := by
  apply nodeValid_prime [2, 3, 43] ⟨20899, 2, [(2, 1), (3, 5), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_21803 : Nat.Prime 21803 := by
  apply nodeValid_prime [2, 11, 991] ⟨21803, 2, [(2, 1), (11, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_991
  · decide +kernel

theorem prime_22159 : Nat.Prime 22159 := by
  apply nodeValid_prime [2, 3, 1231] ⟨22159, 6, [(2, 1), (3, 2), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1231
  · decide +kernel

theorem prime_25667 : Nat.Prime 25667 := by
  apply nodeValid_prime [2, 41, 313] ⟨25667, 2, [(2, 1), (41, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_313
  · decide +kernel

theorem prime_29339 : Nat.Prime 29339 := by
  apply nodeValid_prime [2, 14669] ⟨29339, 2, [(2, 1), (14669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14669
  · decide +kernel

theorem prime_30469 : Nat.Prime 30469 := by
  apply nodeValid_prime [2, 3, 2539] ⟨30469, 2, [(2, 2), (3, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2539
  · decide +kernel

theorem prime_31657 : Nat.Prime 31657 := by
  apply nodeValid_prime [2, 3, 1319] ⟨31657, 5, [(2, 3), (3, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1319
  · decide +kernel

theorem prime_33863 : Nat.Prime 33863 := by
  apply nodeValid_prime [2, 16931] ⟨33863, 5, [(2, 1), (16931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16931
  · decide +kernel

theorem prime_37547 : Nat.Prime 37547 := by
  apply nodeValid_prime [2, 18773] ⟨37547, 2, [(2, 1), (18773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18773
  · decide +kernel

theorem prime_41539 : Nat.Prime 41539 := by
  apply nodeValid_prime [2, 3, 7, 23, 43] ⟨41539, 3, [(2, 1), (3, 1), (7, 1), (23, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_43
  · decide +kernel

theorem prime_46511 : Nat.Prime 46511 := by
  apply nodeValid_prime [2, 5, 4651] ⟨46511, 11, [(2, 1), (5, 1), (4651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4651
  · decide +kernel

theorem prime_48193 : Nat.Prime 48193 := by
  apply nodeValid_prime [2, 3, 251] ⟨48193, 7, [(2, 6), (3, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
  · decide +kernel

theorem prime_55399 : Nat.Prime 55399 := by
  apply nodeValid_prime [2, 3, 7, 1319] ⟨55399, 6, [(2, 1), (3, 1), (7, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1319
  · decide +kernel

theorem prime_59659 : Nat.Prime 59659 := by
  apply nodeValid_prime [2, 3, 61, 163] ⟨59659, 3, [(2, 1), (3, 1), (61, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_163
  · decide +kernel

theorem prime_62903 : Nat.Prime 62903 := by
  apply nodeValid_prime [2, 7, 4493] ⟨62903, 5, [(2, 1), (7, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4493
  · decide +kernel

theorem prime_64151 : Nat.Prime 64151 := by
  apply nodeValid_prime [2, 5, 1283] ⟨64151, 17, [(2, 1), (5, 2), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1283
  · decide +kernel

theorem prime_74527 : Nat.Prime 74527 := by
  apply nodeValid_prime [2, 3, 12421] ⟨74527, 3, [(2, 1), (3, 1), (12421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12421
  · decide +kernel

theorem prime_77377 : Nat.Prime 77377 := by
  apply nodeValid_prime [2, 3, 13, 31] ⟨77377, 5, [(2, 6), (3, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_79187 : Nat.Prime 79187 := by
  apply nodeValid_prime [2, 17, 137] ⟨79187, 5, [(2, 1), (17, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_137
  · decide +kernel

theorem prime_91997 : Nat.Prime 91997 := by
  apply nodeValid_prime [2, 109, 211] ⟨91997, 2, [(2, 2), (109, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_211
  · decide +kernel

theorem prime_100237 : Nat.Prime 100237 := by
  apply nodeValid_prime [2, 3, 8353] ⟨100237, 5, [(2, 2), (3, 1), (8353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8353
  · decide +kernel

theorem prime_115471 : Nat.Prime 115471 := by
  apply nodeValid_prime [2, 3, 5, 1283] ⟨115471, 6, [(2, 1), (3, 2), (5, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1283
  · decide +kernel

theorem prime_116443 : Nat.Prime 116443 := by
  apply nodeValid_prime [2, 3, 6469] ⟨116443, 2, [(2, 1), (3, 2), (6469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6469
  · decide +kernel

theorem prime_132929 : Nat.Prime 132929 := by
  apply nodeValid_prime [2, 31, 67] ⟨132929, 3, [(2, 6), (31, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_67
  · decide +kernel

theorem prime_148921 : Nat.Prime 148921 := by
  apply nodeValid_prime [2, 3, 5, 17, 73] ⟨148921, 13, [(2, 3), (3, 1), (5, 1), (17, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_73
  · decide +kernel

theorem prime_164191 : Nat.Prime 164191 := by
  apply nodeValid_prime [2, 3, 5, 13, 421] ⟨164191, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_421
  · decide +kernel

theorem prime_173183 : Nat.Prime 173183 := by
  apply nodeValid_prime [2, 131, 661] ⟨173183, 5, [(2, 1), (131, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_661
  · decide +kernel

theorem prime_198013 : Nat.Prime 198013 := by
  apply nodeValid_prime [2, 3, 29, 569] ⟨198013, 5, [(2, 2), (3, 1), (29, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_569
  · decide +kernel

theorem prime_208991 : Nat.Prime 208991 := by
  apply nodeValid_prime [2, 5, 20899] ⟨208991, 17, [(2, 1), (5, 1), (20899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20899
  · decide +kernel

theorem prime_214481 : Nat.Prime 214481 := by
  apply nodeValid_prime [2, 5, 7, 383] ⟨214481, 3, [(2, 4), (5, 1), (7, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_383
  · decide +kernel

theorem prime_224881 : Nat.Prime 224881 := by
  apply nodeValid_prime [2, 3, 5, 937] ⟨224881, 7, [(2, 4), (3, 1), (5, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_937
  · decide +kernel

theorem prime_241489 : Nat.Prime 241489 := by
  apply nodeValid_prime [2, 3, 13, 43] ⟨241489, 7, [(2, 4), (3, 3), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_245863 : Nat.Prime 245863 := by
  apply nodeValid_prime [2, 3, 29, 157] ⟨245863, 3, [(2, 1), (3, 3), (29, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_157
  · decide +kernel

theorem prime_246577 : Nat.Prime 246577 := by
  apply nodeValid_prime [2, 3, 11, 467] ⟨246577, 5, [(2, 4), (3, 1), (11, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_467
  · decide +kernel

theorem prime_300193 : Nat.Prime 300193 := by
  apply nodeValid_prime [2, 3, 53, 59] ⟨300193, 5, [(2, 5), (3, 1), (53, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_59
  · decide +kernel

theorem prime_331537 : Nat.Prime 331537 := by
  apply nodeValid_prime [2, 3, 6907] ⟨331537, 5, [(2, 4), (3, 1), (6907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6907
  · decide +kernel

theorem prime_363371 : Nat.Prime 363371 := by
  apply nodeValid_prime [2, 5, 7, 29, 179] ⟨363371, 2, [(2, 1), (5, 1), (7, 1), (29, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_179
  · decide +kernel

theorem prime_366853 : Nat.Prime 366853 := by
  apply nodeValid_prime [2, 3, 19, 1609] ⟨366853, 13, [(2, 2), (3, 1), (19, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1609
  · decide +kernel

theorem prime_369331 : Nat.Prime 369331 := by
  apply nodeValid_prime [2, 3, 5, 13, 947] ⟨369331, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_947
  · decide +kernel

theorem prime_386237 : Nat.Prime 386237 := by
  apply nodeValid_prime [2, 223, 433] ⟨386237, 2, [(2, 2), (223, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_433
  · decide +kernel

theorem prime_457253 : Nat.Prime 457253 := by
  apply nodeValid_prime [2, 79, 1447] ⟨457253, 2, [(2, 2), (79, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1447
  · decide +kernel

theorem prime_468121 : Nat.Prime 468121 := by
  apply nodeValid_prime [2, 3, 5, 47, 83] ⟨468121, 14, [(2, 3), (3, 1), (5, 1), (47, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_83
  · decide +kernel

theorem prime_511633 : Nat.Prime 511633 := by
  apply nodeValid_prime [2, 3, 11, 17, 19] ⟨511633, 13, [(2, 4), (3, 2), (11, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_532619 : Nat.Prime 532619 := by
  apply nodeValid_prime [2, 79, 3371] ⟨532619, 2, [(2, 1), (79, 1), (3371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_3371
  · decide +kernel

theorem prime_585061 : Nat.Prime 585061 := by
  apply nodeValid_prime [2, 3, 5, 7, 199] ⟨585061, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_199
  · decide +kernel

theorem prime_673801 : Nat.Prime 673801 := by
  apply nodeValid_prime [2, 3, 5, 1123] ⟨673801, 22, [(2, 3), (3, 1), (5, 2), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1123
  · decide +kernel

theorem prime_715909 : Nat.Prime 715909 := by
  apply nodeValid_prime [2, 3, 59659] ⟨715909, 6, [(2, 2), (3, 1), (59659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59659
  · decide +kernel

theorem prime_755809 : Nat.Prime 755809 := by
  apply nodeValid_prime [2, 3, 7873] ⟨755809, 7, [(2, 5), (3, 1), (7873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7873
  · decide +kernel

theorem prime_776551 : Nat.Prime 776551 := by
  apply nodeValid_prime [2, 3, 5, 31, 167] ⟨776551, 3, [(2, 1), (3, 1), (5, 2), (31, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_167
  · decide +kernel

theorem prime_818341 : Nat.Prime 818341 := by
  apply nodeValid_prime [2, 3, 5, 23, 593] ⟨818341, 2, [(2, 2), (3, 1), (5, 1), (23, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_593
  · decide +kernel

theorem prime_866963 : Nat.Prime 866963 := by
  apply nodeValid_prime [2, 23, 47, 401] ⟨866963, 2, [(2, 1), (23, 1), (47, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_401
  · decide +kernel

theorem prime_959333 : Nat.Prime 959333 := by
  apply nodeValid_prime [2, 11, 21803] ⟨959333, 2, [(2, 2), (11, 1), (21803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_21803
  · decide +kernel

theorem prime_1301957 : Nat.Prime 1301957 := by
  apply nodeValid_prime [2, 19, 37, 463] ⟨1301957, 2, [(2, 2), (19, 1), (37, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_463
  · decide +kernel

theorem prime_1462621 : Nat.Prime 1462621 := by
  apply nodeValid_prime [2, 3, 5, 19, 1283] ⟨1462621, 7, [(2, 2), (3, 1), (5, 1), (19, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1283
  · decide +kernel

theorem prime_1462999 : Nat.Prime 1462999 := by
  apply nodeValid_prime [2, 3, 109, 2237] ⟨1462999, 3, [(2, 1), (3, 1), (109, 1), (2237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_2237
  · decide +kernel

theorem prime_1466389 : Nat.Prime 1466389 := by
  apply nodeValid_prime [2, 3, 7, 11, 23] ⟨1466389, 14, [(2, 2), (3, 2), (7, 1), (11, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_1467413 : Nat.Prime 1467413 := by
  apply nodeValid_prime [2, 366853] ⟨1467413, 2, [(2, 2), (366853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_366853
  · decide +kernel

theorem prime_1478639 : Nat.Prime 1478639 := by
  apply nodeValid_prime [2, 7, 31, 3407] ⟨1478639, 7, [(2, 1), (7, 1), (31, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_3407
  · decide +kernel

theorem prime_1918667 : Nat.Prime 1918667 := by
  apply nodeValid_prime [2, 959333] ⟨1918667, 2, [(2, 1), (959333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_959333
  · decide +kernel

theorem prime_2235557 : Nat.Prime 2235557 := by
  apply nodeValid_prime [2, 197, 2837] ⟨2235557, 2, [(2, 2), (197, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_2837
  · decide +kernel

theorem prime_2296699 : Nat.Prime 2296699 := by
  apply nodeValid_prime [2, 3, 503, 761] ⟨2296699, 2, [(2, 1), (3, 1), (503, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
    · exact prime_761
  · decide +kernel

theorem prime_2630819 : Nat.Prime 2630819 := by
  apply nodeValid_prime [2, 17, 77377] ⟨2630819, 2, [(2, 1), (17, 1), (77377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_77377
  · decide +kernel

theorem prime_3276263 : Nat.Prime 3276263 := by
  apply nodeValid_prime [2, 11, 148921] ⟨3276263, 5, [(2, 1), (11, 1), (148921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_148921
  · decide +kernel

theorem prime_3524383 : Nat.Prime 3524383 := by
  apply nodeValid_prime [2, 3, 23, 8513] ⟨3524383, 3, [(2, 1), (3, 2), (23, 1), (8513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_8513
  · decide +kernel

theorem prime_3800387 : Nat.Prime 3800387 := by
  apply nodeValid_prime [2, 479, 3967] ⟨3800387, 2, [(2, 1), (479, 1), (3967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_3967
  · decide +kernel

theorem prime_3837511 : Nat.Prime 3837511 := by
  apply nodeValid_prime [2, 3, 5, 61, 233] ⟨3837511, 3, [(2, 1), (3, 3), (5, 1), (61, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_233
  · decide +kernel

theorem prime_4502759 : Nat.Prime 4502759 := by
  apply nodeValid_prime [2, 13, 173183] ⟨4502759, 7, [(2, 1), (13, 1), (173183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_173183
  · decide +kernel

theorem prime_4910047 : Nat.Prime 4910047 := by
  apply nodeValid_prime [2, 3, 818341] ⟨4910047, 3, [(2, 1), (3, 1), (818341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_818341
  · decide +kernel

theorem prime_6255797 : Nat.Prime 6255797 := by
  apply nodeValid_prime [2, 17, 91997] ⟨6255797, 2, [(2, 2), (17, 1), (91997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_91997
  · decide +kernel

theorem prime_6603383 : Nat.Prime 6603383 := by
  apply nodeValid_prime [2, 149, 22159] ⟨6603383, 5, [(2, 1), (149, 1), (22159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_22159
  · decide +kernel

theorem prime_7956889 : Nat.Prime 7956889 := by
  apply nodeValid_prime [2, 3, 331537] ⟨7956889, 13, [(2, 3), (3, 1), (331537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331537
  · decide +kernel

theorem prime_8821151 : Nat.Prime 8821151 := by
  apply nodeValid_prime [2, 5, 13, 41, 331] ⟨8821151, 11, [(2, 1), (5, 2), (13, 1), (41, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_331
  · decide +kernel

theorem prime_11226037 : Nat.Prime 11226037 := by
  apply nodeValid_prime [2, 3, 19, 53, 929] ⟨11226037, 2, [(2, 2), (3, 1), (19, 1), (53, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
    · exact prime_929
  · decide +kernel

theorem prime_16994429 : Nat.Prime 16994429 := by
  apply nodeValid_prime [2, 11, 386237] ⟨16994429, 2, [(2, 2), (11, 1), (386237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_386237
  · decide +kernel

theorem prime_18343133 : Nat.Prime 18343133 := by
  apply nodeValid_prime [2, 19, 12703] ⟨18343133, 2, [(2, 2), (19, 2), (12703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_12703
  · decide +kernel

theorem prime_26103947 : Nat.Prime 26103947 := by
  apply nodeValid_prime [2, 11, 431, 2753] ⟨26103947, 2, [(2, 1), (11, 1), (431, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_431
    · exact prime_2753
  · decide +kernel

theorem prime_33988859 : Nat.Prime 33988859 := by
  apply nodeValid_prime [2, 16994429] ⟨33988859, 2, [(2, 1), (16994429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16994429
  · decide +kernel

theorem prime_35411353 : Nat.Prime 35411353 := by
  apply nodeValid_prime [2, 3, 23, 64151] ⟨35411353, 5, [(2, 3), (3, 1), (23, 1), (64151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_64151
  · decide +kernel

theorem prime_38375111 : Nat.Prime 38375111 := by
  apply nodeValid_prime [2, 5, 3837511] ⟨38375111, 11, [(2, 1), (5, 1), (3837511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3837511
  · decide +kernel

theorem prime_40438033 : Nat.Prime 40438033 := by
  apply nodeValid_prime [2, 3, 619, 1361] ⟨40438033, 15, [(2, 4), (3, 1), (619, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
    · exact prime_1361
  · decide +kernel

theorem prime_49885343 : Nat.Prime 49885343 := by
  apply nodeValid_prime [2, 13, 1918667] ⟨49885343, 5, [(2, 1), (13, 1), (1918667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1918667
  · decide +kernel

theorem prime_50444269 : Nat.Prime 50444269 := by
  apply nodeValid_prime [2, 3, 7, 41, 97, 151] ⟨50444269, 13, [(2, 2), (3, 1), (7, 1), (41, 1), (97, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_97
    · exact prime_151
  · decide +kernel

theorem prime_51216031 : Nat.Prime 51216031 := by
  apply nodeValid_prime [2, 3, 5, 29, 31, 211] ⟨51216031, 11, [(2, 1), (3, 3), (5, 1), (29, 1), (31, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_31
    · exact prime_211
  · decide +kernel

theorem prime_66133523 : Nat.Prime 66133523 := by
  apply nodeValid_prime [2, 7, 13, 363371] ⟨66133523, 2, [(2, 1), (7, 1), (13, 1), (363371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_363371
  · decide +kernel

theorem prime_127155757 : Nat.Prime 127155757 := by
  apply nodeValid_prime [2, 3, 7, 13, 116443] ⟨127155757, 5, [(2, 2), (3, 1), (7, 1), (13, 1), (116443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_116443
  · decide +kernel

theorem prime_161752133 : Nat.Prime 161752133 := by
  apply nodeValid_prime [2, 40438033] ⟨161752133, 2, [(2, 2), (40438033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40438033
  · decide +kernel

theorem prime_190323013 : Nat.Prime 190323013 := by
  apply nodeValid_prime [2, 3, 11, 31, 46511] ⟨190323013, 5, [(2, 2), (3, 1), (11, 1), (31, 1), (46511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_46511
  · decide +kernel

theorem prime_213286991 : Nat.Prime 213286991 := by
  apply nodeValid_prime [2, 5, 7, 1613, 1889] ⟨213286991, 11, [(2, 1), (5, 1), (7, 1), (1613, 1), (1889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1613
    · exact prime_1889
  · decide +kernel

theorem prime_334012183 : Nat.Prime 334012183 := by
  apply nodeValid_prime [2, 3, 7, 1427, 5573] ⟨334012183, 6, [(2, 1), (3, 1), (7, 1), (1427, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1427
    · exact prime_5573
  · decide +kernel

theorem prime_409409747 : Nat.Prime 409409747 := by
  apply nodeValid_prime [2, 31, 6603383] ⟨409409747, 2, [(2, 1), (31, 1), (6603383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_6603383
  · decide +kernel

theorem prime_630547271 : Nat.Prime 630547271 := by
  apply nodeValid_prime [2, 5, 43, 1466389] ⟨630547271, 14, [(2, 1), (5, 1), (43, 1), (1466389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_1466389
  · decide +kernel

theorem prime_740120431 : Nat.Prime 740120431 := by
  apply nodeValid_prime [2, 3, 5, 7, 3524383] ⟨740120431, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (3524383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3524383
  · decide +kernel

theorem prime_997706861 : Nat.Prime 997706861 := by
  apply nodeValid_prime [2, 5, 49885343] ⟨997706861, 2, [(2, 2), (5, 1), (49885343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49885343
  · decide +kernel

theorem prime_1033753859 : Nat.Prime 1033753859 := by
  apply nodeValid_prime [2, 397, 1301957] ⟨1033753859, 2, [(2, 1), (397, 1), (1301957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_1301957
  · decide +kernel

theorem prime_1134985087 : Nat.Prime 1134985087 := by
  apply nodeValid_prime [2, 3, 43, 1466389] ⟨1134985087, 6, [(2, 1), (3, 2), (43, 1), (1466389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1466389
  · decide +kernel

theorem prime_1259261357 : Nat.Prime 1259261357 := by
  apply nodeValid_prime [2, 89, 1511, 2341] ⟨1259261357, 2, [(2, 2), (89, 1), (1511, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1511
    · exact prime_2341
  · decide +kernel

theorem prime_1843498567 : Nat.Prime 1843498567 := by
  apply nodeValid_prime [2, 3, 7, 13, 487, 2311] ⟨1843498567, 3, [(2, 1), (3, 2), (7, 1), (13, 1), (487, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_487
    · exact prime_2311
  · decide +kernel

theorem prime_2118431129 : Nat.Prime 2118431129 := by
  apply nodeValid_prime [2, 11, 31, 776551] ⟨2118431129, 3, [(2, 3), (11, 1), (31, 1), (776551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_776551
  · decide +kernel

theorem prime_5472557281 : Nat.Prime 5472557281 := by
  apply nodeValid_prime [2, 3, 5, 3800387] ⟨5472557281, 17, [(2, 5), (3, 2), (5, 1), (3800387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3800387
  · decide +kernel

theorem prime_9900321653 : Nat.Prime 9900321653 := by
  apply nodeValid_prime [2, 13, 911, 208991] ⟨9900321653, 2, [(2, 2), (13, 1), (911, 1), (208991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_911
    · exact prime_208991
  · decide +kernel

theorem prime_10298391139 : Nat.Prime 10298391139 := by
  apply nodeValid_prime [2, 3, 7, 17, 127, 12619] ⟨10298391139, 3, [(2, 1), (3, 3), (7, 1), (17, 1), (127, 1), (12619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_127
    · exact prime_12619
  · decide +kernel

theorem prime_15958525711 : Nat.Prime 15958525711 := by
  apply nodeValid_prime [2, 3, 5, 29, 18343133] ⟨15958525711, 3, [(2, 1), (3, 1), (5, 1), (29, 1), (18343133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_18343133
  · decide +kernel

theorem prime_31981666547 : Nat.Prime 31981666547 := by
  apply nodeValid_prime [2, 317, 50444269] ⟨31981666547, 2, [(2, 1), (317, 1), (50444269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_50444269
  · decide +kernel

theorem prime_41025365287 : Nat.Prime 41025365287 := by
  apply nodeValid_prime [2, 3, 2087, 3276263] ⟨41025365287, 6, [(2, 1), (3, 1), (2087, 1), (3276263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2087
    · exact prime_3276263
  · decide +kernel

theorem prime_42728493931 : Nat.Prime 42728493931 := by
  apply nodeValid_prime [2, 3, 5, 179, 7956889] ⟨42728493931, 10, [(2, 1), (3, 1), (5, 1), (179, 1), (7956889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_7956889
  · decide +kernel

theorem prime_62043353893 : Nat.Prime 62043353893 := by
  apply nodeValid_prime [2, 3, 13, 4910047] ⟨62043353893, 5, [(2, 2), (3, 5), (13, 1), (4910047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4910047
  · decide +kernel

theorem prime_123833521541 : Nat.Prime 123833521541 := by
  apply nodeValid_prime [2, 5, 149, 1619, 25667] ⟨123833521541, 2, [(2, 2), (5, 1), (149, 1), (1619, 1), (25667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_1619
    · exact prime_25667
  · decide +kernel

theorem prime_125102955683 : Nat.Prime 125102955683 := by
  apply nodeValid_prime [2, 41, 31657, 48193] ⟨125102955683, 2, [(2, 1), (41, 1), (31657, 1), (48193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_31657
    · exact prime_48193
  · decide +kernel

theorem prime_128964064409 : Nat.Prime 128964064409 := by
  apply nodeValid_prime [2, 47, 11257, 30469] ⟨128964064409, 3, [(2, 3), (47, 1), (11257, 1), (30469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_11257
    · exact prime_30469
  · decide +kernel

theorem prime_129224303003 : Nat.Prime 129224303003 := by
  apply nodeValid_prime [2, 74527, 866963] ⟨129224303003, 2, [(2, 1), (74527, 1), (866963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_74527
    · exact prime_866963
  · decide +kernel

theorem prime_246152134889 : Nat.Prime 246152134889 := by
  apply nodeValid_prime [2, 11, 31, 367, 245863] ⟨246152134889, 3, [(2, 3), (11, 1), (31, 1), (367, 1), (245863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_367
    · exact prime_245863
  · decide +kernel

theorem prime_246152191723 : Nat.Prime 246152191723 := by
  apply nodeValid_prime [2, 3, 41025365287] ⟨246152191723, 2, [(2, 1), (3, 1), (41025365287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41025365287
  · decide +kernel

theorem prime_246152191763 : Nat.Prime 246152191763 := by
  apply nodeValid_prime [2, 419, 1789, 164191] ⟨246152191763, 2, [(2, 1), (419, 1), (1789, 1), (164191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_1789
    · exact prime_164191
  · decide +kernel

theorem prime_246656405297 : Nat.Prime 246656405297 := by
  apply nodeValid_prime [2, 7, 43, 51216031] ⟨246656405297, 3, [(2, 4), (7, 1), (43, 1), (51216031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_51216031
  · decide +kernel

theorem prime_246656405441 : Nat.Prime 246656405441 := by
  apply nodeValid_prime [2, 5, 17, 31, 1462621] ⟨246656405441, 3, [(2, 6), (5, 1), (17, 1), (31, 1), (1462621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_1462621
  · decide +kernel

theorem prime_246656405951 : Nat.Prime 246656405951 := by
  apply nodeValid_prime [2, 5, 17, 37, 59, 132929] ⟨246656405951, 13, [(2, 1), (5, 2), (17, 1), (37, 1), (59, 1), (132929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_37
    · exact prime_59
    · exact prime_132929
  · decide +kernel

theorem prime_247161372859 : Nat.Prime 247161372859 := by
  apply nodeValid_prime [2, 3, 23, 47, 1009, 12589] ⟨247161372859, 2, [(2, 1), (3, 2), (23, 1), (47, 1), (1009, 1), (12589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47
    · exact prime_1009
    · exact prime_12589
  · decide +kernel

theorem prime_247161387337 : Nat.Prime 247161387337 := by
  apply nodeValid_prime [2, 3, 10298391139] ⟨247161387337, 5, [(2, 3), (3, 1), (10298391139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10298391139
  · decide +kernel

theorem prime_247161387491 : Nat.Prime 247161387491 := by
  apply nodeValid_prime [2, 5, 100237, 246577] ⟨247161387491, 6, [(2, 1), (5, 1), (100237, 1), (246577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_100237
    · exact prime_246577
  · decide +kernel

theorem prime_247667002883 : Nat.Prime 247667002883 := by
  apply nodeValid_prime [2, 13, 269, 35411353] ⟨247667002883, 5, [(2, 1), (13, 1), (269, 1), (35411353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_269
    · exact prime_35411353
  · decide +kernel

theorem prime_247667003231 : Nat.Prime 247667003231 := by
  apply nodeValid_prime [2, 5, 37, 107, 6255797] ⟨247667003231, 7, [(2, 1), (5, 1), (37, 1), (107, 1), (6255797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_107
    · exact prime_6255797
  · decide +kernel

theorem prime_247667043083 : Nat.Prime 247667043083 := by
  apply nodeValid_prime [2, 123833521541] ⟨247667043083, 2, [(2, 1), (123833521541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_123833521541
  · decide +kernel

theorem prime_248173411909 : Nat.Prime 248173411909 := by
  apply nodeValid_prime [2, 3, 44179, 468121] ⟨248173411909, 2, [(2, 2), (3, 1), (44179, 1), (468121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44179
    · exact prime_468121
  · decide +kernel

theorem prime_248173415521 : Nat.Prime 248173415521 := by
  apply nodeValid_prime [2, 3, 5, 2141, 241489] ⟨248173415521, 13, [(2, 5), (3, 1), (5, 1), (2141, 1), (241489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2141
    · exact prime_241489
  · decide +kernel

theorem prime_248173415573 : Nat.Prime 248173415573 := by
  apply nodeValid_prime [2, 62043353893] ⟨248173415573, 2, [(2, 2), (62043353893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_62043353893
  · decide +kernel

theorem prime_248680464299 : Nat.Prime 248680464299 := by
  apply nodeValid_prime [2, 7, 41, 293, 1478639] ⟨248680464299, 2, [(2, 1), (7, 1), (41, 1), (293, 1), (1478639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_293
    · exact prime_1478639
  · decide +kernel

theorem prime_248680464817 : Nat.Prime 248680464817 := by
  apply nodeValid_prime [2, 3, 7, 740120431] ⟨248680464817, 5, [(2, 4), (3, 1), (7, 1), (740120431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_740120431
  · decide +kernel

theorem prime_248680481587 : Nat.Prime 248680481587 := by
  apply nodeValid_prime [2, 3, 101, 1367, 300193] ⟨248680481587, 3, [(2, 1), (3, 1), (101, 1), (1367, 1), (300193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1367
    · exact prime_300193
  · decide +kernel

theorem prime_249188251751 : Nat.Prime 249188251751 := by
  apply nodeValid_prime [2, 5, 109, 541, 16903] ⟨249188251751, 23, [(2, 1), (5, 3), (109, 1), (541, 1), (16903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_541
    · exact prime_16903
  · decide +kernel

theorem prime_249188278063 : Nat.Prime 249188278063 := by
  apply nodeValid_prime [2, 3, 37, 43, 26103947] ⟨249188278063, 7, [(2, 1), (3, 1), (37, 1), (43, 1), (26103947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_43
    · exact prime_26103947
  · decide +kernel

theorem prime_249188278501 : Nat.Prime 249188278501 := by
  apply nodeValid_prime [2, 3, 5, 7, 151, 5821] ⟨249188278501, 10, [(2, 2), (3, 4), (5, 3), (7, 1), (151, 1), (5821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_151
    · exact prime_5821
  · decide +kernel

theorem prime_249696719141 : Nat.Prime 249696719141 := by
  apply nodeValid_prime [2, 5, 11, 1134985087] ⟨249696719141, 2, [(2, 2), (5, 1), (11, 1), (1134985087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1134985087
  · decide +kernel

theorem prime_249696719317 : Nat.Prime 249696719317 := by
  apply nodeValid_prime [2, 3, 11, 630547271] ⟨249696719317, 2, [(2, 2), (3, 2), (11, 1), (630547271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_630547271
  · decide +kernel

theorem prime_249696724499 : Nat.Prime 249696724499 := by
  apply nodeValid_prime [2, 13, 23, 5273, 79187] ⟨249696724499, 6, [(2, 1), (13, 1), (23, 1), (5273, 1), (79187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_5273
    · exact prime_79187
  · decide +kernel

theorem prime_250205900047 : Nat.Prime 250205900047 := by
  apply nodeValid_prime [2, 3, 31, 1879, 715909] ⟨250205900047, 3, [(2, 1), (3, 1), (31, 1), (1879, 1), (715909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1879
    · exact prime_715909
  · decide +kernel

theorem prime_250205911367 : Nat.Prime 250205911367 := by
  apply nodeValid_prime [2, 125102955683] ⟨250205911367, 5, [(2, 1), (125102955683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_125102955683
  · decide +kernel

theorem prime_250205912657 : Nat.Prime 250205912657 := by
  apply nodeValid_prime [2, 7, 199, 11226037] ⟨250205912657, 3, [(2, 4), (7, 1), (199, 1), (11226037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_199
    · exact prime_11226037
  · decide +kernel

theorem prime_250715779043 : Nat.Prime 250715779043 := by
  apply nodeValid_prime [2, 19, 29339, 224881] ⟨250715779043, 2, [(2, 1), (19, 1), (29339, 1), (224881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29339
    · exact prime_224881
  · decide +kernel

theorem prime_250715805113 : Nat.Prime 250715805113 := by
  apply nodeValid_prime [2, 17, 1843498567] ⟨250715805113, 3, [(2, 3), (17, 1), (1843498567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1843498567
  · decide +kernel

theorem prime_250715806151 : Nat.Prime 250715806151 := by
  apply nodeValid_prime [2, 5, 31, 161752133] ⟨250715806151, 13, [(2, 1), (5, 2), (31, 1), (161752133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_161752133
  · decide +kernel

theorem prime_251226363523 : Nat.Prime 251226363523 := by
  apply nodeValid_prime [2, 3, 59, 1213, 585061] ⟨251226363523, 2, [(2, 1), (3, 1), (59, 1), (1213, 1), (585061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_1213
    · exact prime_585061
  · decide +kernel

theorem prime_251226376747 : Nat.Prime 251226376747 := by
  apply nodeValid_prime [2, 3, 55399, 755809] ⟨251226376747, 2, [(2, 1), (3, 1), (55399, 1), (755809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55399
    · exact prime_755809
  · decide +kernel

theorem prime_251226377161 : Nat.Prime 251226377161 := by
  apply nodeValid_prime [2, 3, 5, 11, 190323013] ⟨251226377161, 43, [(2, 3), (3, 1), (5, 1), (11, 1), (190323013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_190323013
  · decide +kernel

theorem prime_251737634927 : Nat.Prime 251737634927 := by
  apply nodeValid_prime [2, 23, 5472557281] ⟨251737634927, 5, [(2, 1), (23, 1), (5472557281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_5472557281
  · decide +kernel

theorem prime_251737634977 : Nat.Prime 251737634977 := by
  apply nodeValid_prime [2, 3, 1787, 1467413] ⟨251737634977, 5, [(2, 5), (3, 1), (1787, 1), (1467413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1787
    · exact prime_1467413
  · decide +kernel

theorem prime_251737649851 : Nat.Prime 251737649851 := by
  apply nodeValid_prime [2, 3, 5, 17, 31, 43, 2389] ⟨251737649851, 2, [(2, 1), (3, 1), (5, 2), (17, 1), (31, 2), (43, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_43
    · exact prime_2389
  · decide +kernel

theorem prime_252249632689 : Nat.Prime 252249632689 := by
  apply nodeValid_prime [2, 3, 71, 641, 115471] ⟨252249632689, 11, [(2, 4), (3, 1), (71, 1), (641, 1), (115471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_641
    · exact prime_115471
  · decide +kernel

theorem prime_252249633997 : Nat.Prime 252249633997 := by
  apply nodeValid_prime [2, 3, 2383, 8821151] ⟨252249633997, 2, [(2, 2), (3, 1), (2383, 1), (8821151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2383
    · exact prime_8821151
  · decide +kernel

theorem prime_252249641299 : Nat.Prime 252249641299 := by
  apply nodeValid_prime [2, 3, 17, 167, 257, 19207] ⟨252249641299, 2, [(2, 1), (3, 2), (17, 1), (167, 1), (257, 1), (19207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_167
    · exact prime_257
    · exact prime_19207
  · decide +kernel

theorem prime_252762324907 : Nat.Prime 252762324907 := by
  apply nodeValid_prime [2, 3, 7, 13, 66133523] ⟨252762324907, 3, [(2, 1), (3, 1), (7, 2), (13, 1), (66133523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_66133523
  · decide +kernel

theorem prime_252762324937 : Nat.Prime 252762324937 := by
  apply nodeValid_prime [2, 3, 11, 193, 277, 17909] ⟨252762324937, 7, [(2, 3), (3, 1), (11, 1), (193, 1), (277, 1), (17909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193
    · exact prime_277
    · exact prime_17909
  · decide +kernel

theorem prime_252762337231 : Nat.Prime 252762337231 := by
  apply nodeValid_prime [2, 3, 5, 13, 443, 1462999] ⟨252762337231, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (443, 1), (1462999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_443
    · exact prime_1462999
  · decide +kernel

theorem prime_253275730523 : Nat.Prime 253275730523 := by
  apply nodeValid_prime [2, 41, 6037, 511633] ⟨253275730523, 2, [(2, 1), (41, 1), (6037, 1), (511633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_6037
    · exact prime_511633
  · decide +kernel

theorem prime_253275731041 : Nat.Prime 253275731041 := by
  apply nodeValid_prime [2, 3, 5, 43, 103, 109, 1093] ⟨253275731041, 17, [(2, 5), (3, 1), (5, 1), (43, 1), (103, 1), (109, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_103
    · exact prime_109
    · exact prime_1093
  · decide +kernel

theorem prime_253275732601 : Nat.Prime 253275732601 := by
  apply nodeValid_prime [2, 3, 5, 11, 38375111] ⟨253275732601, 7, [(2, 3), (3, 1), (5, 2), (11, 1), (38375111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_38375111
  · decide +kernel

theorem prime_253789832899 : Nat.Prime 253789832899 := by
  apply nodeValid_prime [2, 3, 7, 877, 2296699] ⟨253789832899, 3, [(2, 1), (3, 2), (7, 1), (877, 1), (2296699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_877
    · exact prime_2296699
  · decide +kernel

theorem prime_253789842979 : Nat.Prime 253789842979 := by
  apply nodeValid_prime [2, 3, 7, 2203, 33863] ⟨253789842979, 22, [(2, 1), (3, 5), (7, 1), (2203, 1), (33863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2203
    · exact prime_33863
  · decide +kernel

theorem prime_253789847293 : Nat.Prime 253789847293 := by
  apply nodeValid_prime [2, 3, 8039, 2630819] ⟨253789847293, 2, [(2, 2), (3, 1), (8039, 1), (2630819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8039
    · exact prime_2630819
  · decide +kernel

theorem prime_254304625819 : Nat.Prime 254304625819 := by
  apply nodeValid_prime [2, 3, 62903, 673801] ⟨254304625819, 2, [(2, 1), (3, 1), (62903, 1), (673801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62903
    · exact prime_673801
  · decide +kernel

theorem prime_254304625933 : Nat.Prime 254304625933 := by
  apply nodeValid_prime [2, 3, 7, 41, 1811, 13591] ⟨254304625933, 5, [(2, 2), (3, 2), (7, 1), (41, 1), (1811, 1), (13591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_1811
    · exact prime_13591
  · decide +kernel

theorem prime_254304643039 : Nat.Prime 254304643039 := by
  apply nodeValid_prime [2, 3, 29, 43, 33988859] ⟨254304643039, 6, [(2, 1), (3, 1), (29, 1), (43, 1), (33988859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
    · exact prime_33988859
  · decide +kernel

theorem prime_254820137029 : Nat.Prime 254820137029 := by
  apply nodeValid_prime [2, 3, 167, 127155757] ⟨254820137029, 2, [(2, 2), (3, 1), (167, 1), (127155757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_127155757
  · decide +kernel

theorem prime_254820137329 : Nat.Prime 254820137329 := by
  apply nodeValid_prime [2, 3, 131, 4502759] ⟨254820137329, 11, [(2, 4), (3, 3), (131, 1), (4502759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_4502759
  · decide +kernel

theorem prime_254820157519 : Nat.Prime 254820157519 := by
  apply nodeValid_prime [2, 3, 198013, 214481] ⟨254820157519, 3, [(2, 1), (3, 1), (198013, 1), (214481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_198013
    · exact prime_214481
  · decide +kernel

theorem prime_255336378313 : Nat.Prime 255336378313 := by
  apply nodeValid_prime [2, 3, 4759, 2235557] ⟨255336378313, 10, [(2, 3), (3, 1), (4759, 1), (2235557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4759
    · exact prime_2235557
  · decide +kernel

theorem prime_255336411377 : Nat.Prime 255336411377 := by
  apply nodeValid_prime [2, 15958525711] ⟨255336411377, 3, [(2, 4), (15958525711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15958525711
  · decide +kernel

theorem prime_255336411413 : Nat.Prime 255336411413 := by
  apply nodeValid_prime [2, 151, 10177, 41539] ⟨255336411413, 2, [(2, 2), (151, 1), (10177, 1), (41539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_10177
    · exact prime_41539
  · decide +kernel

theorem prime_255853311589 : Nat.Prime 255853311589 := by
  apply nodeValid_prime [2, 3, 7, 2749, 369331] ⟨255853311589, 2, [(2, 2), (3, 2), (7, 1), (2749, 1), (369331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2749
    · exact prime_369331
  · decide +kernel

theorem prime_255853332179 : Nat.Prime 255853332179 := by
  apply nodeValid_prime [2, 383, 334012183] ⟨255853332179, 2, [(2, 1), (383, 1), (334012183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_334012183
  · decide +kernel

theorem prime_255853332377 : Nat.Prime 255853332377 := by
  apply nodeValid_prime [2, 31981666547] ⟨255853332377, 3, [(2, 3), (31981666547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31981666547
  · decide +kernel

theorem prime_256370957033 : Nat.Prime 256370957033 := by
  apply nodeValid_prime [2, 31, 1033753859] ⟨256370957033, 3, [(2, 3), (31, 1), (1033753859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1033753859
  · decide +kernel

theorem prime_256370963183 : Nat.Prime 256370963183 := by
  apply nodeValid_prime [2, 601, 213286991] ⟨256370963183, 5, [(2, 1), (601, 1), (213286991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_213286991
  · decide +kernel

theorem prime_256370963587 : Nat.Prime 256370963587 := by
  apply nodeValid_prime [2, 3, 42728493931] ⟨256370963587, 2, [(2, 1), (3, 1), (42728493931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42728493931
  · decide +kernel

theorem prime_256889307931 : Nat.Prime 256889307931 := by
  apply nodeValid_prime [2, 3, 5, 61, 307, 457253] ⟨256889307931, 2, [(2, 1), (3, 1), (5, 1), (61, 1), (307, 1), (457253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_307
    · exact prime_457253
  · decide +kernel

theorem prime_256889316679 : Nat.Prime 256889316679 := by
  apply nodeValid_prime [2, 3, 1301, 4987, 6599] ⟨256889316679, 3, [(2, 1), (3, 1), (1301, 1), (4987, 1), (6599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1301
    · exact prime_4987
    · exact prime_6599
  · decide +kernel

theorem prime_256889316829 : Nat.Prime 256889316829 := by
  apply nodeValid_prime [2, 3, 17, 1259261357] ⟨256889316829, 2, [(2, 2), (3, 1), (17, 1), (1259261357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1259261357
  · decide +kernel

theorem prime_257408362979 : Nat.Prime 257408362979 := by
  apply nodeValid_prime [2, 13, 9900321653] ⟨257408362979, 2, [(2, 1), (13, 1), (9900321653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_9900321653
  · decide +kernel

theorem prime_257408370139 : Nat.Prime 257408370139 := by
  apply nodeValid_prime [2, 3, 43, 997706861] ⟨257408370139, 2, [(2, 1), (3, 1), (43, 1), (997706861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_997706861
  · decide +kernel

theorem prime_257408371273 : Nat.Prime 257408371273 := by
  apply nodeValid_prime [2, 3, 13, 1549, 532619] ⟨257408371273, 5, [(2, 3), (3, 1), (13, 1), (1549, 1), (532619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1549
    · exact prime_532619
  · decide +kernel

theorem prime_257928128819 : Nat.Prime 257928128819 := by
  apply nodeValid_prime [2, 128964064409] ⟨257928128819, 2, [(2, 1), (128964064409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_128964064409
  · decide +kernel

theorem prime_257928140279 : Nat.Prime 257928140279 := by
  apply nodeValid_prime [2, 227, 15131, 37547] ⟨257928140279, 17, [(2, 1), (227, 1), (15131, 1), (37547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_15131
    · exact prime_37547
  · decide +kernel

theorem prime_257928140611 : Nat.Prime 257928140611 := by
  apply nodeValid_prime [2, 3, 5, 7, 409409747] ⟨257928140611, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (409409747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_409409747
  · decide +kernel

theorem prime_258448597061 : Nat.Prime 258448597061 := by
  apply nodeValid_prime [2, 5, 19, 271, 1213, 2069] ⟨258448597061, 2, [(2, 2), (5, 1), (19, 1), (271, 1), (1213, 1), (2069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_271
    · exact prime_1213
    · exact prime_2069
  · decide +kernel

theorem prime_258448597739 : Nat.Prime 258448597739 := by
  apply nodeValid_prime [2, 61, 2118431129] ⟨258448597739, 2, [(2, 1), (61, 1), (2118431129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_2118431129
  · decide +kernel

theorem prime_258448606007 : Nat.Prime 258448606007 := by
  apply nodeValid_prime [2, 129224303003] ⟨258448606007, 5, [(2, 1), (129224303003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_129224303003
  · decide +kernel

end Sude.Lucas.Generated
