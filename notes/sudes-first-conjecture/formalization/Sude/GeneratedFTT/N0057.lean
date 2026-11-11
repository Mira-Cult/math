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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3169 : Nat.Prime 3169 := by
  apply nodeValid_prime [2, 3, 11] ⟨3169, 7, [(2, 5), (3, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_6883 : Nat.Prime 6883 := by
  apply nodeValid_prime [2, 3, 31, 37] ⟨6883, 2, [(2, 1), (3, 1), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_9127 : Nat.Prime 9127 := by
  apply nodeValid_prime [2, 3, 13] ⟨9127, 3, [(2, 1), (3, 3), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_10559 : Nat.Prime 10559 := by
  apply nodeValid_prime [2, 5279] ⟨10559, 23, [(2, 1), (5279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5279
  · decide +kernel

theorem prime_11177 : Nat.Prime 11177 := by
  apply nodeValid_prime [2, 11, 127] ⟨11177, 3, [(2, 3), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_12269 : Nat.Prime 12269 := by
  apply nodeValid_prime [2, 3067] ⟨12269, 2, [(2, 2), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3067
  · decide +kernel

theorem prime_13901 : Nat.Prime 13901 := by
  apply nodeValid_prime [2, 5, 139] ⟨13901, 2, [(2, 2), (5, 2), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
  · decide +kernel

theorem prime_15749 : Nat.Prime 15749 := by
  apply nodeValid_prime [2, 31, 127] ⟨15749, 2, [(2, 2), (31, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_127
  · decide +kernel

theorem prime_16427 : Nat.Prime 16427 := by
  apply nodeValid_prime [2, 43, 191] ⟨16427, 2, [(2, 1), (43, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_191
  · decide +kernel

theorem prime_20719 : Nat.Prime 20719 := by
  apply nodeValid_prime [2, 3, 1151] ⟨20719, 3, [(2, 1), (3, 2), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1151
  · decide +kernel

theorem prime_22273 : Nat.Prime 22273 := by
  apply nodeValid_prime [2, 3, 29] ⟨22273, 5, [(2, 8), (3, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_22567 : Nat.Prime 22567 := by
  apply nodeValid_prime [2, 3, 3761] ⟨22567, 3, [(2, 1), (3, 1), (3761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3761
  · decide +kernel

theorem prime_24197 : Nat.Prime 24197 := by
  apply nodeValid_prime [2, 23, 263] ⟨24197, 2, [(2, 2), (23, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_263
  · decide +kernel

theorem prime_26371 : Nat.Prime 26371 := by
  apply nodeValid_prime [2, 3, 5, 293] ⟨26371, 3, [(2, 1), (3, 2), (5, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
  · decide +kernel

theorem prime_33049 : Nat.Prime 33049 := by
  apply nodeValid_prime [2, 3, 17] ⟨33049, 29, [(2, 3), (3, 5), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_35437 : Nat.Prime 35437 := by
  apply nodeValid_prime [2, 3, 2953] ⟨35437, 6, [(2, 2), (3, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2953
  · decide +kernel

theorem prime_36457 : Nat.Prime 36457 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨36457, 5, [(2, 3), (3, 1), (7, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_37361 : Nat.Prime 37361 := by
  apply nodeValid_prime [2, 5, 467] ⟨37361, 3, [(2, 4), (5, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_467
  · decide +kernel

theorem prime_41737 : Nat.Prime 41737 := by
  apply nodeValid_prime [2, 3, 37, 47] ⟨41737, 5, [(2, 3), (3, 1), (37, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_47
  · decide +kernel

theorem prime_49193 : Nat.Prime 49193 := by
  apply nodeValid_prime [2, 11, 13, 43] ⟨49193, 3, [(2, 3), (11, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_54877 : Nat.Prime 54877 := by
  apply nodeValid_prime [2, 3, 17, 269] ⟨54877, 2, [(2, 2), (3, 1), (17, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_269
  · decide +kernel

theorem prime_60919 : Nat.Prime 60919 := by
  apply nodeValid_prime [2, 3, 11, 13, 71] ⟨60919, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_65699 : Nat.Prime 65699 := by
  apply nodeValid_prime [2, 107, 307] ⟨65699, 2, [(2, 1), (107, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_307
  · decide +kernel

theorem prime_67559 : Nat.Prime 67559 := by
  apply nodeValid_prime [2, 17, 1987] ⟨67559, 7, [(2, 1), (17, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1987
  · decide +kernel

theorem prime_74959 : Nat.Prime 74959 := by
  apply nodeValid_prime [2, 3, 13, 31] ⟨74959, 3, [(2, 1), (3, 1), (13, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_84313 : Nat.Prime 84313 := by
  apply nodeValid_prime [2, 3, 1171] ⟨84313, 5, [(2, 3), (3, 2), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1171
  · decide +kernel

theorem prime_86861 : Nat.Prime 86861 := by
  apply nodeValid_prime [2, 5, 43, 101] ⟨86861, 2, [(2, 2), (5, 1), (43, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_101
  · decide +kernel

theorem prime_108439 : Nat.Prime 108439 := by
  apply nodeValid_prime [2, 3, 11, 31, 53] ⟨108439, 3, [(2, 1), (3, 1), (11, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_115061 : Nat.Prime 115061 := by
  apply nodeValid_prime [2, 5, 11, 523] ⟨115061, 3, [(2, 2), (5, 1), (11, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_523
  · decide +kernel

theorem prime_123833 : Nat.Prime 123833 := by
  apply nodeValid_prime [2, 23, 673] ⟨123833, 3, [(2, 3), (23, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_673
  · decide +kernel

theorem prime_128339 : Nat.Prime 128339 := by
  apply nodeValid_prime [2, 7, 89, 103] ⟨128339, 2, [(2, 1), (7, 1), (89, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_103
  · decide +kernel

theorem prime_135403 : Nat.Prime 135403 := by
  apply nodeValid_prime [2, 3, 22567] ⟨135403, 2, [(2, 1), (3, 1), (22567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22567
  · decide +kernel

theorem prime_145829 : Nat.Prime 145829 := by
  apply nodeValid_prime [2, 36457] ⟨145829, 2, [(2, 2), (36457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36457
  · decide +kernel

theorem prime_158227 : Nat.Prime 158227 := by
  apply nodeValid_prime [2, 3, 26371] ⟨158227, 3, [(2, 1), (3, 1), (26371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26371
  · decide +kernel

theorem prime_160387 : Nat.Prime 160387 := by
  apply nodeValid_prime [2, 3, 26731] ⟨160387, 2, [(2, 1), (3, 1), (26731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26731
  · decide +kernel

theorem prime_181603 : Nat.Prime 181603 := by
  apply nodeValid_prime [2, 3, 19, 59] ⟨181603, 3, [(2, 1), (3, 4), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_197957 : Nat.Prime 197957 := by
  apply nodeValid_prime [2, 11, 409] ⟨197957, 2, [(2, 2), (11, 2), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_409
  · decide +kernel

theorem prime_207191 : Nat.Prime 207191 := by
  apply nodeValid_prime [2, 5, 20719] ⟨207191, 17, [(2, 1), (5, 1), (20719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20719
  · decide +kernel

theorem prime_220021 : Nat.Prime 220021 := by
  apply nodeValid_prime [2, 3, 5, 19, 193] ⟨220021, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_193
  · decide +kernel

theorem prime_230123 : Nat.Prime 230123 := by
  apply nodeValid_prime [2, 115061] ⟨230123, 2, [(2, 1), (115061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115061
  · decide +kernel

theorem prime_250423 : Nat.Prime 250423 := by
  apply nodeValid_prime [2, 3, 41737] ⟨250423, 21, [(2, 1), (3, 1), (41737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41737
  · decide +kernel

theorem prime_260747 : Nat.Prime 260747 := by
  apply nodeValid_prime [2, 17, 7669] ⟨260747, 2, [(2, 1), (17, 1), (7669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_7669
  · decide +kernel

theorem prime_262387 : Nat.Prime 262387 := by
  apply nodeValid_prime [2, 3, 43, 113] ⟨262387, 5, [(2, 1), (3, 3), (43, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_113
  · decide +kernel

theorem prime_277789 : Nat.Prime 277789 := by
  apply nodeValid_prime [2, 3, 7, 3307] ⟨277789, 6, [(2, 2), (3, 1), (7, 1), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3307
  · decide +kernel

theorem prime_313721 : Nat.Prime 313721 := by
  apply nodeValid_prime [2, 5, 11, 23, 31] ⟨313721, 3, [(2, 3), (5, 1), (11, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_334721 : Nat.Prime 334721 := by
  apply nodeValid_prime [2, 5, 523] ⟨334721, 3, [(2, 7), (5, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_523
  · decide +kernel

theorem prime_394249 : Nat.Prime 394249 := by
  apply nodeValid_prime [2, 3, 16427] ⟨394249, 13, [(2, 3), (3, 1), (16427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16427
  · decide +kernel

theorem prime_418351 : Nat.Prime 418351 := by
  apply nodeValid_prime [2, 3, 5, 2789] ⟨418351, 3, [(2, 1), (3, 1), (5, 2), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2789
  · decide +kernel

theorem prime_443759 : Nat.Prime 443759 := by
  apply nodeValid_prime [2, 7, 29, 1093] ⟨443759, 7, [(2, 1), (7, 1), (29, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_1093
  · decide +kernel

theorem prime_519581 : Nat.Prime 519581 := by
  apply nodeValid_prime [2, 5, 83, 313] ⟨519581, 2, [(2, 2), (5, 1), (83, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_313
  · decide +kernel

theorem prime_592321 : Nat.Prime 592321 := by
  apply nodeValid_prime [2, 3, 5, 617] ⟨592321, 13, [(2, 6), (3, 1), (5, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_617
  · decide +kernel

theorem prime_625777 : Nat.Prime 625777 := by
  apply nodeValid_prime [2, 3, 13037] ⟨625777, 5, [(2, 4), (3, 1), (13037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13037
  · decide +kernel

theorem prime_641549 : Nat.Prime 641549 := by
  apply nodeValid_prime [2, 160387] ⟨641549, 2, [(2, 2), (160387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160387
  · decide +kernel

theorem prime_647081 : Nat.Prime 647081 := by
  apply nodeValid_prime [2, 5, 7, 2311] ⟨647081, 3, [(2, 3), (5, 1), (7, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2311
  · decide +kernel

theorem prime_654029 : Nat.Prime 654029 := by
  apply nodeValid_prime [2, 23, 7109] ⟨654029, 2, [(2, 2), (23, 1), (7109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_7109
  · decide +kernel

theorem prime_663737 : Nat.Prime 663737 := by
  apply nodeValid_prime [2, 163, 509] ⟨663737, 3, [(2, 3), (163, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_509
  · decide +kernel

theorem prime_669937 : Nat.Prime 669937 := by
  apply nodeValid_prime [2, 3, 17, 821] ⟨669937, 5, [(2, 4), (3, 1), (17, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_821
  · decide +kernel

theorem prime_676069 : Nat.Prime 676069 := by
  apply nodeValid_prime [2, 3, 53, 1063] ⟨676069, 2, [(2, 2), (3, 1), (53, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1063
  · decide +kernel

theorem prime_768221 : Nat.Prime 768221 := by
  apply nodeValid_prime [2, 5, 71, 541] ⟨768221, 2, [(2, 2), (5, 1), (71, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_541
  · decide +kernel

theorem prime_821861 : Nat.Prime 821861 := by
  apply nodeValid_prime [2, 5, 13, 29, 109] ⟨821861, 3, [(2, 2), (5, 1), (13, 1), (29, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
    · exact prime_109
  · decide +kernel

theorem prime_902179 : Nat.Prime 902179 := by
  apply nodeValid_prime [2, 3, 5569] ⟨902179, 2, [(2, 1), (3, 4), (5569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5569
  · decide +kernel

theorem prime_1042703 : Nat.Prime 1042703 := by
  apply nodeValid_prime [2, 149, 3499] ⟨1042703, 5, [(2, 1), (149, 1), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_3499
  · decide +kernel

theorem prime_1096621 : Nat.Prime 1096621 := by
  apply nodeValid_prime [2, 3, 5, 7, 373] ⟨1096621, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_373
  · decide +kernel

theorem prime_1127561 : Nat.Prime 1127561 := by
  apply nodeValid_prime [2, 5, 7, 4027] ⟨1127561, 3, [(2, 3), (5, 1), (7, 1), (4027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_4027
  · decide +kernel

theorem prime_1173853 : Nat.Prime 1173853 := by
  apply nodeValid_prime [2, 3, 3623] ⟨1173853, 5, [(2, 2), (3, 4), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3623
  · decide +kernel

theorem prime_1243147 : Nat.Prime 1243147 := by
  apply nodeValid_prime [2, 3, 207191] ⟨1243147, 2, [(2, 1), (3, 1), (207191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_207191
  · decide +kernel

theorem prime_1283099 : Nat.Prime 1283099 := by
  apply nodeValid_prime [2, 641549] ⟨1283099, 2, [(2, 1), (641549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_641549
  · decide +kernel

theorem prime_1298291 : Nat.Prime 1298291 := by
  apply nodeValid_prime [2, 5, 7, 17, 1091] ⟨1298291, 2, [(2, 1), (5, 1), (7, 1), (17, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_1091
  · decide +kernel

theorem prime_1322917 : Nat.Prime 1322917 := by
  apply nodeValid_prime [2, 3, 7, 15749] ⟨1322917, 2, [(2, 2), (3, 1), (7, 1), (15749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_15749
  · decide +kernel

theorem prime_1380653 : Nat.Prime 1380653 := by
  apply nodeValid_prime [2, 7, 13, 3793] ⟨1380653, 2, [(2, 2), (7, 1), (13, 1), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_3793
  · decide +kernel

theorem prime_1882327 : Nat.Prime 1882327 := by
  apply nodeValid_prime [2, 3, 313721] ⟨1882327, 3, [(2, 1), (3, 1), (313721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313721
  · decide +kernel

theorem prime_1975573 : Nat.Prime 1975573 := by
  apply nodeValid_prime [2, 3, 54877] ⟨1975573, 2, [(2, 2), (3, 2), (54877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54877
  · decide +kernel

theorem prime_2412271 : Nat.Prime 2412271 := by
  apply nodeValid_prime [2, 3, 5, 7, 547] ⟨2412271, 6, [(2, 1), (3, 2), (5, 1), (7, 2), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_547
  · decide +kernel

theorem prime_2761477 : Nat.Prime 2761477 := by
  apply nodeValid_prime [2, 3, 230123] ⟨2761477, 2, [(2, 2), (3, 1), (230123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_230123
  · decide +kernel

theorem prime_2868799 : Nat.Prime 2868799 := by
  apply nodeValid_prime [2, 3, 647, 739] ⟨2868799, 3, [(2, 1), (3, 1), (647, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_647
    · exact prime_739
  · decide +kernel

theorem prime_3282689 : Nat.Prime 3282689 := by
  apply nodeValid_prime [2, 12823] ⟨3282689, 3, [(2, 8), (12823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12823
  · decide +kernel

theorem prime_3535117 : Nat.Prime 3535117 := by
  apply nodeValid_prime [2, 3, 13, 17, 31, 43] ⟨3535117, 5, [(2, 2), (3, 1), (13, 1), (17, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_4023179 : Nat.Prime 4023179 := by
  apply nodeValid_prime [2, 373, 5393] ⟨4023179, 2, [(2, 1), (373, 1), (5393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_5393
  · decide +kernel

theorem prime_4972589 : Nat.Prime 4972589 := by
  apply nodeValid_prime [2, 1243147] ⟨4972589, 2, [(2, 2), (1243147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1243147
  · decide +kernel

theorem prime_8268031 : Nat.Prime 8268031 := by
  apply nodeValid_prime [2, 3, 5, 91867] ⟨8268031, 3, [(2, 1), (3, 2), (5, 1), (91867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_91867
  · decide +kernel

theorem prime_15579493 : Nat.Prime 15579493 := by
  apply nodeValid_prime [2, 3, 1298291] ⟨15579493, 2, [(2, 2), (3, 1), (1298291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1298291
  · decide +kernel

theorem prime_16567763 : Nat.Prime 16567763 := by
  apply nodeValid_prime [2, 257, 32233] ⟨16567763, 2, [(2, 1), (257, 1), (32233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_32233
  · decide +kernel

theorem prime_17788349 : Nat.Prime 17788349 := by
  apply nodeValid_prime [2, 73, 60919] ⟨17788349, 2, [(2, 2), (73, 1), (60919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_60919
  · decide +kernel

theorem prime_26402521 : Nat.Prime 26402521 := by
  apply nodeValid_prime [2, 3, 5, 220021] ⟨26402521, 7, [(2, 3), (3, 1), (5, 1), (220021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_220021
  · decide +kernel

theorem prime_26797481 : Nat.Prime 26797481 := by
  apply nodeValid_prime [2, 5, 669937] ⟨26797481, 3, [(2, 3), (5, 1), (669937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_669937
  · decide +kernel

theorem prime_31790723 : Nat.Prime 31790723 := by
  apply nodeValid_prime [2, 109, 145829] ⟨31790723, 2, [(2, 1), (109, 1), (145829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_145829
  · decide +kernel

theorem prime_36409661 : Nat.Prime 36409661 := by
  apply nodeValid_prime [2, 5, 7, 139, 1871] ⟨36409661, 2, [(2, 2), (5, 1), (7, 1), (139, 1), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_139
    · exact prime_1871
  · decide +kernel

theorem prime_39309341 : Nat.Prime 39309341 := by
  apply nodeValid_prime [2, 5, 7, 59, 4759] ⟨39309341, 2, [(2, 2), (5, 1), (7, 1), (59, 1), (4759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_4759
  · decide +kernel

theorem prime_40244521 : Nat.Prime 40244521 := by
  apply nodeValid_prime [2, 3, 5, 151, 2221] ⟨40244521, 19, [(2, 3), (3, 1), (5, 1), (151, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_2221
  · decide +kernel

theorem prime_40807493 : Nat.Prime 40807493 := by
  apply nodeValid_prime [2, 11, 84313] ⟨40807493, 2, [(2, 2), (11, 2), (84313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_84313
  · decide +kernel

theorem prime_44347493 : Nat.Prime 44347493 := by
  apply nodeValid_prime [2, 7, 17, 151, 617] ⟨44347493, 2, [(2, 2), (7, 1), (17, 1), (151, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_151
    · exact prime_617
  · decide +kernel

theorem prime_47520439 : Nat.Prime 47520439 := by
  apply nodeValid_prime [2, 3, 7, 23, 49193] ⟨47520439, 6, [(2, 1), (3, 1), (7, 1), (23, 1), (49193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_49193
  · decide +kernel

theorem prime_52733383 : Nat.Prime 52733383 := by
  apply nodeValid_prime [2, 3, 13, 676069] ⟨52733383, 3, [(2, 1), (3, 1), (13, 1), (676069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_676069
  · decide +kernel

theorem prime_53594963 : Nat.Prime 53594963 := by
  apply nodeValid_prime [2, 26797481] ⟨53594963, 2, [(2, 1), (26797481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26797481
  · decide +kernel

theorem prime_53997239 : Nat.Prime 53997239 := by
  apply nodeValid_prime [2, 23, 1173853] ⟨53997239, 7, [(2, 1), (23, 1), (1173853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1173853
  · decide +kernel

theorem prime_59321539 : Nat.Prime 59321539 := by
  apply nodeValid_prime [2, 3, 31, 35437] ⟨59321539, 2, [(2, 1), (3, 3), (31, 1), (35437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_35437
  · decide +kernel

theorem prime_83915197 : Nat.Prime 83915197 := by
  apply nodeValid_prime [2, 3, 17, 24197] ⟨83915197, 6, [(2, 2), (3, 1), (17, 2), (24197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_24197
  · decide +kernel

theorem prime_107389679 : Nat.Prime 107389679 := by
  apply nodeValid_prime [2, 11, 443759] ⟨107389679, 11, [(2, 1), (11, 2), (443759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_443759
  · decide +kernel

theorem prime_141326033 : Nat.Prime 141326033 := by
  apply nodeValid_prime [2, 17, 519581] ⟨141326033, 3, [(2, 4), (17, 1), (519581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_519581
  · decide +kernel

theorem prime_189729343 : Nat.Prime 189729343 := by
  apply nodeValid_prime [2, 3, 11, 433, 2213] ⟨189729343, 3, [(2, 1), (3, 2), (11, 1), (433, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_433
    · exact prime_2213
  · decide +kernel

theorem prime_209438507 : Nat.Prime 209438507 := by
  apply nodeValid_prime [2, 23, 197957] ⟨209438507, 2, [(2, 1), (23, 2), (197957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_197957
  · decide +kernel

theorem prime_395194493 : Nat.Prime 395194493 := by
  apply nodeValid_prime [2, 7, 11, 1283099] ⟨395194493, 2, [(2, 2), (7, 1), (11, 1), (1283099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1283099
  · decide +kernel

theorem prime_461587747 : Nat.Prime 461587747 := by
  apply nodeValid_prime [2, 3, 6883, 11177] ⟨461587747, 2, [(2, 1), (3, 1), (6883, 1), (11177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6883
    · exact prime_11177
  · decide +kernel

theorem prime_527447131 : Nat.Prime 527447131 := by
  apply nodeValid_prime [2, 3, 5, 7, 269, 9337] ⟨527447131, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (269, 1), (9337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_269
    · exact prime_9337
  · decide +kernel

theorem prime_560430623 : Nat.Prime 560430623 := by
  apply nodeValid_prime [2, 103, 239, 11383] ⟨560430623, 5, [(2, 1), (103, 1), (239, 1), (11383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_239
    · exact prime_11383
  · decide +kernel

theorem prime_705591869 : Nat.Prime 705591869 := by
  apply nodeValid_prime [2, 17, 31, 334721] ⟨705591869, 2, [(2, 2), (17, 1), (31, 1), (334721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_334721
  · decide +kernel

theorem prime_739270589 : Nat.Prime 739270589 := by
  apply nodeValid_prime [2, 7, 26402521] ⟨739270589, 2, [(2, 2), (7, 1), (26402521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_26402521
  · decide +kernel

theorem prime_994517801 : Nat.Prime 994517801 := by
  apply nodeValid_prime [2, 5, 4972589] ⟨994517801, 3, [(2, 3), (5, 2), (4972589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4972589
  · decide +kernel

theorem prime_1326944107 : Nat.Prime 1326944107 := by
  apply nodeValid_prime [2, 3, 23, 223, 1597] ⟨1326944107, 3, [(2, 1), (3, 4), (23, 1), (223, 1), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_223
    · exact prime_1597
  · decide +kernel

theorem prime_1481296151 : Nat.Prime 1481296151 := by
  apply nodeValid_prime [2, 5, 3727, 7949] ⟨1481296151, 11, [(2, 1), (5, 2), (3727, 1), (7949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3727
    · exact prime_7949
  · decide +kernel

theorem prime_2500779263 : Nat.Prime 2500779263 := by
  apply nodeValid_prime [2, 2111, 592321] ⟨2500779263, 5, [(2, 1), (2111, 1), (592321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2111
    · exact prime_592321
  · decide +kernel

theorem prime_3164765953 : Nat.Prime 3164765953 := by
  apply nodeValid_prime [2, 3, 89, 46301] ⟨3164765953, 5, [(2, 8), (3, 1), (89, 1), (46301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_46301
  · decide +kernel

theorem prime_3317319197 : Nat.Prime 3317319197 := by
  apply nodeValid_prime [2, 3511, 236209] ⟨3317319197, 2, [(2, 2), (3511, 1), (236209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3511
    · exact prime_236209
  · decide +kernel

theorem prime_4235070167 : Nat.Prime 4235070167 := by
  apply nodeValid_prime [2, 599, 3535117] ⟨4235070167, 5, [(2, 1), (599, 1), (3535117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_599
    · exact prime_3535117
  · decide +kernel

theorem prime_5274471311 : Nat.Prime 5274471311 := by
  apply nodeValid_prime [2, 5, 527447131] ⟨5274471311, 7, [(2, 1), (5, 1), (527447131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_527447131
  · decide +kernel

theorem prime_7079762903 : Nat.Prime 7079762903 := by
  apply nodeValid_prime [2, 199, 17788349] ⟨7079762903, 5, [(2, 1), (199, 1), (17788349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_17788349
  · decide +kernel

theorem prime_8035467763 : Nat.Prime 8035467763 := by
  apply nodeValid_prime [2, 3, 7, 827, 33049] ⟨8035467763, 2, [(2, 1), (3, 1), (7, 2), (827, 1), (33049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_827
    · exact prime_33049
  · decide +kernel

theorem prime_8647076657 : Nat.Prime 8647076657 := by
  apply nodeValid_prime [2, 17, 31790723] ⟨8647076657, 3, [(2, 4), (17, 1), (31790723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31790723
  · decide +kernel

theorem prime_8762214047 : Nat.Prime 8762214047 := by
  apply nodeValid_prime [2, 31, 141326033] ⟨8762214047, 5, [(2, 1), (31, 1), (141326033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_141326033
  · decide +kernel

theorem prime_9849462683 : Nat.Prime 9849462683 := by
  apply nodeValid_prime [2, 65699, 74959] ⟨9849462683, 2, [(2, 1), (65699, 1), (74959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_65699
    · exact prime_74959
  · decide +kernel

theorem prime_13478212081 : Nat.Prime 13478212081 := by
  apply nodeValid_prime [2, 3, 5, 41, 97, 523] ⟨13478212081, 21, [(2, 4), (3, 4), (5, 1), (41, 1), (97, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_97
    · exact prime_523
  · decide +kernel

theorem prime_28417222523 : Nat.Prime 28417222523 := by
  apply nodeValid_prime [2, 13, 23, 47520439] ⟨28417222523, 2, [(2, 1), (13, 1), (23, 1), (47520439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_47520439
  · decide +kernel

theorem prime_31680739889 : Nat.Prime 31680739889 := by
  apply nodeValid_prime [2, 7, 67, 139, 4339] ⟨31680739889, 3, [(2, 4), (7, 2), (67, 1), (139, 1), (4339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_139
    · exact prime_4339
  · decide +kernel

theorem prime_34277447227 : Nat.Prime 34277447227 := by
  apply nodeValid_prime [2, 3, 11, 13901, 37361] ⟨34277447227, 3, [(2, 1), (3, 1), (11, 1), (13901, 1), (37361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13901
    · exact prime_37361
  · decide +kernel

theorem prime_39296040593 : Nat.Prime 39296040593 := by
  apply nodeValid_prime [2, 23, 139, 768221] ⟨39296040593, 3, [(2, 4), (23, 1), (139, 1), (768221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_139
    · exact prime_768221
  · decide +kernel

theorem prime_42736225159 : Nat.Prime 42736225159 := by
  apply nodeValid_prime [2, 3, 11, 23, 1042703] ⟨42736225159, 3, [(2, 1), (3, 4), (11, 1), (23, 1), (1042703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_1042703
  · decide +kernel

theorem prime_57350739049 : Nat.Prime 57350739049 := by
  apply nodeValid_prime [2, 3, 53, 71, 691, 919] ⟨57350739049, 13, [(2, 3), (3, 1), (53, 1), (71, 1), (691, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_71
    · exact prime_691
    · exact prime_919
  · decide +kernel

theorem prime_57572969969 : Nat.Prime 57572969969 := by
  apply nodeValid_prime [2, 9127, 394249] ⟨57572969969, 3, [(2, 4), (9127, 1), (394249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9127
    · exact prime_394249
  · decide +kernel

theorem prime_86137121723 : Nat.Prime 86137121723 := by
  apply nodeValid_prime [2, 227, 189729343] ⟨86137121723, 2, [(2, 1), (227, 1), (189729343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_189729343
  · decide +kernel

theorem prime_86693681653 : Nat.Prime 86693681653 := by
  apply nodeValid_prime [2, 3, 137, 52733383] ⟨86693681653, 5, [(2, 2), (3, 1), (137, 1), (52733383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_52733383
  · decide +kernel

theorem prime_170724020977 : Nat.Prime 170724020977 := by
  apply nodeValid_prime [2, 3, 395194493] ⟨170724020977, 5, [(2, 4), (3, 3), (395194493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_395194493
  · decide +kernel

theorem prime_171830351881 : Nat.Prime 171830351881 := by
  apply nodeValid_prime [2, 3, 5, 11, 157, 313, 883] ⟨171830351881, 17, [(2, 3), (3, 2), (5, 1), (11, 1), (157, 1), (313, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_157
    · exact prime_313
    · exact prime_883
  · decide +kernel

theorem prime_1012468825843 : Nat.Prime 1012468825843 := by
  apply nodeValid_prime [2, 3, 251, 1607, 418351] ⟨1012468825843, 2, [(2, 1), (3, 1), (251, 1), (1607, 1), (418351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_1607
    · exact prime_418351
  · decide +kernel

theorem prime_1012468938139 : Nat.Prime 1012468938139 := by
  apply nodeValid_prime [2, 3, 7, 8035467763] ⟨1012468938139, 7, [(2, 1), (3, 2), (7, 1), (8035467763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8035467763
  · decide +kernel

theorem prime_1012468940227 : Nat.Prime 1012468940227 := by
  apply nodeValid_prime [2, 3, 39499, 158227] ⟨1012468940227, 2, [(2, 1), (3, 4), (39499, 1), (158227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39499
    · exact prime_158227
  · decide +kernel

theorem prime_1013783676449 : Nat.Prime 1013783676449 := by
  apply nodeValid_prime [2, 31680739889] ⟨1013783676449, 3, [(2, 5), (31680739889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31680739889
  · decide +kernel

theorem prime_1013783689727 : Nat.Prime 1013783689727 := by
  apply nodeValid_prime [2, 83, 127, 283, 367, 463] ⟨1013783689727, 5, [(2, 1), (83, 1), (127, 1), (283, 1), (367, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_127
    · exact prime_283
    · exact prime_367
    · exact prime_463
  · decide +kernel

theorem prime_1013783689981 : Nat.Prime 1013783689981 := by
  apply nodeValid_prime [2, 3, 5, 127, 44347493] ⟨1013783689981, 6, [(2, 2), (3, 2), (5, 1), (127, 1), (44347493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
    · exact prime_44347493
  · decide +kernel

theorem prime_1015099647421 : Nat.Prime 1015099647421 := by
  apply nodeValid_prime [2, 3, 5, 67559, 250423] ⟨1015099647421, 2, [(2, 2), (3, 1), (5, 1), (67559, 1), (250423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67559
    · exact prime_250423
  · decide +kernel

theorem prime_1015099647781 : Nat.Prime 1015099647781 := by
  apply nodeValid_prime [2, 3, 5, 89, 1753, 108439] ⟨1015099647781, 2, [(2, 2), (3, 1), (5, 1), (89, 1), (1753, 1), (108439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_1753
    · exact prime_108439
  · decide +kernel

theorem prime_1015099674283 : Nat.Prime 1015099674283 := by
  apply nodeValid_prime [2, 3, 17, 3317319197] ⟨1015099674283, 2, [(2, 1), (3, 2), (17, 1), (3317319197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3317319197
  · decide +kernel

theorem prime_1016416829453 : Nat.Prime 1016416829453 := by
  apply nodeValid_prime [2, 29, 8762214047] ⟨1016416829453, 2, [(2, 2), (29, 1), (8762214047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_8762214047
  · decide +kernel

theorem prime_1016416839391 : Nat.Prime 1016416839391 := by
  apply nodeValid_prime [2, 3, 5, 12269, 2761477] ⟨1016416839391, 6, [(2, 1), (3, 1), (5, 1), (12269, 1), (2761477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12269
    · exact prime_2761477
  · decide +kernel

theorem prime_1016416840081 : Nat.Prime 1016416840081 := by
  apply nodeValid_prime [2, 3, 5, 4235070167] ⟨1016416840081, 14, [(2, 4), (3, 1), (5, 1), (4235070167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4235070167
  · decide +kernel

theorem prime_1017735132131 : Nat.Prime 1017735132131 := by
  apply nodeValid_prime [2, 5, 123833, 821861] ⟨1017735132131, 2, [(2, 1), (5, 1), (123833, 1), (821861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_123833
    · exact prime_821861
  · decide +kernel

theorem prime_1017735133241 : Nat.Prime 1017735133241 := by
  apply nodeValid_prime [2, 5, 7, 181, 2868799] ⟨1017735133241, 3, [(2, 3), (5, 1), (7, 2), (181, 1), (2868799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_181
    · exact prime_2868799
  · decide +kernel

theorem prime_1017735149579 : Nat.Prime 1017735149579 := by
  apply nodeValid_prime [2, 7, 37, 107, 151, 277, 439] ⟨1017735149579, 2, [(2, 1), (7, 1), (37, 1), (107, 1), (151, 1), (277, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_107
    · exact prime_151
    · exact prime_277
    · exact prime_439
  · decide +kernel

theorem prime_1019054626483 : Nat.Prime 1019054626483 := by
  apply nodeValid_prime [2, 3, 3169, 53594963] ⟨1019054626483, 3, [(2, 1), (3, 1), (3169, 1), (53594963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3169
    · exact prime_53594963
  · decide +kernel

theorem prime_1019054636867 : Nat.Prime 1019054636867 := by
  apply nodeValid_prime [2, 7, 23, 3164765953] ⟨1019054636867, 2, [(2, 1), (7, 1), (23, 1), (3164765953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_3164765953
  · decide +kernel

theorem prime_1019054637131 : Nat.Prime 1019054637131 := by
  apply nodeValid_prime [2, 5, 31, 211, 15579493] ⟨1019054637131, 2, [(2, 1), (5, 1), (31, 1), (211, 1), (15579493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_211
    · exact prime_15579493
  · decide +kernel

theorem prime_1020375263827 : Nat.Prime 1020375263827 := by
  apply nodeValid_prime [2, 3, 19, 994517801] ⟨1020375263827, 2, [(2, 1), (3, 3), (19, 1), (994517801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_994517801
  · decide +kernel

theorem prime_1020375275149 : Nat.Prime 1020375275149 := by
  apply nodeValid_prime [2, 3, 89, 353, 902179] ⟨1020375275149, 6, [(2, 2), (3, 2), (89, 1), (353, 1), (902179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_353
    · exact prime_902179
  · decide +kernel

theorem prime_1020375276421 : Nat.Prime 1020375276421 := by
  apply nodeValid_prime [2, 3, 5, 86861, 195787] ⟨1020375276421, 2, [(2, 2), (3, 1), (5, 1), (86861, 1), (195787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_86861
    · exact prime_195787
  · decide +kernel

theorem prime_1021697026313 : Nat.Prime 1021697026313 := by
  apply nodeValid_prime [2, 181, 705591869] ⟨1021697026313, 3, [(2, 3), (181, 1), (705591869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_705591869
  · decide +kernel

theorem prime_1021697026531 : Nat.Prime 1021697026531 := by
  apply nodeValid_prime [2, 3, 5, 17, 1451, 1380653] ⟨1021697026531, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (1451, 1), (1380653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1451
    · exact prime_1380653
  · decide +kernel

theorem prime_1021697055419 : Nat.Prime 1021697055419 := by
  apply nodeValid_prime [2, 13, 39296040593] ⟨1021697055419, 2, [(2, 1), (13, 1), (39296040593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_39296040593
  · decide +kernel

theorem prime_1023020008391 : Nat.Prime 1023020008391 := by
  apply nodeValid_prime [2, 5, 42409, 2412271] ⟨1023020008391, 17, [(2, 1), (5, 1), (42409, 1), (2412271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_42409
    · exact prime_2412271
  · decide +kernel

theorem prime_1023020010829 : Nat.Prime 1023020010829 := by
  apply nodeValid_prime [2, 3, 28417222523] ⟨1023020010829, 6, [(2, 2), (3, 2), (28417222523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28417222523
  · decide +kernel

theorem prime_1023020011693 : Nat.Prime 1023020011693 := by
  apply nodeValid_prime [2, 3, 7, 491, 8268031] ⟨1023020011693, 2, [(2, 2), (3, 2), (7, 1), (491, 1), (8268031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_491
    · exact prime_8268031
  · decide +kernel

theorem prime_1024344118157 : Nat.Prime 1024344118157 := by
  apply nodeValid_prime [2, 19, 13478212081] ⟨1024344118157, 2, [(2, 2), (19, 1), (13478212081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_13478212081
  · decide +kernel

theorem prime_1024344119033 : Nat.Prime 1024344119033 := by
  apply nodeValid_prime [2, 13, 9849462683] ⟨1024344119033, 3, [(2, 3), (13, 1), (9849462683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_9849462683
  · decide +kernel

theorem prime_1024344125863 : Nat.Prime 1024344125863 := by
  apply nodeValid_prime [2, 3, 170724020977] ⟨1024344125863, 13, [(2, 1), (3, 1), (170724020977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_170724020977
  · decide +kernel

theorem prime_1025669403817 : Nat.Prime 1025669403817 := by
  apply nodeValid_prime [2, 3, 42736225159] ⟨1025669403817, 10, [(2, 3), (3, 1), (42736225159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42736225159
  · decide +kernel

theorem prime_1025669409199 : Nat.Prime 1025669409199 := by
  apply nodeValid_prime [2, 3, 7, 29, 4637, 181603] ⟨1025669409199, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (4637, 1), (181603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_4637
    · exact prime_181603
  · decide +kernel

theorem prime_1025669409311 : Nat.Prime 1025669409311 := by
  apply nodeValid_prime [2, 5, 7, 13, 19, 59321539] ⟨1025669409311, 7, [(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (59321539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_59321539
  · decide +kernel

theorem prime_1026995819029 : Nat.Prime 1026995819029 := by
  apply nodeValid_prime [2, 3, 29, 31, 3282689] ⟨1026995819029, 2, [(2, 2), (3, 1), (29, 2), (31, 1), (3282689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
    · exact prime_3282689
  · decide +kernel

theorem prime_1026995842967 : Nat.Prime 1026995842967 := by
  apply nodeValid_prime [2, 13063, 39309341] ⟨1026995842967, 5, [(2, 1), (13063, 1), (39309341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13063
    · exact prime_39309341
  · decide +kernel

theorem prime_1028323416811 : Nat.Prime 1028323416811 := by
  apply nodeValid_prime [2, 3, 5, 34277447227] ⟨1028323416811, 2, [(2, 1), (3, 1), (5, 1), (34277447227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_34277447227
  · decide +kernel

theorem prime_1028323419517 : Nat.Prime 1028323419517 := by
  apply nodeValid_prime [2, 3, 23, 53997239] ⟨1028323419517, 2, [(2, 2), (3, 2), (23, 2), (53997239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53997239
  · decide +kernel

theorem prime_1028323444121 : Nat.Prime 1028323444121 := by
  apply nodeValid_prime [2, 5, 7, 17, 197, 1096621] ⟨1028323444121, 3, [(2, 3), (5, 1), (7, 1), (17, 1), (197, 1), (1096621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_197
    · exact prime_1096621
  · decide +kernel

theorem prime_1029652201471 : Nat.Prime 1029652201471 := by
  apply nodeValid_prime [2, 3, 5, 19, 449, 4023179] ⟨1029652201471, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (449, 1), (4023179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_449
    · exact prime_4023179
  · decide +kernel

theorem prime_1029652242253 : Nat.Prime 1029652242253 := by
  apply nodeValid_prime [2, 3, 17, 47, 107389679] ⟨1029652242253, 5, [(2, 2), (3, 1), (17, 1), (47, 1), (107389679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_47
    · exact prime_107389679
  · decide +kernel

theorem prime_1029652243339 : Nat.Prime 1029652243339 := by
  apply nodeValid_prime [2, 3, 262387, 654029] ⟨1029652243339, 10, [(2, 1), (3, 1), (262387, 1), (654029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_262387
    · exact prime_654029
  · decide +kernel

theorem prime_1030982110343 : Nat.Prime 1030982110343 := by
  apply nodeValid_prime [2, 6143, 83915197] ⟨1030982110343, 5, [(2, 1), (6143, 1), (83915197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6143
    · exact prime_83915197
  · decide +kernel

theorem prime_1030982111287 : Nat.Prime 1030982111287 := by
  apply nodeValid_prime [2, 3, 171830351881] ⟨1030982111287, 5, [(2, 1), (3, 1), (171830351881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_171830351881
  · decide +kernel

theorem prime_1030982121097 : Nat.Prime 1030982121097 := by
  apply nodeValid_prime [2, 3, 29, 1481296151] ⟨1030982121097, 5, [(2, 3), (3, 1), (29, 1), (1481296151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1481296151
  · decide +kernel

theorem prime_1032313207567 : Nat.Prime 1032313207567 := by
  apply nodeValid_prime [2, 3, 307, 560430623] ⟨1032313207567, 5, [(2, 1), (3, 1), (307, 1), (560430623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_560430623
  · decide +kernel

theorem prime_1032313302649 : Nat.Prime 1032313302649 := by
  apply nodeValid_prime [2, 3, 2539, 1882327] ⟨1032313302649, 11, [(2, 3), (3, 3), (2539, 1), (1882327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2539
    · exact prime_1882327
  · decide +kernel

theorem prime_1032313302883 : Nat.Prime 1032313302883 := by
  apply nodeValid_prime [2, 3, 57350739049] ⟨1032313302883, 2, [(2, 1), (3, 2), (57350739049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_57350739049
  · decide +kernel

theorem prime_1033645383839 : Nat.Prime 1033645383839 := by
  apply nodeValid_prime [2, 73, 7079762903] ⟨1033645383839, 17, [(2, 1), (73, 1), (7079762903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_7079762903
  · decide +kernel

theorem prime_1033645384001 : Nat.Prime 1033645384001 := by
  apply nodeValid_prime [2, 5, 5801, 22273] ⟨1033645384001, 3, [(2, 6), (5, 3), (5801, 1), (22273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5801
    · exact prime_22273
  · decide +kernel

theorem prime_1033645460677 : Nat.Prime 1033645460677 := by
  apply nodeValid_prime [2, 3, 86137121723] ⟨1033645460677, 2, [(2, 2), (3, 1), (86137121723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_86137121723
  · decide +kernel

theorem prime_1034978823283 : Nat.Prime 1034978823283 := by
  apply nodeValid_prime [2, 3, 101, 1291, 1322917] ⟨1034978823283, 2, [(2, 1), (3, 1), (101, 1), (1291, 1), (1322917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1291
    · exact prime_1322917
  · decide +kernel

theorem prime_1034978824601 : Nat.Prime 1034978824601 := by
  apply nodeValid_prime [2, 5, 7, 739270589] ⟨1034978824601, 3, [(2, 3), (5, 2), (7, 1), (739270589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_739270589
  · decide +kernel

theorem prime_1034978882099 : Nat.Prime 1034978882099 := by
  apply nodeValid_prime [2, 7, 19, 859, 647081] ⟨1034978882099, 2, [(2, 1), (7, 2), (19, 1), (859, 1), (647081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_859
    · exact prime_647081
  · decide +kernel

theorem prime_1036313459443 : Nat.Prime 1036313459443 := by
  apply nodeValid_prime [2, 3, 57572969969] ⟨1036313459443, 5, [(2, 1), (3, 2), (57572969969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_57572969969
  · decide +kernel

theorem prime_1036313575651 : Nat.Prime 1036313575651 := by
  apply nodeValid_prime [2, 3, 5, 139, 16567763] ⟨1036313575651, 7, [(2, 1), (3, 2), (5, 2), (139, 1), (16567763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_16567763
  · decide +kernel

theorem prime_1036313576047 : Nat.Prime 1036313576047 := by
  apply nodeValid_prime [2, 3, 7, 23, 43, 4889] ⟨1036313576047, 5, [(2, 1), (3, 7), (7, 2), (23, 1), (43, 1), (4889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_43
    · exact prime_4889
  · decide +kernel

theorem prime_1037649198841 : Nat.Prime 1037649198841 := by
  apply nodeValid_prime [2, 3, 5, 8647076657] ⟨1037649198841, 7, [(2, 3), (3, 1), (5, 1), (8647076657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8647076657
  · decide +kernel

theorem prime_1037649255257 : Nat.Prime 1037649255257 := by
  apply nodeValid_prime [2, 281, 461587747] ⟨1037649255257, 3, [(2, 3), (281, 1), (461587747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_461587747
  · decide +kernel

theorem prime_1037649256529 : Nat.Prime 1037649256529 := by
  apply nodeValid_prime [2, 199, 491, 663737] ⟨1037649256529, 3, [(2, 4), (199, 1), (491, 1), (663737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_491
    · exact prime_663737
  · decide +kernel

theorem prime_1038986085283 : Nat.Prime 1038986085283 := by
  apply nodeValid_prime [2, 3, 17, 139, 571, 128339] ⟨1038986085283, 3, [(2, 1), (3, 1), (17, 1), (139, 1), (571, 1), (128339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_139
    · exact prime_571
    · exact prime_128339
  · decide +kernel

theorem prime_1038986086297 : Nat.Prime 1038986086297 := by
  apply nodeValid_prime [2, 3, 29, 41, 36409661] ⟨1038986086297, 7, [(2, 3), (3, 1), (29, 1), (41, 1), (36409661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_41
    · exact prime_36409661
  · decide +kernel

theorem prime_1038986102177 : Nat.Prime 1038986102177 := by
  apply nodeValid_prime [2, 11, 271, 751, 14503] ⟨1038986102177, 3, [(2, 5), (11, 1), (271, 1), (751, 1), (14503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_271
    · exact prime_751
    · exact prime_14503
  · decide +kernel

theorem prime_1040324173409 : Nat.Prime 1040324173409 := by
  apply nodeValid_prime [2, 13, 2500779263] ⟨1040324173409, 3, [(2, 5), (13, 1), (2500779263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2500779263
  · decide +kernel

theorem prime_1040324179837 : Nat.Prime 1040324179837 := by
  apply nodeValid_prime [2, 3, 86693681653] ⟨1040324179837, 2, [(2, 2), (3, 1), (86693681653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_86693681653
  · decide +kernel

theorem prime_1040324179889 : Nat.Prime 1040324179889 := by
  apply nodeValid_prime [2, 7, 1326944107] ⟨1040324179889, 3, [(2, 4), (7, 2), (1326944107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1326944107
  · decide +kernel

theorem prime_1041663403021 : Nat.Prime 1041663403021 := by
  apply nodeValid_prime [2, 3, 5, 89, 173, 1127561] ⟨1041663403021, 7, [(2, 2), (3, 1), (5, 1), (89, 1), (173, 1), (1127561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_173
    · exact prime_1127561
  · decide +kernel

theorem prime_1041663403181 : Nat.Prime 1041663403181 := by
  apply nodeValid_prime [2, 5, 211, 1823, 135403] ⟨1041663403181, 2, [(2, 2), (5, 1), (211, 1), (1823, 1), (135403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
    · exact prime_1823
    · exact prime_135403
  · decide +kernel

theorem prime_1041663405241 : Nat.Prime 1041663405241 := by
  apply nodeValid_prime [2, 3, 5, 137, 260747] ⟨1041663405241, 11, [(2, 3), (3, 6), (5, 1), (137, 1), (260747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_260747
  · decide +kernel

theorem prime_1043003764861 : Nat.Prime 1043003764861 := by
  apply nodeValid_prime [2, 3, 5, 83, 209438507] ⟨1043003764861, 2, [(2, 2), (3, 1), (5, 1), (83, 1), (209438507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_209438507
  · decide +kernel

theorem prime_1043003765351 : Nat.Prime 1043003765351 := by
  apply nodeValid_prime [2, 5, 10559, 1975573] ⟨1043003765351, 11, [(2, 1), (5, 2), (10559, 1), (1975573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10559
    · exact prime_1975573
  · decide +kernel

theorem prime_1043003802319 : Nat.Prime 1043003802319 := by
  apply nodeValid_prime [2, 3, 277789, 625777] ⟨1043003802319, 3, [(2, 1), (3, 1), (277789, 1), (625777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277789
    · exact prime_625777
  · decide +kernel

theorem prime_1044345319579 : Nat.Prime 1044345319579 := by
  apply nodeValid_prime [2, 3, 11, 5274471311] ⟨1044345319579, 10, [(2, 1), (3, 2), (11, 1), (5274471311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5274471311
  · decide +kernel

theorem prime_1044345319951 : Nat.Prime 1044345319951 := by
  apply nodeValid_prime [2, 3, 5, 173, 40244521] ⟨1044345319951, 6, [(2, 1), (3, 1), (5, 2), (173, 1), (40244521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_40244521
  · decide +kernel

theorem prime_1044345360857 : Nat.Prime 1044345360857 := by
  apply nodeValid_prime [2, 7, 457, 40807493] ⟨1044345360857, 5, [(2, 3), (7, 1), (457, 1), (40807493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_457
    · exact prime_40807493
  · decide +kernel

end Sude.Lucas.Generated
