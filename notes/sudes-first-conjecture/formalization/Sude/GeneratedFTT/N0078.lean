import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0076

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2371 : Nat.Prime 2371 := by
  apply nodeValid_prime [2, 3, 5, 79] ⟨2371, 2, [(2, 1), (3, 1), (5, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_5737 : Nat.Prime 5737 := by
  apply nodeValid_prime [2, 3, 239] ⟨5737, 5, [(2, 3), (3, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
  · decide +kernel

theorem prime_7369 : Nat.Prime 7369 := by
  apply nodeValid_prime [2, 3, 307] ⟨7369, 7, [(2, 3), (3, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
  · decide +kernel

theorem prime_7937 : Nat.Prime 7937 := by
  apply nodeValid_prime [2, 31] ⟨7937, 3, [(2, 8), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31
  · decide +kernel

theorem prime_14519 : Nat.Prime 14519 := by
  apply nodeValid_prime [2, 7, 17, 61] ⟨14519, 13, [(2, 1), (7, 1), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_15107 : Nat.Prime 15107 := by
  apply nodeValid_prime [2, 7, 13, 83] ⟨15107, 2, [(2, 1), (7, 1), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_15901 : Nat.Prime 15901 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨15901, 10, [(2, 2), (3, 1), (5, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_17989 : Nat.Prime 17989 := by
  apply nodeValid_prime [2, 3, 1499] ⟨17989, 2, [(2, 2), (3, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1499
  · decide +kernel

theorem prime_20341 : Nat.Prime 20341 := by
  apply nodeValid_prime [2, 3, 5, 113] ⟨20341, 2, [(2, 2), (3, 2), (5, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_22271 : Nat.Prime 22271 := by
  apply nodeValid_prime [2, 5, 17, 131] ⟨22271, 7, [(2, 1), (5, 1), (17, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_131
  · decide +kernel

theorem prime_26717 : Nat.Prime 26717 := by
  apply nodeValid_prime [2, 6679] ⟨26717, 2, [(2, 2), (6679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6679
  · decide +kernel

theorem prime_33071 : Nat.Prime 33071 := by
  apply nodeValid_prime [2, 5, 3307] ⟨33071, 11, [(2, 1), (5, 1), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3307
  · decide +kernel

theorem prime_34039 : Nat.Prime 34039 := by
  apply nodeValid_prime [2, 3, 31, 61] ⟨34039, 3, [(2, 1), (3, 2), (31, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_61
  · decide +kernel

theorem prime_39953 : Nat.Prime 39953 := by
  apply nodeValid_prime [2, 11, 227] ⟨39953, 3, [(2, 4), (11, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_227
  · decide +kernel

theorem prime_47623 : Nat.Prime 47623 := by
  apply nodeValid_prime [2, 3, 7937] ⟨47623, 3, [(2, 1), (3, 1), (7937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7937
  · decide +kernel

theorem prime_49927 : Nat.Prime 49927 := by
  apply nodeValid_prime [2, 3, 53, 157] ⟨49927, 3, [(2, 1), (3, 1), (53, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_157
  · decide +kernel

theorem prime_50051 : Nat.Prime 50051 := by
  apply nodeValid_prime [2, 5, 7, 11, 13] ⟨50051, 2, [(2, 1), (5, 2), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_58439 : Nat.Prime 58439 := by
  apply nodeValid_prime [2, 61, 479] ⟨58439, 17, [(2, 1), (61, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_479
  · decide +kernel

theorem prime_62723 : Nat.Prime 62723 := by
  apply nodeValid_prime [2, 11, 2851] ⟨62723, 2, [(2, 1), (11, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2851
  · decide +kernel

theorem prime_71983 : Nat.Prime 71983 := by
  apply nodeValid_prime [2, 3, 31, 43] ⟨71983, 3, [(2, 1), (3, 3), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_75571 : Nat.Prime 75571 := by
  apply nodeValid_prime [2, 3, 5, 11, 229] ⟨75571, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_229
  · decide +kernel

theorem prime_77243 : Nat.Prime 77243 := by
  apply nodeValid_prime [2, 11, 3511] ⟨77243, 2, [(2, 1), (11, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3511
  · decide +kernel

theorem prime_80831 : Nat.Prime 80831 := by
  apply nodeValid_prime [2, 5, 59, 137] ⟨80831, 7, [(2, 1), (5, 1), (59, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_137
  · decide +kernel

theorem prime_81689 : Nat.Prime 81689 := by
  apply nodeValid_prime [2, 10211] ⟨81689, 3, [(2, 3), (10211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10211
  · decide +kernel

theorem prime_85931 : Nat.Prime 85931 := by
  apply nodeValid_prime [2, 5, 13, 661] ⟨85931, 2, [(2, 1), (5, 1), (13, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_661
  · decide +kernel

theorem prime_87679 : Nat.Prime 87679 := by
  apply nodeValid_prime [2, 3, 4871] ⟨87679, 3, [(2, 1), (3, 2), (4871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4871
  · decide +kernel

theorem prime_89413 : Nat.Prime 89413 := by
  apply nodeValid_prime [2, 3, 7451] ⟨89413, 2, [(2, 2), (3, 1), (7451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7451
  · decide +kernel

theorem prime_99643 : Nat.Prime 99643 := by
  apply nodeValid_prime [2, 3, 16607] ⟨99643, 3, [(2, 1), (3, 1), (16607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16607
  · decide +kernel

theorem prime_103619 : Nat.Prime 103619 := by
  apply nodeValid_prime [2, 103, 503] ⟨103619, 2, [(2, 1), (103, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_503
  · decide +kernel

theorem prime_118037 : Nat.Prime 118037 := by
  apply nodeValid_prime [2, 23, 1283] ⟨118037, 2, [(2, 2), (23, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1283
  · decide +kernel

theorem prime_134507 : Nat.Prime 134507 := by
  apply nodeValid_prime [2, 109, 617] ⟨134507, 2, [(2, 1), (109, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_617
  · decide +kernel

theorem prime_148829 : Nat.Prime 148829 := by
  apply nodeValid_prime [2, 29, 1283] ⟨148829, 2, [(2, 2), (29, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1283
  · decide +kernel

theorem prime_160753 : Nat.Prime 160753 := by
  apply nodeValid_prime [2, 3, 17, 197] ⟨160753, 5, [(2, 4), (3, 1), (17, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_197
  · decide +kernel

theorem prime_162119 : Nat.Prime 162119 := by
  apply nodeValid_prime [2, 11, 7369] ⟨162119, 11, [(2, 1), (11, 1), (7369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_7369
  · decide +kernel

theorem prime_193601 : Nat.Prime 193601 := by
  apply nodeValid_prime [2, 5, 11] ⟨193601, 6, [(2, 6), (5, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_193763 : Nat.Prime 193763 := by
  apply nodeValid_prime [2, 19, 5099] ⟨193763, 2, [(2, 1), (19, 1), (5099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5099
  · decide +kernel

theorem prime_193859 : Nat.Prime 193859 := by
  apply nodeValid_prime [2, 7, 61, 227] ⟨193859, 2, [(2, 1), (7, 1), (61, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_227
  · decide +kernel

theorem prime_228593 : Nat.Prime 228593 := by
  apply nodeValid_prime [2, 7, 13, 157] ⟨228593, 3, [(2, 4), (7, 1), (13, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_157
  · decide +kernel

theorem prime_240811 : Nat.Prime 240811 := by
  apply nodeValid_prime [2, 3, 5, 23, 349] ⟨240811, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_349
  · decide +kernel

theorem prime_297659 : Nat.Prime 297659 := by
  apply nodeValid_prime [2, 148829] ⟨297659, 2, [(2, 1), (148829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_148829
  · decide +kernel

theorem prime_347533 : Nat.Prime 347533 := by
  apply nodeValid_prime [2, 3, 28961] ⟨347533, 2, [(2, 2), (3, 1), (28961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28961
  · decide +kernel

theorem prime_395069 : Nat.Prime 395069 := by
  apply nodeValid_prime [2, 283, 349] ⟨395069, 2, [(2, 2), (283, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_349
  · decide +kernel

theorem prime_450881 : Nat.Prime 450881 := by
  apply nodeValid_prime [2, 5, 1409] ⟨450881, 6, [(2, 6), (5, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1409
  · decide +kernel

theorem prime_476137 : Nat.Prime 476137 := by
  apply nodeValid_prime [2, 3, 17, 389] ⟨476137, 11, [(2, 3), (3, 2), (17, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_389
  · decide +kernel

theorem prime_496289 : Nat.Prime 496289 := by
  apply nodeValid_prime [2, 13, 1193] ⟨496289, 3, [(2, 5), (13, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1193
  · decide +kernel

theorem prime_504523 : Nat.Prime 504523 := by
  apply nodeValid_prime [2, 3, 9343] ⟨504523, 2, [(2, 1), (3, 3), (9343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9343
  · decide +kernel

theorem prime_520291 : Nat.Prime 520291 := by
  apply nodeValid_prime [2, 3, 5, 41, 47] ⟨520291, 3, [(2, 1), (3, 3), (5, 1), (41, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_47
  · decide +kernel

theorem prime_521743 : Nat.Prime 521743 := by
  apply nodeValid_prime [2, 3, 13, 6689] ⟨521743, 3, [(2, 1), (3, 1), (13, 1), (6689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6689
  · decide +kernel

theorem prime_523771 : Nat.Prime 523771 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 79] ⟨523771, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_567467 : Nat.Prime 567467 := by
  apply nodeValid_prime [2, 167, 1699] ⟨567467, 2, [(2, 1), (167, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_1699
  · decide +kernel

theorem prime_697973 : Nat.Prime 697973 := by
  apply nodeValid_prime [2, 11, 29, 547] ⟨697973, 2, [(2, 2), (11, 1), (29, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_547
  · decide +kernel

theorem prime_755351 : Nat.Prime 755351 := by
  apply nodeValid_prime [2, 5, 15107] ⟨755351, 7, [(2, 1), (5, 2), (15107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15107
  · decide +kernel

theorem prime_825059 : Nat.Prime 825059 := by
  apply nodeValid_prime [2, 13, 2441] ⟨825059, 2, [(2, 1), (13, 2), (2441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2441
  · decide +kernel

theorem prime_904789 : Nat.Prime 904789 := by
  apply nodeValid_prime [2, 3, 41, 613] ⟨904789, 2, [(2, 2), (3, 2), (41, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_613
  · decide +kernel

theorem prime_1070233 : Nat.Prime 1070233 := by
  apply nodeValid_prime [2, 3, 19, 2347] ⟨1070233, 5, [(2, 3), (3, 1), (19, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2347
  · decide +kernel

theorem prime_1070423 : Nat.Prime 1070423 := by
  apply nodeValid_prime [2, 17, 19, 1657] ⟨1070423, 5, [(2, 1), (17, 1), (19, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_1657
  · decide +kernel

theorem prime_1125679 : Nat.Prime 1125679 := by
  apply nodeValid_prime [2, 3, 163, 1151] ⟨1125679, 3, [(2, 1), (3, 1), (163, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_1151
  · decide +kernel

theorem prime_1598381 : Nat.Prime 1598381 := by
  apply nodeValid_prime [2, 5, 7, 233] ⟨1598381, 2, [(2, 2), (5, 1), (7, 3), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_233
  · decide +kernel

theorem prime_1619257 : Nat.Prime 1619257 := by
  apply nodeValid_prime [2, 3, 19, 53, 67] ⟨1619257, 5, [(2, 3), (3, 1), (19, 1), (53, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
    · exact prime_67
  · decide +kernel

theorem prime_1683469 : Nat.Prime 1683469 := by
  apply nodeValid_prime [2, 3, 101, 463] ⟨1683469, 10, [(2, 2), (3, 2), (101, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_463
  · decide +kernel

theorem prime_1904549 : Nat.Prime 1904549 := by
  apply nodeValid_prime [2, 476137] ⟨1904549, 2, [(2, 2), (476137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_476137
  · decide +kernel

theorem prime_2234207 : Nat.Prime 2234207 := by
  apply nodeValid_prime [2, 13, 85931] ⟨2234207, 5, [(2, 1), (13, 1), (85931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_85931
  · decide +kernel

theorem prime_2947897 : Nat.Prime 2947897 := by
  apply nodeValid_prime [2, 3, 7, 5849] ⟨2947897, 15, [(2, 3), (3, 2), (7, 1), (5849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5849
  · decide +kernel

theorem prime_3142627 : Nat.Prime 3142627 := by
  apply nodeValid_prime [2, 3, 523771] ⟨3142627, 2, [(2, 1), (3, 1), (523771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523771
  · decide +kernel

theorem prime_4246993 : Nat.Prime 4246993 := by
  apply nodeValid_prime [2, 3, 29, 113] ⟨4246993, 10, [(2, 4), (3, 4), (29, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_113
  · decide +kernel

theorem prime_4866263 : Nat.Prime 4866263 := by
  apply nodeValid_prime [2, 449, 5419] ⟨4866263, 5, [(2, 1), (449, 1), (5419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_449
    · exact prime_5419
  · decide +kernel

theorem prime_4929259 : Nat.Prime 4929259 := by
  apply nodeValid_prime [2, 3, 811, 1013] ⟨4929259, 10, [(2, 1), (3, 1), (811, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
    · exact prime_1013
  · decide +kernel

theorem prime_5026877 : Nat.Prime 5026877 := by
  apply nodeValid_prime [2, 67, 18757] ⟨5026877, 2, [(2, 2), (67, 1), (18757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_18757
  · decide +kernel

theorem prime_5035267 : Nat.Prime 5035267 := by
  apply nodeValid_prime [2, 3, 19, 14723] ⟨5035267, 5, [(2, 1), (3, 2), (19, 1), (14723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_14723
  · decide +kernel

theorem prime_5376421 : Nat.Prime 5376421 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 251] ⟨5376421, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (17, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_251
  · decide +kernel

theorem prime_8716007 : Nat.Prime 8716007 := by
  apply nodeValid_prime [2, 13, 107, 241] ⟨8716007, 5, [(2, 1), (13, 2), (107, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_107
    · exact prime_241
  · decide +kernel

theorem prime_9715543 : Nat.Prime 9715543 := by
  apply nodeValid_prime [2, 3, 1619257] ⟨9715543, 3, [(2, 1), (3, 1), (1619257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1619257
  · decide +kernel

theorem prime_15708247 : Nat.Prime 15708247 := by
  apply nodeValid_prime [2, 3, 47, 53, 1051] ⟨15708247, 5, [(2, 1), (3, 1), (47, 1), (53, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_53
    · exact prime_1051
  · decide +kernel

theorem prime_16073587 : Nat.Prime 16073587 := by
  apply nodeValid_prime [2, 3, 297659] ⟨16073587, 2, [(2, 1), (3, 3), (297659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_297659
  · decide +kernel

theorem prime_16142167 : Nat.Prime 16142167 := by
  apply nodeValid_prime [2, 3, 99643] ⟨16142167, 3, [(2, 1), (3, 4), (99643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_99643
  · decide +kernel

theorem prime_16932353 : Nat.Prime 16932353 := by
  apply nodeValid_prime [2, 33071] ⟨16932353, 3, [(2, 9), (33071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33071
  · decide +kernel

theorem prime_16987973 : Nat.Prime 16987973 := by
  apply nodeValid_prime [2, 4246993] ⟨16987973, 2, [(2, 2), (4246993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4246993
  · decide +kernel

theorem prime_19213889 : Nat.Prime 19213889 := by
  apply nodeValid_prime [2, 331, 907] ⟨19213889, 3, [(2, 6), (331, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_907
  · decide +kernel

theorem prime_19658999 : Nat.Prime 19658999 := by
  apply nodeValid_prime [2, 43, 228593] ⟨19658999, 17, [(2, 1), (43, 1), (228593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_228593
  · decide +kernel

theorem prime_19717037 : Nat.Prime 19717037 := by
  apply nodeValid_prime [2, 4929259] ⟨19717037, 2, [(2, 2), (4929259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4929259
  · decide +kernel

theorem prime_23032859 : Nat.Prime 23032859 := by
  apply nodeValid_prime [2, 17, 67, 10111] ⟨23032859, 2, [(2, 1), (17, 1), (67, 1), (10111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_67
    · exact prime_10111
  · decide +kernel

theorem prime_30832969 : Nat.Prime 30832969 := by
  apply nodeValid_prime [2, 3, 17, 75571] ⟨30832969, 13, [(2, 3), (3, 1), (17, 1), (75571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_75571
  · decide +kernel

theorem prime_34281883 : Nat.Prime 34281883 := by
  apply nodeValid_prime [2, 3, 1904549] ⟨34281883, 5, [(2, 1), (3, 2), (1904549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1904549
  · decide +kernel

theorem prime_62104699 : Nat.Prime 62104699 := by
  apply nodeValid_prime [2, 3, 59, 101, 193] ⟨62104699, 2, [(2, 1), (3, 3), (59, 1), (101, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_101
    · exact prime_193
  · decide +kernel

theorem prime_63288557 : Nat.Prime 63288557 := by
  apply nodeValid_prime [2, 29, 103, 5297] ⟨63288557, 2, [(2, 2), (29, 1), (103, 1), (5297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_103
    · exact prime_5297
  · decide +kernel

theorem prime_68453513 : Nat.Prime 68453513 := by
  apply nodeValid_prime [2, 409, 20921] ⟨68453513, 3, [(2, 3), (409, 1), (20921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_20921
  · decide +kernel

theorem prime_77053199 : Nat.Prime 77053199 := by
  apply nodeValid_prime [2, 199, 193601] ⟨77053199, 11, [(2, 1), (199, 1), (193601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_193601
  · decide +kernel

theorem prime_82671661 : Nat.Prime 82671661 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 1051] ⟨82671661, 2, [(2, 2), (3, 2), (5, 1), (19, 1), (23, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_1051
  · decide +kernel

theorem prime_107724817 : Nat.Prime 107724817 := by
  apply nodeValid_prime [2, 3, 103, 269] ⟨107724817, 5, [(2, 4), (3, 5), (103, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_269
  · decide +kernel

theorem prime_126410197 : Nat.Prime 126410197 := by
  apply nodeValid_prime [2, 3, 11, 43, 22271] ⟨126410197, 6, [(2, 2), (3, 1), (11, 1), (43, 1), (22271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_22271
  · decide +kernel

theorem prime_160203773 : Nat.Prime 160203773 := by
  apply nodeValid_prime [2, 29, 47623] ⟨160203773, 2, [(2, 2), (29, 2), (47623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_47623
  · decide +kernel

theorem prime_170423137 : Nat.Prime 170423137 := by
  apply nodeValid_prime [2, 3, 13, 15173] ⟨170423137, 7, [(2, 5), (3, 3), (13, 1), (15173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_15173
  · decide +kernel

theorem prime_196863209 : Nat.Prime 196863209 := by
  apply nodeValid_prime [2, 127, 193763] ⟨196863209, 3, [(2, 3), (127, 1), (193763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_193763
  · decide +kernel

theorem prime_302902813 : Nat.Prime 302902813 := by
  apply nodeValid_prime [2, 3, 103, 81689] ⟨302902813, 5, [(2, 2), (3, 2), (103, 1), (81689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_81689
  · decide +kernel

theorem prime_320407547 : Nat.Prime 320407547 := by
  apply nodeValid_prime [2, 160203773] ⟨320407547, 2, [(2, 1), (160203773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160203773
  · decide +kernel

theorem prime_506308457 : Nat.Prime 506308457 := by
  apply nodeValid_prime [2, 63288557] ⟨506308457, 3, [(2, 3), (63288557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63288557
  · decide +kernel

theorem prime_543461707 : Nat.Prime 543461707 := by
  apply nodeValid_prime [2, 3, 97, 149, 2089] ⟨543461707, 2, [(2, 1), (3, 2), (97, 1), (149, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_149
    · exact prime_2089
  · decide +kernel

theorem prime_559307911 : Nat.Prime 559307911 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 71983] ⟨559307911, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (71983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_71983
  · decide +kernel

theorem prime_1141621513 : Nat.Prime 1141621513 := by
  apply nodeValid_prime [2, 3, 89, 103, 5189] ⟨1141621513, 5, [(2, 3), (3, 1), (89, 1), (103, 1), (5189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_103
    · exact prime_5189
  · decide +kernel

theorem prime_2976179797 : Nat.Prime 2976179797 := by
  apply nodeValid_prime [2, 3, 82671661] ⟨2976179797, 5, [(2, 2), (3, 2), (82671661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_82671661
  · decide +kernel

theorem prime_4623191941 : Nat.Prime 4623191941 := by
  apply nodeValid_prime [2, 3, 5, 77053199] ⟨4623191941, 14, [(2, 2), (3, 1), (5, 1), (77053199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_77053199
  · decide +kernel

theorem prime_7919686493 : Nat.Prime 7919686493 := by
  apply nodeValid_prime [2, 67, 523, 56503] ⟨7919686493, 2, [(2, 2), (67, 1), (523, 1), (56503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_523
    · exact prime_56503
  · decide +kernel

theorem prime_8636054429 : Nat.Prime 8636054429 := by
  apply nodeValid_prime [2, 193, 691, 16189] ⟨8636054429, 2, [(2, 2), (193, 1), (691, 1), (16189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_691
    · exact prime_16189
  · decide +kernel

theorem prime_9258179143 : Nat.Prime 9258179143 := by
  apply nodeValid_prime [2, 3, 491, 3142627] ⟨9258179143, 5, [(2, 1), (3, 1), (491, 1), (3142627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_491
    · exact prime_3142627
  · decide +kernel

theorem prime_9763898503 : Nat.Prime 9763898503 := by
  apply nodeValid_prime [2, 3, 3119, 521743] ⟨9763898503, 3, [(2, 1), (3, 1), (3119, 1), (521743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3119
    · exact prime_521743
  · decide +kernel

theorem prime_12806228573 : Nat.Prime 12806228573 := by
  apply nodeValid_prime [2, 2003, 1598381] ⟨12806228573, 2, [(2, 2), (2003, 1), (1598381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2003
    · exact prime_1598381
  · decide +kernel

theorem prime_13129682353 : Nat.Prime 13129682353 := by
  apply nodeValid_prime [2, 3, 17, 83, 193859] ⟨13129682353, 5, [(2, 4), (3, 1), (17, 1), (83, 1), (193859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_83
    · exact prime_193859
  · decide +kernel

theorem prime_13170980717 : Nat.Prime 13170980717 := by
  apply nodeValid_prime [2, 167, 19717037] ⟨13170980717, 2, [(2, 2), (167, 1), (19717037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_19717037
  · decide +kernel

theorem prime_24111023821 : Nat.Prime 24111023821 := by
  apply nodeValid_prime [2, 3, 5, 13, 89, 26717] ⟨24111023821, 2, [(2, 2), (3, 1), (5, 1), (13, 2), (89, 1), (26717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_89
    · exact prime_26717
  · decide +kernel

theorem prime_39222079781 : Nat.Prime 39222079781 := by
  apply nodeValid_prime [2, 5, 13, 31, 4866263] ⟨39222079781, 2, [(2, 2), (5, 1), (13, 1), (31, 1), (4866263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_4866263
  · decide +kernel

theorem prime_47317036951 : Nat.Prime 47317036951 := by
  apply nodeValid_prime [2, 3, 5, 1553, 7523] ⟨47317036951, 3, [(2, 1), (3, 4), (5, 2), (1553, 1), (7523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1553
    · exact prime_7523
  · decide +kernel

theorem prime_78778094119 : Nat.Prime 78778094119 := by
  apply nodeValid_prime [2, 3, 13129682353] ⟨78778094119, 3, [(2, 1), (3, 1), (13129682353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13129682353
  · decide +kernel

theorem prime_79112990227 : Nat.Prime 79112990227 := by
  apply nodeValid_prime [2, 3, 43, 61, 5026877] ⟨79112990227, 2, [(2, 1), (3, 1), (43, 1), (61, 1), (5026877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_61
    · exact prime_5026877
  · decide +kernel

theorem prime_87038917171 : Nat.Prime 87038917171 := by
  apply nodeValid_prime [2, 3, 5, 151, 19213889] ⟨87038917171, 3, [(2, 1), (3, 1), (5, 1), (151, 1), (19213889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_19213889
  · decide +kernel

theorem prime_104703405647 : Nat.Prime 104703405647 := by
  apply nodeValid_prime [2, 7, 43, 59, 2947897] ⟨104703405647, 5, [(2, 1), (7, 1), (43, 1), (59, 1), (2947897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_59
    · exact prime_2947897
  · decide +kernel

theorem prime_117166782037 : Nat.Prime 117166782037 := by
  apply nodeValid_prime [2, 3, 9763898503] ⟨117166782037, 2, [(2, 2), (3, 1), (9763898503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9763898503
  · decide +kernel

theorem prime_191283305641 : Nat.Prime 191283305641 := by
  apply nodeValid_prime [2, 3, 5, 7, 14321, 15901] ⟨191283305641, 23, [(2, 3), (3, 1), (5, 1), (7, 1), (14321, 1), (15901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_14321
    · exact prime_15901
  · decide +kernel

theorem prime_234583018997 : Nat.Prime 234583018997 := by
  apply nodeValid_prime [2, 19, 613, 5035267] ⟨234583018997, 2, [(2, 2), (19, 1), (613, 1), (5035267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_613
    · exact prime_5035267
  · decide +kernel

theorem prime_318468564607 : Nat.Prime 318468564607 := by
  apply nodeValid_prime [2, 3, 41, 769, 1683469] ⟨318468564607, 3, [(2, 1), (3, 1), (41, 1), (769, 1), (1683469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_769
    · exact prime_1683469
  · decide +kernel

theorem prime_474677941567 : Nat.Prime 474677941567 := by
  apply nodeValid_prime [2, 3, 4657, 16987973] ⟨474677941567, 3, [(2, 1), (3, 1), (4657, 1), (16987973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4657
    · exact prime_16987973
  · decide +kernel

theorem prime_937334226869 : Nat.Prime 937334226869 := by
  apply nodeValid_prime [2, 13, 29, 619, 77243] ⟨937334226869, 2, [(2, 2), (13, 2), (29, 1), (619, 1), (77243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_619
    · exact prime_77243
  · decide +kernel

theorem prime_945337129619 : Nat.Prime 945337129619 := by
  apply nodeValid_prime [2, 7, 196863209] ⟨945337129619, 2, [(2, 1), (7, 4), (196863209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_196863209
  · decide +kernel

theorem prime_957428052533 : Nat.Prime 957428052533 := by
  apply nodeValid_prime [2, 7, 60257, 567467] ⟨957428052533, 2, [(2, 2), (7, 1), (60257, 1), (567467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_60257
    · exact prime_567467
  · decide +kernel

theorem prime_1874668453739 : Nat.Prime 1874668453739 := by
  apply nodeValid_prime [2, 937334226869] ⟨1874668453739, 2, [(2, 1), (937334226869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_937334226869
  · decide +kernel

theorem prime_1874668512593 : Nat.Prime 1874668512593 := by
  apply nodeValid_prime [2, 117166782037] ⟨1874668512593, 3, [(2, 4), (117166782037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117166782037
  · decide +kernel

theorem prime_1874668512991 : Nat.Prime 1874668512991 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 1523, 450881] ⟨1874668512991, 14, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (1523, 1), (450881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_1523
    · exact prime_450881
  · decide +kernel

theorem prime_1876664151977 : Nat.Prime 1876664151977 := by
  apply nodeValid_prime [2, 234583018997] ⟨1876664151977, 3, [(2, 3), (234583018997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_234583018997
  · decide +kernel

theorem prime_1876664267831 : Nat.Prime 1876664267831 := by
  apply nodeValid_prime [2, 5, 11, 19, 839, 1070233] ⟨1876664267831, 11, [(2, 1), (5, 1), (11, 1), (19, 1), (839, 1), (1070233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_839
    · exact prime_1070233
  · decide +kernel

theorem prime_1876664269091 : Nat.Prime 1876664269091 := by
  apply nodeValid_prime [2, 5, 13, 919, 15708247] ⟨1876664269091, 2, [(2, 1), (5, 1), (13, 1), (919, 1), (15708247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_919
    · exact prime_15708247
  · decide +kernel

theorem prime_1878661284347 : Nat.Prime 1878661284347 := by
  apply nodeValid_prime [2, 7, 11, 2269, 5376421] ⟨1878661284347, 2, [(2, 1), (7, 1), (11, 1), (2269, 1), (5376421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_2269
    · exact prime_5376421
  · decide +kernel

theorem prime_1878661334909 : Nat.Prime 1878661334909 := by
  apply nodeValid_prime [2, 47, 103, 139, 697973] ⟨1878661334909, 2, [(2, 2), (47, 1), (103, 1), (139, 1), (697973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_103
    · exact prime_139
    · exact prime_697973
  · decide +kernel

theorem prime_1878661335169 : Nat.Prime 1878661335169 := by
  apply nodeValid_prime [2, 3, 17, 23, 727, 5737] ⟨1878661335169, 7, [(2, 7), (3, 2), (17, 1), (23, 1), (727, 1), (5737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_727
    · exact prime_5737
  · decide +kernel

theorem prime_1880659855187 : Nat.Prime 1880659855187 := by
  apply nodeValid_prime [2, 7, 29, 43, 107724817] ⟨1880659855187, 5, [(2, 1), (7, 1), (29, 1), (43, 1), (107724817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_43
    · exact prime_107724817
  · decide +kernel

theorem prime_1880659858039 : Nat.Prime 1880659858039 := by
  apply nodeValid_prime [2, 3, 13, 24111023821] ⟨1880659858039, 3, [(2, 1), (3, 1), (13, 1), (24111023821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_24111023821
  · decide +kernel

theorem prime_1880659858507 : Nat.Prime 1880659858507 := by
  apply nodeValid_prime [2, 3, 11, 13, 131, 2371, 7057] ⟨1880659858507, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (131, 1), (2371, 1), (7057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_131
    · exact prime_2371
    · exact prime_7057
  · decide +kernel

theorem prime_1882659828943 : Nat.Prime 1882659828943 := by
  apply nodeValid_prime [2, 3, 19, 239, 23032859] ⟨1882659828943, 5, [(2, 1), (3, 2), (19, 1), (239, 1), (23032859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_239
    · exact prime_23032859
  · decide +kernel

theorem prime_1882659829489 : Nat.Prime 1882659829489 := by
  apply nodeValid_prime [2, 3, 39222079781] ⟨1882659829489, 11, [(2, 4), (3, 1), (39222079781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39222079781
  · decide +kernel

theorem prime_1882659865523 : Nat.Prime 1882659865523 := by
  apply nodeValid_prime [2, 109, 8636054429] ⟨1882659865523, 2, [(2, 1), (109, 1), (8636054429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_8636054429
  · decide +kernel

theorem prime_1884661301647 : Nat.Prime 1884661301647 := by
  apply nodeValid_prime [2, 3, 104703405647] ⟨1884661301647, 5, [(2, 1), (3, 2), (104703405647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_104703405647
  · decide +kernel

theorem prime_1884661302487 : Nat.Prime 1884661302487 := by
  apply nodeValid_prime [2, 3, 17, 61, 302902813] ⟨1884661302487, 3, [(2, 1), (3, 1), (17, 1), (61, 1), (302902813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_302902813
  · decide +kernel

theorem prime_1884661311677 : Nat.Prime 1884661311677 := by
  apply nodeValid_prime [2, 11, 13, 2927, 1125679] ⟨1884661311677, 2, [(2, 2), (11, 1), (13, 1), (2927, 1), (1125679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_2927
    · exact prime_1125679
  · decide +kernel

theorem prime_1886664194627 : Nat.Prime 1886664194627 := by
  apply nodeValid_prime [2, 58439, 16142167] ⟨1886664194627, 2, [(2, 1), (58439, 1), (16142167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_58439
    · exact prime_16142167
  · decide +kernel

theorem prime_1886664213223 : Nat.Prime 1886664213223 := by
  apply nodeValid_prime [2, 3, 347533, 904789] ⟨1886664213223, 5, [(2, 1), (3, 1), (347533, 1), (904789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347533
    · exact prime_904789
  · decide +kernel

theorem prime_1886664213649 : Nat.Prime 1886664213649 := by
  apply nodeValid_prime [2, 3, 449, 1049, 27817] ⟨1886664213649, 7, [(2, 4), (3, 2), (449, 1), (1049, 1), (27817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
    · exact prime_1049
    · exact prime_27817
  · decide +kernel

theorem prime_1888668518327 : Nat.Prime 1888668518327 := by
  apply nodeValid_prime [2, 43, 1297, 16932353] ⟨1888668518327, 5, [(2, 1), (43, 1), (1297, 1), (16932353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1297
    · exact prime_16932353
  · decide +kernel

theorem prime_1888668543451 : Nat.Prime 1888668543451 := by
  apply nodeValid_prime [2, 3, 5, 13, 19, 3511, 14519] ⟨1888668543451, 2, [(2, 1), (3, 1), (5, 2), (13, 1), (19, 1), (3511, 1), (14519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_3511
    · exact prime_14519
  · decide +kernel

theorem prime_1888668545173 : Nat.Prime 1888668545173 := by
  apply nodeValid_prime [2, 3, 17, 9258179143] ⟨1888668545173, 2, [(2, 2), (3, 1), (17, 1), (9258179143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9258179143
  · decide +kernel

theorem prime_1890674258857 : Nat.Prime 1890674258857 := by
  apply nodeValid_prime [2, 3, 78778094119] ⟨1890674258857, 10, [(2, 3), (3, 1), (78778094119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_78778094119
  · decide +kernel

theorem prime_1890674259239 : Nat.Prime 1890674259239 := by
  apply nodeValid_prime [2, 945337129619] ⟨1890674259239, 17, [(2, 1), (945337129619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_945337129619
  · decide +kernel

theorem prime_1890674281879 : Nat.Prime 1890674281879 := by
  apply nodeValid_prime [2, 3, 43, 170423137] ⟨1890674281879, 6, [(2, 1), (3, 1), (43, 2), (170423137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_170423137
  · decide +kernel

theorem prime_1892681478041 : Nat.Prime 1892681478041 := by
  apply nodeValid_prime [2, 5, 47317036951] ⟨1892681478041, 3, [(2, 3), (5, 1), (47317036951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47317036951
  · decide +kernel

theorem prime_1892681478053 : Nat.Prime 1892681478053 := by
  apply nodeValid_prime [2, 53, 17989, 496289] ⟨1892681478053, 2, [(2, 2), (53, 1), (17989, 1), (496289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_17989
    · exact prime_496289
  · decide +kernel

theorem prime_1892681489999 : Nat.Prime 1892681489999 := by
  apply nodeValid_prime [2, 13, 17, 5669, 755351] ⟨1892681489999, 11, [(2, 1), (13, 1), (17, 1), (5669, 1), (755351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_5669
    · exact prime_755351
  · decide +kernel

theorem prime_1894690141213 : Nat.Prime 1894690141213 := by
  apply nodeValid_prime [2, 3, 11, 19, 47, 16073587] ⟨1894690141213, 5, [(2, 2), (3, 1), (11, 1), (19, 1), (47, 1), (16073587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_47
    · exact prime_16073587
  · decide +kernel

theorem prime_1894690157033 : Nat.Prime 1894690157033 := by
  apply nodeValid_prime [2, 307, 4799, 160753] ⟨1894690157033, 3, [(2, 3), (307, 1), (4799, 1), (160753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_4799
    · exact prime_160753
  · decide +kernel

theorem prime_1894690157093 : Nat.Prime 1894690157093 := by
  apply nodeValid_prime [2, 29, 263, 62104699] ⟨1894690157093, 2, [(2, 2), (29, 1), (263, 1), (62104699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_263
    · exact prime_62104699
  · decide +kernel

theorem prime_1896700223311 : Nat.Prime 1896700223311 := by
  apply nodeValid_prime [2, 3, 5, 593, 1319, 80831] ⟨1896700223311, 3, [(2, 1), (3, 1), (5, 1), (593, 1), (1319, 1), (80831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_593
    · exact prime_1319
    · exact prime_80831
  · decide +kernel

theorem prime_1896700223521 : Nat.Prime 1896700223521 := by
  apply nodeValid_prime [2, 3, 5, 67, 19658999] ⟨1896700223521, 19, [(2, 5), (3, 2), (5, 1), (67, 1), (19658999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_19658999
  · decide +kernel

theorem prime_1896700231949 : Nat.Prime 1896700231949 := by
  apply nodeValid_prime [2, 23, 47, 2027, 216401] ⟨1896700231949, 2, [(2, 2), (23, 1), (47, 1), (2027, 1), (216401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_2027
    · exact prime_216401
  · decide +kernel

theorem prime_1898711765449 : Nat.Prime 1898711765449 := by
  apply nodeValid_prime [2, 3, 79112990227] ⟨1898711765449, 13, [(2, 3), (3, 1), (79112990227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79112990227
  · decide +kernel

theorem prime_1898711766269 : Nat.Prime 1898711766269 := by
  apply nodeValid_prime [2, 474677941567] ⟨1898711766269, 2, [(2, 2), (474677941567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_474677941567
  · decide +kernel

theorem prime_1898711767741 : Nat.Prime 1898711767741 := by
  apply nodeValid_prime [2, 3, 5, 62723, 504523] ⟨1898711767741, 2, [(2, 2), (3, 1), (5, 1), (62723, 1), (504523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_62723
    · exact prime_504523
  · decide +kernel

theorem prime_1900724720897 : Nat.Prime 1900724720897 := by
  apply nodeValid_prime [2, 8999, 825059] ⟨1900724720897, 3, [(2, 8), (8999, 1), (825059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8999
    · exact prime_825059
  · decide +kernel

theorem prime_1900724721053 : Nat.Prime 1900724721053 := by
  apply nodeValid_prime [2, 83, 167, 34281883] ⟨1900724721053, 2, [(2, 2), (83, 1), (167, 1), (34281883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_167
    · exact prime_34281883
  · decide +kernel

theorem prime_1900724758321 : Nat.Prime 1900724758321 := by
  apply nodeValid_prime [2, 3, 5, 7919686493] ⟨1900724758321, 19, [(2, 4), (3, 1), (5, 1), (7919686493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7919686493
  · decide +kernel

theorem prime_1902739192129 : Nat.Prime 1902739192129 := by
  apply nodeValid_prime [2, 3, 379, 8716007] ⟨1902739192129, 11, [(2, 6), (3, 2), (379, 1), (8716007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_8716007
  · decide +kernel

theorem prime_1902739219181 : Nat.Prime 1902739219181 := by
  apply nodeValid_prime [2, 5, 240811, 395069] ⟨1902739219181, 2, [(2, 2), (5, 1), (240811, 1), (395069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_240811
    · exact prime_395069
  · decide +kernel

theorem prime_1902739219247 : Nat.Prime 1902739219247 := by
  apply nodeValid_prime [2, 19, 227, 2467, 89413] ⟨1902739219247, 5, [(2, 1), (19, 1), (227, 1), (2467, 1), (89413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_227
    · exact prime_2467
    · exact prime_89413
  · decide +kernel

theorem prime_1904755070081 : Nat.Prime 1904755070081 := by
  apply nodeValid_prime [2, 5, 2976179797] ⟨1904755070081, 6, [(2, 7), (5, 1), (2976179797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2976179797
  · decide +kernel

theorem prime_1904755079653 : Nat.Prime 1904755079653 := by
  apply nodeValid_prime [2, 3, 89, 20341, 87679] ⟨1904755079653, 5, [(2, 2), (3, 1), (89, 1), (20341, 1), (87679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_20341
    · exact prime_87679
  · decide +kernel

theorem prime_1904755079693 : Nat.Prime 1904755079693 := by
  apply nodeValid_prime [2, 103, 4623191941] ⟨1904755079693, 2, [(2, 2), (103, 1), (4623191941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_4623191941
  · decide +kernel

theorem prime_1906772397377 : Nat.Prime 1906772397377 := by
  apply nodeValid_prime [2, 7, 11, 23, 2897, 5807] ⟨1906772397377, 5, [(2, 6), (7, 1), (11, 1), (23, 1), (2897, 1), (5807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_2897
    · exact prime_5807
  · decide +kernel

theorem prime_1906772468899 : Nat.Prime 1906772468899 := by
  apply nodeValid_prime [2, 3, 11, 937, 30832969] ⟨1906772468899, 2, [(2, 1), (3, 1), (11, 1), (937, 1), (30832969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_937
    · exact prime_30832969
  · decide +kernel

theorem prime_1906772469181 : Nat.Prime 1906772469181 := by
  apply nodeValid_prime [2, 3, 5, 3271, 9715543] ⟨1906772469181, 2, [(2, 2), (3, 1), (5, 1), (3271, 1), (9715543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3271
    · exact prime_9715543
  · decide +kernel

theorem prime_1908791138677 : Nat.Prime 1908791138677 := by
  apply nodeValid_prime [2, 3, 181, 821, 1070423] ⟨1908791138677, 2, [(2, 2), (3, 1), (181, 1), (821, 1), (1070423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_821
    · exact prime_1070423
  · decide +kernel

theorem prime_1908791169737 : Nat.Prime 1908791169737 := by
  apply nodeValid_prime [2, 11, 19, 1141621513] ⟨1908791169737, 3, [(2, 3), (11, 1), (19, 1), (1141621513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1141621513
  · decide +kernel

theorem prime_1910811361813 : Nat.Prime 1910811361813 := by
  apply nodeValid_prime [2, 3, 293, 543461707] ⟨1910811361813, 2, [(2, 2), (3, 1), (293, 1), (543461707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_543461707
  · decide +kernel

theorem prime_1910811361883 : Nat.Prime 1910811361883 := by
  apply nodeValid_prime [2, 17, 821, 68453513] ⟨1910811361883, 2, [(2, 1), (17, 1), (821, 1), (68453513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_821
    · exact prime_68453513
  · decide +kernel

theorem prime_1910811387643 : Nat.Prime 1910811387643 := by
  apply nodeValid_prime [2, 3, 318468564607] ⟨1910811387643, 2, [(2, 1), (3, 1), (318468564607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_318468564607
  · decide +kernel

theorem prime_1912833055591 : Nat.Prime 1912833055591 := by
  apply nodeValid_prime [2, 3, 5, 199, 320407547] ⟨1912833055591, 3, [(2, 1), (3, 1), (5, 1), (199, 1), (320407547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_320407547
  · decide +kernel

theorem prime_1912833055621 : Nat.Prime 1912833055621 := by
  apply nodeValid_prime [2, 3, 5, 19, 559307911] ⟨1912833055621, 6, [(2, 2), (3, 2), (5, 1), (19, 1), (559307911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_559307911
  · decide +kernel

theorem prime_1912833056411 : Nat.Prime 1912833056411 := by
  apply nodeValid_prime [2, 5, 191283305641] ⟨1912833056411, 6, [(2, 1), (5, 1), (191283305641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191283305641
  · decide +kernel

theorem prime_1914856103597 : Nat.Prime 1914856103597 := by
  apply nodeValid_prime [2, 71, 12959, 520291] ⟨1914856103597, 2, [(2, 2), (71, 1), (12959, 1), (520291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_12959
    · exact prime_520291
  · decide +kernel

theorem prime_1914856105067 : Nat.Prime 1914856105067 := by
  apply nodeValid_prime [2, 957428052533] ⟨1914856105067, 2, [(2, 1), (957428052533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_957428052533
  · decide +kernel

theorem prime_1914856177763 : Nat.Prime 1914856177763 := by
  apply nodeValid_prime [2, 11, 87038917171] ⟨1914856177763, 2, [(2, 1), (11, 1), (87038917171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_87038917171
  · decide +kernel

theorem prime_1916880747421 : Nat.Prime 1916880747421 := by
  apply nodeValid_prime [2, 3, 5, 31, 8731, 118037] ⟨1916880747421, 10, [(2, 2), (3, 1), (5, 1), (31, 1), (8731, 1), (118037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_8731
    · exact prime_118037
  · decide +kernel

theorem prime_1916880762091 : Nat.Prime 1916880762091 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 7949, 49927] ⟨1916880762091, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (7949, 1), (49927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_7949
    · exact prime_49927
  · decide +kernel

theorem prime_1916880763321 : Nat.Prime 1916880763321 := by
  apply nodeValid_prime [2, 3, 5, 17, 179, 277, 6317] ⟨1916880763321, 11, [(2, 3), (3, 2), (5, 1), (17, 1), (179, 1), (277, 1), (6317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_179
    · exact prime_277
    · exact prime_6317
  · decide +kernel

theorem prime_1918906771333 : Nat.Prime 1918906771333 := by
  apply nodeValid_prime [2, 3, 19, 3767, 2234207] ⟨1918906771333, 2, [(2, 2), (3, 1), (19, 1), (3767, 1), (2234207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3767
    · exact prime_2234207
  · decide +kernel

theorem prime_1918906790461 : Nat.Prime 1918906790461 := by
  apply nodeValid_prime [2, 3, 5, 11, 23, 126410197] ⟨1918906790461, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (126410197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_126410197
  · decide +kernel

theorem prime_1918906790531 : Nat.Prime 1918906790531 := by
  apply nodeValid_prime [2, 5, 37, 50051, 103619] ⟨1918906790531, 2, [(2, 1), (5, 1), (37, 1), (50051, 1), (103619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_50051
    · exact prime_103619
  · decide +kernel

theorem prime_1920934247051 : Nat.Prime 1920934247051 := by
  apply nodeValid_prime [2, 5, 7, 13, 10567, 39953] ⟨1920934247051, 2, [(2, 1), (5, 2), (7, 1), (13, 1), (10567, 1), (39953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_10567
    · exact prime_39953
  · decide +kernel

theorem prime_1920934285859 : Nat.Prime 1920934285859 := by
  apply nodeValid_prime [2, 7, 271, 506308457] ⟨1920934285859, 2, [(2, 1), (7, 1), (271, 1), (506308457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_271
    · exact prime_506308457
  · decide +kernel

theorem prime_1920934285951 : Nat.Prime 1920934285951 := by
  apply nodeValid_prime [2, 3, 5, 12806228573] ⟨1920934285951, 3, [(2, 1), (3, 1), (5, 2), (12806228573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12806228573
  · decide +kernel

theorem prime_1922963170171 : Nat.Prime 1922963170171 := by
  apply nodeValid_prime [2, 3, 5, 7, 8069, 162119] ⟨1922963170171, 7, [(2, 1), (3, 1), (5, 1), (7, 2), (8069, 1), (162119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_8069
    · exact prime_162119
  · decide +kernel

theorem prime_1922963184661 : Nat.Prime 1922963184661 := by
  apply nodeValid_prime [2, 3, 5, 7, 34039, 134507] ⟨1922963184661, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (34039, 1), (134507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_34039
    · exact prime_134507
  · decide +kernel

theorem prime_1922963184683 : Nat.Prime 1922963184683 := by
  apply nodeValid_prime [2, 73, 13170980717] ⟨1922963184683, 2, [(2, 1), (73, 1), (13170980717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_13170980717
  · decide +kernel

end Sude.Lucas.Generated
