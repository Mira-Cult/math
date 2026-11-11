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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0139
import Sude.GeneratedTwinBase.M000

/-! Generated Lucas nodes for the FT base; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_19231 : Nat.Prime 19231 := by
  apply nodeValid_prime [2, 3, 5, 641] ⟨19231, 6, [(2, 1), (3, 1), (5, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_641
  · decide +kernel

theorem prime_19273 : Nat.Prime 19273 := by
  apply nodeValid_prime [2, 3, 11, 73] ⟨19273, 5, [(2, 3), (3, 1), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_19379 : Nat.Prime 19379 := by
  apply nodeValid_prime [2, 9689] ⟨19379, 2, [(2, 1), (9689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9689
  · decide +kernel

theorem prime_19391 : Nat.Prime 19391 := by
  apply nodeValid_prime [2, 5, 7, 277] ⟨19391, 11, [(2, 1), (5, 1), (7, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_19423 : Nat.Prime 19423 := by
  apply nodeValid_prime [2, 3, 13, 83] ⟨19423, 3, [(2, 1), (3, 2), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_19469 : Nat.Prime 19469 := by
  apply nodeValid_prime [2, 31, 157] ⟨19469, 2, [(2, 2), (31, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_157
  · decide +kernel

theorem prime_19477 : Nat.Prime 19477 := by
  apply nodeValid_prime [2, 3, 541] ⟨19477, 6, [(2, 2), (3, 2), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
  · decide +kernel

theorem prime_19531 : Nat.Prime 19531 := by
  apply nodeValid_prime [2, 3, 5, 7, 31] ⟨19531, 13, [(2, 1), (3, 2), (5, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_19543 : Nat.Prime 19543 := by
  apply nodeValid_prime [2, 3, 3257] ⟨19543, 3, [(2, 1), (3, 1), (3257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3257
  · decide +kernel

theorem prime_19577 : Nat.Prime 19577 := by
  apply nodeValid_prime [2, 2447] ⟨19577, 3, [(2, 3), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2447
  · decide +kernel

theorem prime_19687 : Nat.Prime 19687 := by
  apply nodeValid_prime [2, 3, 17, 193] ⟨19687, 5, [(2, 1), (3, 1), (17, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_193
  · decide +kernel

theorem prime_19697 : Nat.Prime 19697 := by
  apply nodeValid_prime [2, 1231] ⟨19697, 3, [(2, 4), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1231
  · decide +kernel

theorem prime_19709 : Nat.Prime 19709 := by
  apply nodeValid_prime [2, 13, 379] ⟨19709, 2, [(2, 2), (13, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_379
  · decide +kernel

theorem prime_19727 : Nat.Prime 19727 := by
  apply nodeValid_prime [2, 7, 1409] ⟨19727, 5, [(2, 1), (7, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1409
  · decide +kernel

theorem prime_19739 : Nat.Prime 19739 := by
  apply nodeValid_prime [2, 71, 139] ⟨19739, 2, [(2, 1), (71, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_139
  · decide +kernel

theorem prime_19759 : Nat.Prime 19759 := by
  apply nodeValid_prime [2, 3, 37, 89] ⟨19759, 3, [(2, 1), (3, 1), (37, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_89
  · decide +kernel

theorem prime_19777 : Nat.Prime 19777 := by
  apply nodeValid_prime [2, 3, 103] ⟨19777, 11, [(2, 6), (3, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_19793 : Nat.Prime 19793 := by
  apply nodeValid_prime [2, 1237] ⟨19793, 3, [(2, 4), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1237
  · decide +kernel

theorem prime_19813 : Nat.Prime 19813 := by
  apply nodeValid_prime [2, 3, 13, 127] ⟨19813, 2, [(2, 2), (3, 1), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_19853 : Nat.Prime 19853 := by
  apply nodeValid_prime [2, 7, 709] ⟨19853, 2, [(2, 2), (7, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_709
  · decide +kernel

theorem prime_19891 : Nat.Prime 19891 := by
  apply nodeValid_prime [2, 3, 5, 13, 17] ⟨19891, 2, [(2, 1), (3, 2), (5, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_19937 : Nat.Prime 19937 := by
  apply nodeValid_prime [2, 7, 89] ⟨19937, 3, [(2, 5), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_19963 : Nat.Prime 19963 := by
  apply nodeValid_prime [2, 3, 1109] ⟨19963, 2, [(2, 1), (3, 2), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1109
  · decide +kernel

theorem prime_19973 : Nat.Prime 19973 := by
  apply nodeValid_prime [2, 4993] ⟨19973, 2, [(2, 2), (4993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4993
  · decide +kernel

theorem prime_19993 : Nat.Prime 19993 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨19993, 10, [(2, 3), (3, 1), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_19997 : Nat.Prime 19997 := by
  apply nodeValid_prime [2, 4999] ⟨19997, 2, [(2, 2), (4999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4999
  · decide +kernel

theorem prime_20011 : Nat.Prime 20011 := by
  apply nodeValid_prime [2, 3, 5, 23, 29] ⟨20011, 12, [(2, 1), (3, 1), (5, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_20123 : Nat.Prime 20123 := by
  apply nodeValid_prime [2, 10061] ⟨20123, 2, [(2, 1), (10061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10061
  · decide +kernel

theorem prime_20173 : Nat.Prime 20173 := by
  apply nodeValid_prime [2, 3, 41] ⟨20173, 2, [(2, 2), (3, 1), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_20177 : Nat.Prime 20177 := by
  apply nodeValid_prime [2, 13, 97] ⟨20177, 3, [(2, 4), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_20231 : Nat.Prime 20231 := by
  apply nodeValid_prime [2, 5, 7, 17] ⟨20231, 29, [(2, 1), (5, 1), (7, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_20249 : Nat.Prime 20249 := by
  apply nodeValid_prime [2, 2531] ⟨20249, 3, [(2, 3), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2531
  · decide +kernel

theorem prime_20261 : Nat.Prime 20261 := by
  apply nodeValid_prime [2, 5, 1013] ⟨20261, 2, [(2, 2), (5, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1013
  · decide +kernel

theorem prime_20323 : Nat.Prime 20323 := by
  apply nodeValid_prime [2, 3, 1129] ⟨20323, 2, [(2, 1), (3, 2), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1129
  · decide +kernel

theorem prime_20327 : Nat.Prime 20327 := by
  apply nodeValid_prime [2, 10163] ⟨20327, 5, [(2, 1), (10163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10163
  · decide +kernel

theorem prime_20333 : Nat.Prime 20333 := by
  apply nodeValid_prime [2, 13, 17, 23] ⟨20333, 3, [(2, 2), (13, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_20431 : Nat.Prime 20431 := by
  apply nodeValid_prime [2, 3, 5, 227] ⟨20431, 3, [(2, 1), (3, 2), (5, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_227
  · decide +kernel

theorem prime_20441 : Nat.Prime 20441 := by
  apply nodeValid_prime [2, 5, 7, 73] ⟨20441, 3, [(2, 3), (5, 1), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_20443 : Nat.Prime 20443 := by
  apply nodeValid_prime [2, 3, 3407] ⟨20443, 2, [(2, 1), (3, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3407
  · decide +kernel

theorem prime_20507 : Nat.Prime 20507 := by
  apply nodeValid_prime [2, 10253] ⟨20507, 2, [(2, 1), (10253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10253
  · decide +kernel

theorem prime_20509 : Nat.Prime 20509 := by
  apply nodeValid_prime [2, 3, 1709] ⟨20509, 2, [(2, 2), (3, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1709
  · decide +kernel

theorem prime_20521 : Nat.Prime 20521 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨20521, 11, [(2, 3), (3, 3), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_20543 : Nat.Prime 20543 := by
  apply nodeValid_prime [2, 10271] ⟨20543, 5, [(2, 1), (10271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10271
  · decide +kernel

theorem prime_20611 : Nat.Prime 20611 := by
  apply nodeValid_prime [2, 3, 5, 229] ⟨20611, 2, [(2, 1), (3, 2), (5, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
  · decide +kernel

theorem prime_20717 : Nat.Prime 20717 := by
  apply nodeValid_prime [2, 5179] ⟨20717, 2, [(2, 2), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5179
  · decide +kernel

theorem prime_20743 : Nat.Prime 20743 := by
  apply nodeValid_prime [2, 3, 3457] ⟨20743, 5, [(2, 1), (3, 1), (3457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3457
  · decide +kernel

theorem prime_20749 : Nat.Prime 20749 := by
  apply nodeValid_prime [2, 3, 7, 13, 19] ⟨20749, 2, [(2, 2), (3, 1), (7, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_20759 : Nat.Prime 20759 := by
  apply nodeValid_prime [2, 97, 107] ⟨20759, 7, [(2, 1), (97, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_107
  · decide +kernel

theorem prime_20771 : Nat.Prime 20771 := by
  apply nodeValid_prime [2, 5, 31, 67] ⟨20771, 2, [(2, 1), (5, 1), (31, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_67
  · decide +kernel

theorem prime_20879 : Nat.Prime 20879 := by
  apply nodeValid_prime [2, 11, 13, 73] ⟨20879, 11, [(2, 1), (11, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_20947 : Nat.Prime 20947 := by
  apply nodeValid_prime [2, 3, 3491] ⟨20947, 3, [(2, 1), (3, 1), (3491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3491
  · decide +kernel

theorem prime_20959 : Nat.Prime 20959 := by
  apply nodeValid_prime [2, 3, 7, 499] ⟨20959, 7, [(2, 1), (3, 1), (7, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_499
  · decide +kernel

theorem prime_21013 : Nat.Prime 21013 := by
  apply nodeValid_prime [2, 3, 17, 103] ⟨21013, 2, [(2, 2), (3, 1), (17, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_103
  · decide +kernel

theorem prime_21017 : Nat.Prime 21017 := by
  apply nodeValid_prime [2, 37, 71] ⟨21017, 3, [(2, 3), (37, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_71
  · decide +kernel

theorem prime_21121 : Nat.Prime 21121 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨21121, 19, [(2, 7), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_21157 : Nat.Prime 21157 := by
  apply nodeValid_prime [2, 3, 41, 43] ⟨21157, 2, [(2, 2), (3, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_21191 : Nat.Prime 21191 := by
  apply nodeValid_prime [2, 5, 13, 163] ⟨21191, 7, [(2, 1), (5, 1), (13, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_163
  · decide +kernel

theorem prime_21313 : Nat.Prime 21313 := by
  apply nodeValid_prime [2, 3, 37] ⟨21313, 5, [(2, 6), (3, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_21397 : Nat.Prime 21397 := by
  apply nodeValid_prime [2, 3, 1783] ⟨21397, 2, [(2, 2), (3, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1783
  · decide +kernel

theorem prime_21467 : Nat.Prime 21467 := by
  apply nodeValid_prime [2, 10733] ⟨21467, 2, [(2, 1), (10733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10733
  · decide +kernel

theorem prime_21491 : Nat.Prime 21491 := by
  apply nodeValid_prime [2, 5, 7, 307] ⟨21491, 2, [(2, 1), (5, 1), (7, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_307
  · decide +kernel

theorem prime_21529 : Nat.Prime 21529 := by
  apply nodeValid_prime [2, 3, 13, 23] ⟨21529, 11, [(2, 3), (3, 2), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_21557 : Nat.Prime 21557 := by
  apply nodeValid_prime [2, 17, 317] ⟨21557, 2, [(2, 2), (17, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_317
  · decide +kernel

theorem prime_21569 : Nat.Prime 21569 := by
  apply nodeValid_prime [2, 337] ⟨21569, 3, [(2, 6), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_337
  · decide +kernel

theorem prime_21587 : Nat.Prime 21587 := by
  apply nodeValid_prime [2, 43, 251] ⟨21587, 2, [(2, 1), (43, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_251
  · decide +kernel

theorem prime_21599 : Nat.Prime 21599 := by
  apply nodeValid_prime [2, 10799] ⟨21599, 7, [(2, 1), (10799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10799
  · decide +kernel

theorem prime_21611 : Nat.Prime 21611 := by
  apply nodeValid_prime [2, 5, 2161] ⟨21611, 2, [(2, 1), (5, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2161
  · decide +kernel

theorem prime_21613 : Nat.Prime 21613 := by
  apply nodeValid_prime [2, 3, 1801] ⟨21613, 2, [(2, 2), (3, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1801
  · decide +kernel

theorem prime_21647 : Nat.Prime 21647 := by
  apply nodeValid_prime [2, 79, 137] ⟨21647, 5, [(2, 1), (79, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_137
  · decide +kernel

theorem prime_21661 : Nat.Prime 21661 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨21661, 2, [(2, 2), (3, 1), (5, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_21713 : Nat.Prime 21713 := by
  apply nodeValid_prime [2, 23, 59] ⟨21713, 3, [(2, 4), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_21727 : Nat.Prime 21727 := by
  apply nodeValid_prime [2, 3, 17, 71] ⟨21727, 3, [(2, 1), (3, 2), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_21739 : Nat.Prime 21739 := by
  apply nodeValid_prime [2, 3, 3623] ⟨21739, 2, [(2, 1), (3, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3623
  · decide +kernel

theorem prime_21757 : Nat.Prime 21757 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨21757, 5, [(2, 2), (3, 1), (7, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_21799 : Nat.Prime 21799 := by
  apply nodeValid_prime [2, 3, 7, 173] ⟨21799, 7, [(2, 1), (3, 2), (7, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173
  · decide +kernel

theorem prime_21841 : Nat.Prime 21841 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨21841, 11, [(2, 4), (3, 1), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_21851 : Nat.Prime 21851 := by
  apply nodeValid_prime [2, 5, 19, 23] ⟨21851, 6, [(2, 1), (5, 2), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_21859 : Nat.Prime 21859 := by
  apply nodeValid_prime [2, 3, 3643] ⟨21859, 2, [(2, 1), (3, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3643
  · decide +kernel

theorem prime_21863 : Nat.Prime 21863 := by
  apply nodeValid_prime [2, 17, 643] ⟨21863, 5, [(2, 1), (17, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_643
  · decide +kernel

theorem prime_21911 : Nat.Prime 21911 := by
  apply nodeValid_prime [2, 5, 7, 313] ⟨21911, 13, [(2, 1), (5, 1), (7, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_313
  · decide +kernel

theorem prime_21937 : Nat.Prime 21937 := by
  apply nodeValid_prime [2, 3, 457] ⟨21937, 7, [(2, 4), (3, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_457
  · decide +kernel

theorem prime_22027 : Nat.Prime 22027 := by
  apply nodeValid_prime [2, 3, 3671] ⟨22027, 3, [(2, 1), (3, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3671
  · decide +kernel

theorem prime_22039 : Nat.Prime 22039 := by
  apply nodeValid_prime [2, 3, 3673] ⟨22039, 6, [(2, 1), (3, 1), (3673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3673
  · decide +kernel

theorem prime_22189 : Nat.Prime 22189 := by
  apply nodeValid_prime [2, 3, 43] ⟨22189, 2, [(2, 2), (3, 1), (43, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_22229 : Nat.Prime 22229 := by
  apply nodeValid_prime [2, 5557] ⟨22229, 2, [(2, 2), (5557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5557
  · decide +kernel

theorem prime_22247 : Nat.Prime 22247 := by
  apply nodeValid_prime [2, 7, 227] ⟨22247, 5, [(2, 1), (7, 2), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
  · decide +kernel

theorem prime_22283 : Nat.Prime 22283 := by
  apply nodeValid_prime [2, 13, 857] ⟨22283, 2, [(2, 1), (13, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_857
  · decide +kernel

theorem prime_22291 : Nat.Prime 22291 := by
  apply nodeValid_prime [2, 3, 5, 743] ⟨22291, 3, [(2, 1), (3, 1), (5, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_743
  · decide +kernel

theorem prime_22303 : Nat.Prime 22303 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨22303, 6, [(2, 1), (3, 3), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_22349 : Nat.Prime 22349 := by
  apply nodeValid_prime [2, 37, 151] ⟨22349, 2, [(2, 2), (37, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_151
  · decide +kernel

theorem prime_22369 : Nat.Prime 22369 := by
  apply nodeValid_prime [2, 3, 233] ⟨22369, 11, [(2, 5), (3, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
  · decide +kernel

theorem prime_22381 : Nat.Prime 22381 := by
  apply nodeValid_prime [2, 3, 5, 373] ⟨22381, 10, [(2, 2), (3, 1), (5, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_373
  · decide +kernel

theorem prime_22433 : Nat.Prime 22433 := by
  apply nodeValid_prime [2, 701] ⟨22433, 3, [(2, 5), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_701
  · decide +kernel

theorem prime_22441 : Nat.Prime 22441 := by
  apply nodeValid_prime [2, 3, 5, 11, 17] ⟨22441, 14, [(2, 3), (3, 1), (5, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_22447 : Nat.Prime 22447 := by
  apply nodeValid_prime [2, 3, 29, 43] ⟨22447, 3, [(2, 1), (3, 2), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_22453 : Nat.Prime 22453 := by
  apply nodeValid_prime [2, 3, 1871] ⟨22453, 5, [(2, 2), (3, 1), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1871
  · decide +kernel

theorem prime_22481 : Nat.Prime 22481 := by
  apply nodeValid_prime [2, 5, 281] ⟨22481, 3, [(2, 4), (5, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_281
  · decide +kernel

theorem prime_22501 : Nat.Prime 22501 := by
  apply nodeValid_prime [2, 3, 5] ⟨22501, 2, [(2, 2), (3, 2), (5, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_22541 : Nat.Prime 22541 := by
  apply nodeValid_prime [2, 5, 7, 23] ⟨22541, 3, [(2, 2), (5, 1), (7, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_22543 : Nat.Prime 22543 := by
  apply nodeValid_prime [2, 3, 13, 17] ⟨22543, 3, [(2, 1), (3, 1), (13, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_22619 : Nat.Prime 22619 := by
  apply nodeValid_prime [2, 43, 263] ⟨22619, 2, [(2, 1), (43, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_263
  · decide +kernel

theorem prime_22637 : Nat.Prime 22637 := by
  apply nodeValid_prime [2, 5659] ⟨22637, 2, [(2, 2), (5659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5659
  · decide +kernel

theorem prime_22679 : Nat.Prime 22679 := by
  apply nodeValid_prime [2, 17, 23, 29] ⟨22679, 13, [(2, 1), (17, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_22699 : Nat.Prime 22699 := by
  apply nodeValid_prime [2, 3, 13, 97] ⟨22699, 12, [(2, 1), (3, 2), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_22717 : Nat.Prime 22717 := by
  apply nodeValid_prime [2, 3, 631] ⟨22717, 2, [(2, 2), (3, 2), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
  · decide +kernel

theorem prime_22769 : Nat.Prime 22769 := by
  apply nodeValid_prime [2, 1423] ⟨22769, 3, [(2, 4), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1423
  · decide +kernel

theorem prime_22783 : Nat.Prime 22783 := by
  apply nodeValid_prime [2, 3, 3797] ⟨22783, 3, [(2, 1), (3, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3797
  · decide +kernel

theorem prime_22859 : Nat.Prime 22859 := by
  apply nodeValid_prime [2, 11, 1039] ⟨22859, 2, [(2, 1), (11, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1039
  · decide +kernel

theorem prime_22937 : Nat.Prime 22937 := by
  apply nodeValid_prime [2, 47, 61] ⟨22937, 3, [(2, 3), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_22961 : Nat.Prime 22961 := by
  apply nodeValid_prime [2, 5, 7, 41] ⟨22961, 6, [(2, 4), (5, 1), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_22963 : Nat.Prime 22963 := by
  apply nodeValid_prime [2, 3, 43, 89] ⟨22963, 3, [(2, 1), (3, 1), (43, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_89
  · decide +kernel

theorem prime_23021 : Nat.Prime 23021 := by
  apply nodeValid_prime [2, 5, 1151] ⟨23021, 2, [(2, 2), (5, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1151
  · decide +kernel

theorem prime_23027 : Nat.Prime 23027 := by
  apply nodeValid_prime [2, 29, 397] ⟨23027, 2, [(2, 1), (29, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_397
  · decide +kernel

theorem prime_23029 : Nat.Prime 23029 := by
  apply nodeValid_prime [2, 3, 19, 101] ⟨23029, 2, [(2, 2), (3, 1), (19, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_101
  · decide +kernel

theorem prime_23041 : Nat.Prime 23041 := by
  apply nodeValid_prime [2, 3, 5] ⟨23041, 11, [(2, 9), (3, 2), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_23057 : Nat.Prime 23057 := by
  apply nodeValid_prime [2, 11, 131] ⟨23057, 5, [(2, 4), (11, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_131
  · decide +kernel

theorem prime_23081 : Nat.Prime 23081 := by
  apply nodeValid_prime [2, 5, 577] ⟨23081, 3, [(2, 3), (5, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_577
  · decide +kernel

theorem prime_23087 : Nat.Prime 23087 := by
  apply nodeValid_prime [2, 7, 17, 97] ⟨23087, 5, [(2, 1), (7, 1), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_23173 : Nat.Prime 23173 := by
  apply nodeValid_prime [2, 3, 1931] ⟨23173, 5, [(2, 2), (3, 1), (1931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1931
  · decide +kernel

theorem prime_23197 : Nat.Prime 23197 := by
  apply nodeValid_prime [2, 3, 1933] ⟨23197, 2, [(2, 2), (3, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1933
  · decide +kernel

theorem prime_23201 : Nat.Prime 23201 := by
  apply nodeValid_prime [2, 5, 29] ⟨23201, 3, [(2, 5), (5, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_23203 : Nat.Prime 23203 := by
  apply nodeValid_prime [2, 3, 1289] ⟨23203, 3, [(2, 1), (3, 2), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1289
  · decide +kernel

theorem prime_23227 : Nat.Prime 23227 := by
  apply nodeValid_prime [2, 3, 7, 79] ⟨23227, 3, [(2, 1), (3, 1), (7, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_23251 : Nat.Prime 23251 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨23251, 2, [(2, 1), (3, 1), (5, 3), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_23291 : Nat.Prime 23291 := by
  apply nodeValid_prime [2, 5, 17, 137] ⟨23291, 6, [(2, 1), (5, 1), (17, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_137
  · decide +kernel

theorem prime_23293 : Nat.Prime 23293 := by
  apply nodeValid_prime [2, 3, 647] ⟨23293, 5, [(2, 2), (3, 2), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_647
  · decide +kernel

theorem prime_23327 : Nat.Prime 23327 := by
  apply nodeValid_prime [2, 107, 109] ⟨23327, 5, [(2, 1), (107, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_109
  · decide +kernel

theorem prime_23371 : Nat.Prime 23371 := by
  apply nodeValid_prime [2, 3, 5, 19, 41] ⟨23371, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_23417 : Nat.Prime 23417 := by
  apply nodeValid_prime [2, 2927] ⟨23417, 3, [(2, 3), (2927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2927
  · decide +kernel

theorem prime_23497 : Nat.Prime 23497 := by
  apply nodeValid_prime [2, 3, 11, 89] ⟨23497, 5, [(2, 3), (3, 1), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_23557 : Nat.Prime 23557 := by
  apply nodeValid_prime [2, 3, 13, 151] ⟨23557, 5, [(2, 2), (3, 1), (13, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_151
  · decide +kernel

theorem prime_23567 : Nat.Prime 23567 := by
  apply nodeValid_prime [2, 11783] ⟨23567, 5, [(2, 1), (11783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11783
  · decide +kernel

theorem prime_23581 : Nat.Prime 23581 := by
  apply nodeValid_prime [2, 3, 5, 131] ⟨23581, 6, [(2, 2), (3, 2), (5, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
  · decide +kernel

theorem prime_23627 : Nat.Prime 23627 := by
  apply nodeValid_prime [2, 11813] ⟨23627, 2, [(2, 1), (11813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11813
  · decide +kernel

theorem prime_23629 : Nat.Prime 23629 := by
  apply nodeValid_prime [2, 3, 11, 179] ⟨23629, 2, [(2, 2), (3, 1), (11, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_179
  · decide +kernel

theorem prime_23671 : Nat.Prime 23671 := by
  apply nodeValid_prime [2, 3, 5, 263] ⟨23671, 3, [(2, 1), (3, 2), (5, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_23719 : Nat.Prime 23719 := by
  apply nodeValid_prime [2, 3, 59, 67] ⟨23719, 6, [(2, 1), (3, 1), (59, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_67
  · decide +kernel

theorem prime_23753 : Nat.Prime 23753 := by
  apply nodeValid_prime [2, 2969] ⟨23753, 3, [(2, 3), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2969
  · decide +kernel

theorem prime_23813 : Nat.Prime 23813 := by
  apply nodeValid_prime [2, 5953] ⟨23813, 2, [(2, 2), (5953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5953
  · decide +kernel

theorem prime_23819 : Nat.Prime 23819 := by
  apply nodeValid_prime [2, 11909] ⟨23819, 2, [(2, 1), (11909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11909
  · decide +kernel

theorem prime_23869 : Nat.Prime 23869 := by
  apply nodeValid_prime [2, 3, 13, 17] ⟨23869, 2, [(2, 2), (3, 3), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_23887 : Nat.Prime 23887 := by
  apply nodeValid_prime [2, 3, 1327] ⟨23887, 3, [(2, 1), (3, 2), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1327
  · decide +kernel

theorem prime_24001 : Nat.Prime 24001 := by
  apply nodeValid_prime [2, 3, 5] ⟨24001, 14, [(2, 6), (3, 1), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_24007 : Nat.Prime 24007 := by
  apply nodeValid_prime [2, 3, 4001] ⟨24007, 17, [(2, 1), (3, 1), (4001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4001
  · decide +kernel

theorem prime_24019 : Nat.Prime 24019 := by
  apply nodeValid_prime [2, 3, 4003] ⟨24019, 2, [(2, 1), (3, 1), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4003
  · decide +kernel

theorem prime_24029 : Nat.Prime 24029 := by
  apply nodeValid_prime [2, 6007] ⟨24029, 2, [(2, 2), (6007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6007
  · decide +kernel

theorem prime_24043 : Nat.Prime 24043 := by
  apply nodeValid_prime [2, 3, 4007] ⟨24043, 2, [(2, 1), (3, 1), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4007
  · decide +kernel

theorem prime_24083 : Nat.Prime 24083 := by
  apply nodeValid_prime [2, 12041] ⟨24083, 2, [(2, 1), (12041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12041
  · decide +kernel

theorem prime_24091 : Nat.Prime 24091 := by
  apply nodeValid_prime [2, 3, 5, 11, 73] ⟨24091, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_24107 : Nat.Prime 24107 := by
  apply nodeValid_prime [2, 17, 709] ⟨24107, 2, [(2, 1), (17, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_709
  · decide +kernel

end Sude.Lucas.Generated
