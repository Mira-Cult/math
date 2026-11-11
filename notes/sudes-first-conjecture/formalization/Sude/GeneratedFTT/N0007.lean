import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_479 : Nat.Prime 479 := by
  apply nodeValid_prime [2, 239] ⟨479, 13, [(2, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_239
  · decide +kernel

theorem prime_503 : Nat.Prime 503 := by
  apply nodeValid_prime [2, 251] ⟨503, 5, [(2, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_251
  · decide +kernel

theorem prime_571 : Nat.Prime 571 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨571, 3, [(2, 1), (3, 1), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_701 : Nat.Prime 701 := by
  apply nodeValid_prime [2, 5, 7] ⟨701, 2, [(2, 2), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_1051 : Nat.Prime 1051 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨1051, 7, [(2, 1), (3, 1), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_1091 : Nat.Prime 1091 := by
  apply nodeValid_prime [2, 5, 109] ⟨1091, 2, [(2, 1), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_1123 : Nat.Prime 1123 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨1123, 2, [(2, 1), (3, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_1559 : Nat.Prime 1559 := by
  apply nodeValid_prime [2, 19, 41] ⟨1559, 19, [(2, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_1657 : Nat.Prime 1657 := by
  apply nodeValid_prime [2, 3, 23] ⟨1657, 11, [(2, 3), (3, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_1669 : Nat.Prime 1669 := by
  apply nodeValid_prime [2, 3, 139] ⟨1669, 2, [(2, 2), (3, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_1759 : Nat.Prime 1759 := by
  apply nodeValid_prime [2, 3, 293] ⟨1759, 6, [(2, 1), (3, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
  · decide +kernel

theorem prime_2063 : Nat.Prime 2063 := by
  apply nodeValid_prime [2, 1031] ⟨2063, 5, [(2, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1031
  · decide +kernel

theorem prime_2437 : Nat.Prime 2437 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨2437, 2, [(2, 2), (3, 1), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_2683 : Nat.Prime 2683 := by
  apply nodeValid_prime [2, 3, 149] ⟨2683, 2, [(2, 1), (3, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
  · decide +kernel

theorem prime_2719 : Nat.Prime 2719 := by
  apply nodeValid_prime [2, 3, 151] ⟨2719, 3, [(2, 1), (3, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
  · decide +kernel

theorem prime_2791 : Nat.Prime 2791 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨2791, 6, [(2, 1), (3, 2), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_2833 : Nat.Prime 2833 := by
  apply nodeValid_prime [2, 3, 59] ⟨2833, 5, [(2, 4), (3, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_2909 : Nat.Prime 2909 := by
  apply nodeValid_prime [2, 727] ⟨2909, 2, [(2, 2), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_727
  · decide +kernel

theorem prime_3253 : Nat.Prime 3253 := by
  apply nodeValid_prime [2, 3, 271] ⟨3253, 2, [(2, 2), (3, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
  · decide +kernel

theorem prime_3313 : Nat.Prime 3313 := by
  apply nodeValid_prime [2, 3, 23] ⟨3313, 10, [(2, 4), (3, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_3539 : Nat.Prime 3539 := by
  apply nodeValid_prime [2, 29, 61] ⟨3539, 2, [(2, 1), (29, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_61
  · decide +kernel

theorem prime_3613 : Nat.Prime 3613 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨3613, 2, [(2, 2), (3, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_3659 : Nat.Prime 3659 := by
  apply nodeValid_prime [2, 31, 59] ⟨3659, 2, [(2, 1), (31, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_59
  · decide +kernel

theorem prime_4363 : Nat.Prime 4363 := by
  apply nodeValid_prime [2, 3, 727] ⟨4363, 2, [(2, 1), (3, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_727
  · decide +kernel

theorem prime_4967 : Nat.Prime 4967 := by
  apply nodeValid_prime [2, 13, 191] ⟨4967, 5, [(2, 1), (13, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_191
  · decide +kernel

theorem prime_4999 : Nat.Prime 4999 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨4999, 3, [(2, 1), (3, 1), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_5167 : Nat.Prime 5167 := by
  apply nodeValid_prime [2, 3, 7, 41] ⟨5167, 6, [(2, 1), (3, 2), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_5381 : Nat.Prime 5381 := by
  apply nodeValid_prime [2, 5, 269] ⟨5381, 3, [(2, 2), (5, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
  · decide +kernel

theorem prime_5501 : Nat.Prime 5501 := by
  apply nodeValid_prime [2, 5, 11] ⟨5501, 2, [(2, 2), (5, 3), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_6521 : Nat.Prime 6521 := by
  apply nodeValid_prime [2, 5, 163] ⟨6521, 6, [(2, 3), (5, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
  · decide +kernel

theorem prime_6857 : Nat.Prime 6857 := by
  apply nodeValid_prime [2, 857] ⟨6857, 3, [(2, 3), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_857
  · decide +kernel

theorem prime_7057 : Nat.Prime 7057 := by
  apply nodeValid_prime [2, 3, 7] ⟨7057, 5, [(2, 4), (3, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_7079 : Nat.Prime 7079 := by
  apply nodeValid_prime [2, 3539] ⟨7079, 7, [(2, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3539
  · decide +kernel

theorem prime_7451 : Nat.Prime 7451 := by
  apply nodeValid_prime [2, 5, 149] ⟨7451, 2, [(2, 1), (5, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
  · decide +kernel

theorem prime_7591 : Nat.Prime 7591 := by
  apply nodeValid_prime [2, 3, 5, 11, 23] ⟨7591, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_7853 : Nat.Prime 7853 := by
  apply nodeValid_prime [2, 13, 151] ⟨7853, 2, [(2, 2), (13, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_151
  · decide +kernel

theorem prime_8317 : Nat.Prime 8317 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨8317, 6, [(2, 2), (3, 3), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_9421 : Nat.Prime 9421 := by
  apply nodeValid_prime [2, 3, 5, 157] ⟨9421, 2, [(2, 2), (3, 1), (5, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
  · decide +kernel

theorem prime_9811 : Nat.Prime 9811 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨9811, 3, [(2, 1), (3, 2), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_11197 : Nat.Prime 11197 := by
  apply nodeValid_prime [2, 3, 311] ⟨11197, 2, [(2, 2), (3, 2), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
  · decide +kernel

theorem prime_11251 : Nat.Prime 11251 := by
  apply nodeValid_prime [2, 3, 5] ⟨11251, 13, [(2, 1), (3, 2), (5, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_11969 : Nat.Prime 11969 := by
  apply nodeValid_prime [2, 11, 17] ⟨11969, 3, [(2, 6), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_12671 : Nat.Prime 12671 := by
  apply nodeValid_prime [2, 5, 7, 181] ⟨12671, 14, [(2, 1), (5, 1), (7, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_181
  · decide +kernel

theorem prime_13043 : Nat.Prime 13043 := by
  apply nodeValid_prime [2, 6521] ⟨13043, 2, [(2, 1), (6521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6521
  · decide +kernel

theorem prime_14159 : Nat.Prime 14159 := by
  apply nodeValid_prime [2, 7079] ⟨14159, 13, [(2, 1), (7079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7079
  · decide +kernel

theorem prime_14629 : Nat.Prime 14629 := by
  apply nodeValid_prime [2, 3, 23, 53] ⟨14629, 2, [(2, 2), (3, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_15091 : Nat.Prime 15091 := by
  apply nodeValid_prime [2, 3, 5, 503] ⟨15091, 2, [(2, 1), (3, 1), (5, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_503
  · decide +kernel

theorem prime_17239 : Nat.Prime 17239 := by
  apply nodeValid_prime [2, 3, 13, 17] ⟨17239, 6, [(2, 1), (3, 1), (13, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_18401 : Nat.Prime 18401 := by
  apply nodeValid_prime [2, 5, 23] ⟨18401, 3, [(2, 5), (5, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_19801 : Nat.Prime 19801 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨19801, 13, [(2, 3), (3, 2), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_19979 : Nat.Prime 19979 := by
  apply nodeValid_prime [2, 7, 1427] ⟨19979, 2, [(2, 1), (7, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1427
  · decide +kernel

theorem prime_20399 : Nat.Prime 20399 := by
  apply nodeValid_prime [2, 7, 31, 47] ⟨20399, 7, [(2, 1), (7, 1), (31, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_47
  · decide +kernel

theorem prime_20849 : Nat.Prime 20849 := by
  apply nodeValid_prime [2, 1303] ⟨20849, 3, [(2, 4), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1303
  · decide +kernel

theorem prime_21179 : Nat.Prime 21179 := by
  apply nodeValid_prime [2, 10589] ⟨21179, 2, [(2, 1), (10589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10589
  · decide +kernel

theorem prime_25237 : Nat.Prime 25237 := by
  apply nodeValid_prime [2, 3, 701] ⟨25237, 2, [(2, 2), (3, 2), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_701
  · decide +kernel

theorem prime_26731 : Nat.Prime 26731 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨26731, 3, [(2, 1), (3, 5), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_27799 : Nat.Prime 27799 := by
  apply nodeValid_prime [2, 3, 41, 113] ⟨27799, 7, [(2, 1), (3, 1), (41, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_113
  · decide +kernel

theorem prime_28319 : Nat.Prime 28319 := by
  apply nodeValid_prime [2, 14159] ⟨28319, 7, [(2, 1), (14159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14159
  · decide +kernel

theorem prime_29569 : Nat.Prime 29569 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨29569, 17, [(2, 7), (3, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_30391 : Nat.Prime 30391 := by
  apply nodeValid_prime [2, 3, 5, 1013] ⟨30391, 3, [(2, 1), (3, 1), (5, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1013
  · decide +kernel

theorem prime_33151 : Nat.Prime 33151 := by
  apply nodeValid_prime [2, 3, 5, 13, 17] ⟨33151, 3, [(2, 1), (3, 1), (5, 2), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_36389 : Nat.Prime 36389 := by
  apply nodeValid_prime [2, 11, 827] ⟨36389, 3, [(2, 2), (11, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_827
  · decide +kernel

theorem prime_36721 : Nat.Prime 36721 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨36721, 37, [(2, 4), (3, 3), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_37633 : Nat.Prime 37633 := by
  apply nodeValid_prime [2, 3, 7] ⟨37633, 5, [(2, 8), (3, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_39551 : Nat.Prime 39551 := by
  apply nodeValid_prime [2, 5, 7, 113] ⟨39551, 7, [(2, 1), (5, 2), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_41131 : Nat.Prime 41131 := by
  apply nodeValid_prime [2, 3, 5, 457] ⟨41131, 10, [(2, 1), (3, 2), (5, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_457
  · decide +kernel

theorem prime_41143 : Nat.Prime 41143 := by
  apply nodeValid_prime [2, 3, 6857] ⟨41143, 3, [(2, 1), (3, 1), (6857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6857
  · decide +kernel

theorem prime_42359 : Nat.Prime 42359 := by
  apply nodeValid_prime [2, 21179] ⟨42359, 7, [(2, 1), (21179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21179
  · decide +kernel

theorem prime_44789 : Nat.Prime 44789 := by
  apply nodeValid_prime [2, 11197] ⟨44789, 2, [(2, 2), (11197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11197
  · decide +kernel

theorem prime_45061 : Nat.Prime 45061 := by
  apply nodeValid_prime [2, 3, 5, 751] ⟨45061, 2, [(2, 2), (3, 1), (5, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_751
  · decide +kernel

theorem prime_45179 : Nat.Prime 45179 := by
  apply nodeValid_prime [2, 7, 461] ⟨45179, 6, [(2, 1), (7, 2), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_461
  · decide +kernel

theorem prime_45329 : Nat.Prime 45329 := by
  apply nodeValid_prime [2, 2833] ⟨45329, 3, [(2, 4), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2833
  · decide +kernel

theorem prime_53569 : Nat.Prime 53569 := by
  apply nodeValid_prime [2, 3, 31] ⟨53569, 19, [(2, 6), (3, 3), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_57601 : Nat.Prime 57601 := by
  apply nodeValid_prime [2, 3, 5] ⟨57601, 7, [(2, 8), (3, 2), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_63857 : Nat.Prime 63857 := by
  apply nodeValid_prime [2, 13, 307] ⟨63857, 3, [(2, 4), (13, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_307
  · decide +kernel

theorem prime_69809 : Nat.Prime 69809 := by
  apply nodeValid_prime [2, 4363] ⟨69809, 3, [(2, 4), (4363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4363
  · decide +kernel

theorem prime_76801 : Nat.Prime 76801 := by
  apply nodeValid_prime [2, 3, 5] ⟨76801, 17, [(2, 10), (3, 1), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_82721 : Nat.Prime 82721 := by
  apply nodeValid_prime [2, 5, 11, 47] ⟨82721, 6, [(2, 5), (5, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_113081 : Nat.Prime 113081 := by
  apply nodeValid_prime [2, 5, 11, 257] ⟨113081, 3, [(2, 3), (5, 1), (11, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_257
  · decide +kernel

theorem prime_114493 : Nat.Prime 114493 := by
  apply nodeValid_prime [2, 3, 7, 29, 47] ⟨114493, 2, [(2, 2), (3, 1), (7, 1), (29, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_47
  · decide +kernel

theorem prime_119953 : Nat.Prime 119953 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨119953, 5, [(2, 4), (3, 2), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_147377 : Nat.Prime 147377 := by
  apply nodeValid_prime [2, 61, 151] ⟨147377, 3, [(2, 4), (61, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_151
  · decide +kernel

theorem prime_164051 : Nat.Prime 164051 := by
  apply nodeValid_prime [2, 5, 17, 193] ⟨164051, 2, [(2, 1), (5, 2), (17, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_193
  · decide +kernel

theorem prime_165443 : Nat.Prime 165443 := by
  apply nodeValid_prime [2, 82721] ⟨165443, 2, [(2, 1), (82721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82721
  · decide +kernel

theorem prime_185551 : Nat.Prime 185551 := by
  apply nodeValid_prime [2, 3, 5, 1237] ⟨185551, 11, [(2, 1), (3, 1), (5, 2), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1237
  · decide +kernel

theorem prime_207709 : Nat.Prime 207709 := by
  apply nodeValid_prime [2, 3, 19, 911] ⟨207709, 2, [(2, 2), (3, 1), (19, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_911
  · decide +kernel

theorem prime_215617 : Nat.Prime 215617 := by
  apply nodeValid_prime [2, 3, 1123] ⟨215617, 7, [(2, 6), (3, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1123
  · decide +kernel

theorem prime_225949 : Nat.Prime 225949 := by
  apply nodeValid_prime [2, 3, 19, 991] ⟨225949, 2, [(2, 2), (3, 1), (19, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_991
  · decide +kernel

theorem prime_227371 : Nat.Prime 227371 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 53] ⟨227371, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_251297 : Nat.Prime 251297 := by
  apply nodeValid_prime [2, 7853] ⟨251297, 3, [(2, 5), (7853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7853
  · decide +kernel

theorem prime_361433 : Nat.Prime 361433 := by
  apply nodeValid_prime [2, 45179] ⟨361433, 3, [(2, 3), (45179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45179
  · decide +kernel

theorem prime_382583 : Nat.Prime 382583 := by
  apply nodeValid_prime [2, 23, 8317] ⟨382583, 5, [(2, 1), (23, 1), (8317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_8317
  · decide +kernel

theorem prime_427781 : Nat.Prime 427781 := by
  apply nodeValid_prime [2, 5, 73, 293] ⟨427781, 2, [(2, 2), (5, 1), (73, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_293
  · decide +kernel

theorem prime_453643 : Nat.Prime 453643 := by
  apply nodeValid_prime [2, 3, 7, 1543] ⟨453643, 3, [(2, 1), (3, 1), (7, 2), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1543
  · decide +kernel

theorem prime_592223 : Nat.Prime 592223 := by
  apply nodeValid_prime [2, 37, 53, 151] ⟨592223, 5, [(2, 1), (37, 1), (53, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_53
    · exact prime_151
  · decide +kernel

theorem prime_689561 : Nat.Prime 689561 := by
  apply nodeValid_prime [2, 5, 17239] ⟨689561, 3, [(2, 3), (5, 1), (17239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17239
  · decide +kernel

theorem prime_844957 : Nat.Prime 844957 := by
  apply nodeValid_prime [2, 3, 7, 479] ⟨844957, 2, [(2, 2), (3, 2), (7, 2), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_479
  · decide +kernel

theorem prime_893999 : Nat.Prime 893999 := by
  apply nodeValid_prime [2, 7, 63857] ⟨893999, 7, [(2, 1), (7, 1), (63857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_63857
  · decide +kernel

theorem prime_936097 : Nat.Prime 936097 := by
  apply nodeValid_prime [2, 3, 7, 199] ⟨936097, 5, [(2, 5), (3, 1), (7, 2), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199
  · decide +kernel

theorem prime_1049899 : Nat.Prime 1049899 := by
  apply nodeValid_prime [2, 3, 233, 751] ⟨1049899, 3, [(2, 1), (3, 1), (233, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_751
  · decide +kernel

theorem prime_1054171 : Nat.Prime 1054171 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 53] ⟨1054171, 3, [(2, 1), (3, 2), (5, 1), (13, 1), (17, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_53
  · decide +kernel

theorem prime_1148713 : Nat.Prime 1148713 := by
  apply nodeValid_prime [2, 3, 23, 2081] ⟨1148713, 5, [(2, 3), (3, 1), (23, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2081
  · decide +kernel

theorem prime_1398863 : Nat.Prime 1398863 := by
  apply nodeValid_prime [2, 17, 41143] ⟨1398863, 5, [(2, 1), (17, 1), (41143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41143
  · decide +kernel

theorem prime_1858807 : Nat.Prime 1858807 := by
  apply nodeValid_prime [2, 3, 37, 2791] ⟨1858807, 3, [(2, 1), (3, 2), (37, 1), (2791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2791
  · decide +kernel

theorem prime_2492509 : Nat.Prime 2492509 := by
  apply nodeValid_prime [2, 3, 207709] ⟨2492509, 2, [(2, 2), (3, 1), (207709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_207709
  · decide +kernel

theorem prime_2552449 : Nat.Prime 2552449 := by
  apply nodeValid_prime [2, 3, 17, 23] ⟨2552449, 41, [(2, 7), (3, 1), (17, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_2596057 : Nat.Prime 2596057 := by
  apply nodeValid_prime [2, 3, 23, 4703] ⟨2596057, 10, [(2, 3), (3, 1), (23, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_4703
  · decide +kernel

theorem prime_2652743 : Nat.Prime 2652743 := by
  apply nodeValid_prime [2, 19, 69809] ⟨2652743, 5, [(2, 1), (19, 1), (69809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_69809
  · decide +kernel

theorem prime_2884493 : Nat.Prime 2884493 := by
  apply nodeValid_prime [2, 13, 17, 251] ⟨2884493, 2, [(2, 2), (13, 2), (17, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_251
  · decide +kernel

theorem prime_3150509 : Nat.Prime 3150509 := by
  apply nodeValid_prime [2, 17, 107, 433] ⟨3150509, 2, [(2, 2), (17, 1), (107, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_107
    · exact prime_433
  · decide +kernel

theorem prime_4120621 : Nat.Prime 4120621 := by
  apply nodeValid_prime [2, 3, 5, 7, 9811] ⟨4120621, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (9811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_9811
  · decide +kernel

theorem prime_4178959 : Nat.Prime 4178959 := by
  apply nodeValid_prime [2, 3, 7, 29, 47, 73] ⟨4178959, 7, [(2, 1), (3, 1), (7, 1), (29, 1), (47, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_47
    · exact prime_73
  · decide +kernel

theorem prime_4594853 : Nat.Prime 4594853 := by
  apply nodeValid_prime [2, 1148713] ⟨4594853, 2, [(2, 2), (1148713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1148713
  · decide +kernel

theorem prime_4808707 : Nat.Prime 4808707 := by
  apply nodeValid_prime [2, 3, 7, 114493] ⟨4808707, 2, [(2, 1), (3, 1), (7, 1), (114493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_114493
  · decide +kernel

theorem prime_8071517 : Nat.Prime 8071517 := by
  apply nodeValid_prime [2, 101, 19979] ⟨8071517, 2, [(2, 2), (101, 1), (19979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_19979
  · decide +kernel

theorem prime_9992629 : Nat.Prime 9992629 := by
  apply nodeValid_prime [2, 3, 197, 1409] ⟨9992629, 10, [(2, 2), (3, 2), (197, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1409
  · decide +kernel

theorem prime_10021637 : Nat.Prime 10021637 := by
  apply nodeValid_prime [2, 17, 147377] ⟨10021637, 2, [(2, 2), (17, 1), (147377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_147377
  · decide +kernel

theorem prime_19440731 : Nat.Prime 19440731 := by
  apply nodeValid_prime [2, 5, 29, 43, 1559] ⟨19440731, 2, [(2, 1), (5, 1), (29, 1), (43, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_43
    · exact prime_1559
  · decide +kernel

theorem prime_23406511 : Nat.Prime 23406511 := by
  apply nodeValid_prime [2, 3, 5, 151, 5167] ⟨23406511, 3, [(2, 1), (3, 1), (5, 1), (151, 1), (5167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_5167
  · decide +kernel

theorem prime_23460637 : Nat.Prime 23460637 := by
  apply nodeValid_prime [2, 3, 601, 3253] ⟨23460637, 5, [(2, 2), (3, 1), (601, 1), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
    · exact prime_3253
  · decide +kernel

theorem prime_37947461 : Nat.Prime 37947461 := by
  apply nodeValid_prime [2, 5, 67, 28319] ⟨37947461, 2, [(2, 2), (5, 1), (67, 1), (28319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_28319
  · decide +kernel

theorem prime_39327199 : Nat.Prime 39327199 := by
  apply nodeValid_prime [2, 3, 43, 313, 487] ⟨39327199, 3, [(2, 1), (3, 1), (43, 1), (313, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_313
    · exact prime_487
  · decide +kernel

theorem prime_43702259 : Nat.Prime 43702259 := by
  apply nodeValid_prime [2, 719, 30391] ⟨43702259, 2, [(2, 1), (719, 1), (30391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_719
    · exact prime_30391
  · decide +kernel

theorem prime_61704941 : Nat.Prime 61704941 := by
  apply nodeValid_prime [2, 5, 11, 101, 2777] ⟨61704941, 10, [(2, 2), (5, 1), (11, 1), (101, 1), (2777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_101
    · exact prime_2777
  · decide +kernel

theorem prime_70770221 : Nat.Prime 70770221 := by
  apply nodeValid_prime [2, 5, 349, 10139] ⟨70770221, 2, [(2, 2), (5, 1), (349, 1), (10139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
    · exact prime_10139
  · decide +kernel

theorem prime_73274219 : Nat.Prime 73274219 := by
  apply nodeValid_prime [2, 3061, 11969] ⟨73274219, 2, [(2, 1), (3061, 1), (11969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3061
    · exact prime_11969
  · decide +kernel

theorem prime_76966247 : Nat.Prime 76966247 := by
  apply nodeValid_prime [2, 7, 139, 39551] ⟨76966247, 5, [(2, 1), (7, 1), (139, 1), (39551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_139
    · exact prime_39551
  · decide +kernel

theorem prime_81115873 : Nat.Prime 81115873 := by
  apply nodeValid_prime [2, 3, 844957] ⟨81115873, 5, [(2, 5), (3, 1), (844957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_844957
  · decide +kernel

theorem prime_97687823 : Nat.Prime 97687823 := by
  apply nodeValid_prime [2, 113, 571, 757] ⟨97687823, 5, [(2, 1), (113, 1), (571, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_571
    · exact prime_757
  · decide +kernel

theorem prime_148953499 : Nat.Prime 148953499 := by
  apply nodeValid_prime [2, 3, 1217, 20399] ⟨148953499, 2, [(2, 1), (3, 1), (1217, 1), (20399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1217
    · exact prime_20399
  · decide +kernel

theorem prime_161856887 : Nat.Prime 161856887 := by
  apply nodeValid_prime [2, 7193, 11251] ⟨161856887, 5, [(2, 1), (7193, 1), (11251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7193
    · exact prime_11251
  · decide +kernel

theorem prime_280878133 : Nat.Prime 280878133 := by
  apply nodeValid_prime [2, 3, 23406511] ⟨280878133, 2, [(2, 2), (3, 1), (23406511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23406511
  · decide +kernel

theorem prime_472710089 : Nat.Prime 472710089 := by
  apply nodeValid_prime [2, 79, 139, 5381] ⟨472710089, 3, [(2, 3), (79, 1), (139, 1), (5381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_139
    · exact prime_5381
  · decide +kernel

theorem prime_487438993 : Nat.Prime 487438993 := by
  apply nodeValid_prime [2, 3, 463, 2437] ⟨487438993, 7, [(2, 4), (3, 3), (463, 1), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
    · exact prime_2437
  · decide +kernel

theorem prime_922377017 : Nat.Prime 922377017 := by
  apply nodeValid_prime [2, 11, 29, 361433] ⟨922377017, 3, [(2, 3), (11, 1), (29, 1), (361433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_361433
  · decide +kernel

theorem prime_1223313797 : Nat.Prime 1223313797 := by
  apply nodeValid_prime [2, 1217, 251297] ⟨1223313797, 2, [(2, 2), (1217, 1), (251297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1217
    · exact prime_251297
  · decide +kernel

theorem prime_1482078319 : Nat.Prime 1482078319 := by
  apply nodeValid_prime [2, 3, 7, 19, 31, 181, 331] ⟨1482078319, 13, [(2, 1), (3, 1), (7, 1), (19, 1), (31, 1), (181, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_31
    · exact prime_181
    · exact prime_331
  · decide +kernel

theorem prime_2152430227 : Nat.Prime 2152430227 := by
  apply nodeValid_prime [2, 3, 941, 42359] ⟨2152430227, 2, [(2, 1), (3, 3), (941, 1), (42359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_941
    · exact prime_42359
  · decide +kernel

theorem prime_2205299879 : Nat.Prime 2205299879 := by
  apply nodeValid_prime [2, 47, 23460637] ⟨2205299879, 17, [(2, 1), (47, 1), (23460637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_23460637
  · decide +kernel

theorem prime_2838346727 : Nat.Prime 2838346727 := by
  apply nodeValid_prime [2, 73, 19440731] ⟨2838346727, 5, [(2, 1), (73, 1), (19440731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_19440731
  · decide +kernel

theorem prime_3397493861 : Nat.Prime 3397493861 := by
  apply nodeValid_prime [2, 5, 17, 9992629] ⟨3397493861, 2, [(2, 2), (5, 1), (17, 1), (9992629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_9992629
  · decide +kernel

theorem prime_4470099773 : Nat.Prime 4470099773 := by
  apply nodeValid_prime [2, 23, 127, 382583] ⟨4470099773, 2, [(2, 2), (23, 1), (127, 1), (382583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_127
    · exact prime_382583
  · decide +kernel

theorem prime_5724292297 : Nat.Prime 5724292297 := by
  apply nodeValid_prime [2, 3, 1049, 227371] ⟨5724292297, 5, [(2, 3), (3, 1), (1049, 1), (227371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1049
    · exact prime_227371
  · decide +kernel

theorem prime_5849267917 : Nat.Prime 5849267917 := by
  apply nodeValid_prime [2, 3, 487438993] ⟨5849267917, 2, [(2, 2), (3, 1), (487438993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487438993
  · decide +kernel

theorem prime_6741075193 : Nat.Prime 6741075193 := by
  apply nodeValid_prime [2, 3, 280878133] ⟨6741075193, 7, [(2, 3), (3, 1), (280878133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_280878133
  · decide +kernel

theorem prime_7439852897 : Nat.Prime 7439852897 := by
  apply nodeValid_prime [2, 7, 179, 185551] ⟨7439852897, 5, [(2, 5), (7, 1), (179, 1), (185551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_179
    · exact prime_185551
  · decide +kernel

theorem prime_7622116577 : Nat.Prime 7622116577 := by
  apply nodeValid_prime [2, 131, 193, 9421] ⟨7622116577, 3, [(2, 5), (131, 1), (193, 1), (9421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_193
    · exact prime_9421
  · decide +kernel

theorem prime_17126393483 : Nat.Prime 17126393483 := by
  apply nodeValid_prime [2, 11, 70770221] ⟨17126393483, 2, [(2, 1), (11, 2), (70770221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_70770221
  · decide +kernel

theorem prime_17784940073 : Nat.Prime 17784940073 := by
  apply nodeValid_prime [2, 23, 37, 1433, 1823] ⟨17784940073, 3, [(2, 3), (23, 1), (37, 1), (1433, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_1433
    · exact prime_1823
  · decide +kernel

theorem prime_51101077739 : Nat.Prime 51101077739 := by
  apply nodeValid_prime [2, 113081, 225949] ⟨51101077739, 2, [(2, 1), (113081, 1), (225949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113081
    · exact prime_225949
  · decide +kernel

theorem prime_51379190111 : Nat.Prime 51379190111 := by
  apply nodeValid_prime [2, 5, 7451, 689561] ⟨51379190111, 14, [(2, 1), (5, 1), (7451, 1), (689561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7451
    · exact prime_689561
  · decide +kernel

theorem prime_52360673129 : Nat.Prime 52360673129 := by
  apply nodeValid_prime [2, 67, 97687823] ⟨52360673129, 3, [(2, 3), (67, 1), (97687823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_97687823
  · decide +kernel

theorem prime_54072705779 : Nat.Prime 54072705779 := by
  apply nodeValid_prime [2, 7, 13, 103, 2884493] ⟨54072705779, 6, [(2, 1), (7, 1), (13, 1), (103, 1), (2884493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_103
    · exact prime_2884493
  · decide +kernel

theorem prime_101924808961 : Nat.Prime 101924808961 := by
  apply nodeValid_prime [2, 3, 5, 13, 761, 2683] ⟨101924808961, 7, [(2, 8), (3, 1), (5, 1), (13, 1), (761, 1), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_761
    · exact prime_2683
  · decide +kernel

theorem prime_101924810011 : Nat.Prime 101924810011 := by
  apply nodeValid_prime [2, 3, 5, 271, 4178959] ⟨101924810011, 2, [(2, 1), (3, 2), (5, 1), (271, 1), (4178959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
    · exact prime_4178959
  · decide +kernel

theorem prime_101924815831 : Nat.Prime 101924815831 := by
  apply nodeValid_prime [2, 3, 5, 3397493861] ⟨101924815831, 3, [(2, 1), (3, 1), (5, 1), (3397493861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3397493861
  · decide +kernel

theorem prime_102202155479 : Nat.Prime 102202155479 := by
  apply nodeValid_prime [2, 51101077739] ⟨102202155479, 7, [(2, 1), (51101077739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_51101077739
  · decide +kernel

theorem prime_102202157237 : Nat.Prime 102202157237 := by
  apply nodeValid_prime [2, 83, 107, 379, 7591] ⟨102202157237, 2, [(2, 2), (83, 1), (107, 1), (379, 1), (7591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_107
    · exact prime_379
    · exact prime_7591
  · decide +kernel

theorem prime_102202159421 : Nat.Prime 102202159421 := by
  apply nodeValid_prime [2, 5, 571, 2477, 3613] ⟨102202159421, 3, [(2, 2), (5, 1), (571, 1), (2477, 1), (3613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_571
    · exact prime_2477
    · exact prime_3613
  · decide +kernel

theorem prime_102480007057 : Nat.Prime 102480007057 := by
  apply nodeValid_prime [2, 3, 7, 14629, 20849] ⟨102480007057, 5, [(2, 4), (3, 1), (7, 1), (14629, 1), (20849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14629
    · exact prime_20849
  · decide +kernel

theorem prime_102480007313 : Nat.Prime 102480007313 := by
  apply nodeValid_prime [2, 43, 148953499] ⟨102480007313, 3, [(2, 4), (43, 1), (148953499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_148953499
  · decide +kernel

theorem prime_102480012737 : Nat.Prime 102480012737 := by
  apply nodeValid_prime [2, 27799, 57601] ⟨102480012737, 3, [(2, 6), (27799, 1), (57601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_27799
    · exact prime_57601
  · decide +kernel

theorem prime_102758358949 : Nat.Prime 102758358949 := by
  apply nodeValid_prime [2, 3, 7, 1223313797] ⟨102758358949, 14, [(2, 2), (3, 1), (7, 1), (1223313797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1223313797
  · decide +kernel

theorem prime_102758360899 : Nat.Prime 102758360899 := by
  apply nodeValid_prime [2, 3, 17126393483] ⟨102758360899, 2, [(2, 1), (3, 1), (17126393483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17126393483
  · decide +kernel

theorem prime_102758380223 : Nat.Prime 102758380223 := by
  apply nodeValid_prime [2, 51379190111] ⟨102758380223, 5, [(2, 1), (51379190111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_51379190111
  · decide +kernel

theorem prime_103037261233 : Nat.Prime 103037261233 := by
  apply nodeValid_prime [2, 3, 29, 2552449] ⟨103037261233, 5, [(2, 4), (3, 1), (29, 2), (2552449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2552449
  · decide +kernel

theorem prime_103037261347 : Nat.Prime 103037261347 := by
  apply nodeValid_prime [2, 3, 5724292297] ⟨103037261347, 2, [(2, 1), (3, 2), (5724292297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5724292297
  · decide +kernel

theorem prime_103037261381 : Nat.Prime 103037261381 := by
  apply nodeValid_prime [2, 5, 131, 39327199] ⟨103037261381, 2, [(2, 2), (5, 1), (131, 1), (39327199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_39327199
  · decide +kernel

theorem prime_103316648791 : Nat.Prime 103316648791 := by
  apply nodeValid_prime [2, 3, 5, 47, 73274219] ⟨103316648791, 3, [(2, 1), (3, 1), (5, 1), (47, 1), (73274219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_73274219
  · decide +kernel

theorem prime_103316650897 : Nat.Prime 103316650897 := by
  apply nodeValid_prime [2, 3, 2152430227] ⟨103316650897, 5, [(2, 4), (3, 1), (2152430227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2152430227
  · decide +kernel

theorem prime_103316654611 : Nat.Prime 103316654611 := by
  apply nodeValid_prime [2, 3, 5, 13, 31, 751, 3793] ⟨103316654611, 2, [(2, 1), (3, 2), (5, 1), (13, 1), (31, 1), (751, 1), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_751
    · exact prime_3793
  · decide +kernel

theorem prime_103596564607 : Nat.Prime 103596564607 := by
  apply nodeValid_prime [2, 3, 73, 349, 409, 1657] ⟨103596564607, 3, [(2, 1), (3, 1), (73, 1), (349, 1), (409, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_349
    · exact prime_409
    · exact prime_1657
  · decide +kernel

theorem prime_103596568463 : Nat.Prime 103596568463 := by
  apply nodeValid_prime [2, 673, 76966247] ⟨103596568463, 5, [(2, 1), (673, 1), (76966247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_673
    · exact prime_76966247
  · decide +kernel

theorem prime_103596568531 : Nat.Prime 103596568531 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 37947461] ⟨103596568531, 26, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (37947461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_37947461
  · decide +kernel

theorem prime_103876988713 : Nat.Prime 103876988713 := by
  apply nodeValid_prime [2, 3, 7, 29, 47, 453643] ⟨103876988713, 5, [(2, 3), (3, 1), (7, 1), (29, 1), (47, 1), (453643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_47
    · exact prime_453643
  · decide +kernel

theorem prime_103877006221 : Nat.Prime 103877006221 := by
  apply nodeValid_prime [2, 3, 5, 13, 1759, 25237] ⟨103877006221, 2, [(2, 2), (3, 2), (5, 1), (13, 1), (1759, 1), (25237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1759
    · exact prime_25237
  · decide +kernel

theorem prime_103877007061 : Nat.Prime 103877007061 := by
  apply nodeValid_prime [2, 3, 5, 17, 97, 1049899] ⟨103877007061, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (97, 1), (1049899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_97
    · exact prime_1049899
  · decide +kernel

theorem prime_104157926123 : Nat.Prime 104157926123 := by
  apply nodeValid_prime [2, 139, 12671, 29569] ⟨104157926123, 2, [(2, 1), (139, 1), (12671, 1), (29569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_12671
    · exact prime_29569
  · decide +kernel

theorem prime_104157940409 : Nat.Prime 104157940409 := by
  apply nodeValid_prime [2, 211, 61704941] ⟨104157940409, 3, [(2, 3), (211, 1), (61704941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_61704941
  · decide +kernel

theorem prime_104157940559 : Nat.Prime 104157940559 := by
  apply nodeValid_prime [2, 7, 7439852897] ⟨104157940559, 7, [(2, 1), (7, 1), (7439852897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7439852897
  · decide +kernel

theorem prime_104439373111 : Nat.Prime 104439373111 := by
  apply nodeValid_prime [2, 3, 5, 149, 2596057] ⟨104439373111, 3, [(2, 1), (3, 3), (5, 1), (149, 1), (2596057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
    · exact prime_2596057
  · decide +kernel

theorem prime_104439373351 : Nat.Prime 104439373351 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 3150509] ⟨104439373351, 3, [(2, 1), (3, 1), (5, 2), (13, 1), (17, 1), (3150509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_3150509
  · decide +kernel

theorem prime_104439375871 : Nat.Prime 104439375871 := by
  apply nodeValid_prime [2, 3, 5, 45329, 76801] ⟨104439375871, 3, [(2, 1), (3, 1), (5, 1), (45329, 1), (76801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_45329
    · exact prime_76801
  · decide +kernel

theorem prime_104721346259 : Nat.Prime 104721346259 := by
  apply nodeValid_prime [2, 52360673129] ⟨104721346259, 2, [(2, 1), (52360673129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_52360673129
  · decide +kernel

theorem prime_104721346393 : Nat.Prime 104721346393 := by
  apply nodeValid_prime [2, 3, 13, 257, 461, 2833] ⟨104721346393, 5, [(2, 3), (3, 1), (13, 1), (257, 1), (461, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_257
    · exact prime_461
    · exact prime_2833
  · decide +kernel

theorem prime_104721347141 : Nat.Prime 104721347141 := by
  apply nodeValid_prime [2, 5, 4967, 1054171] ⟨104721347141, 2, [(2, 2), (5, 1), (4967, 1), (1054171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4967
    · exact prime_1054171
  · decide +kernel

theorem prime_105003836137 : Nat.Prime 105003836137 := by
  apply nodeValid_prime [2, 3, 1091, 5501] ⟨105003836137, 10, [(2, 3), (3, 7), (1091, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
    · exact prime_5501
  · decide +kernel

theorem prime_105003845371 : Nat.Prime 105003845371 := by
  apply nodeValid_prime [2, 3, 5, 3313, 13043] ⟨105003845371, 10, [(2, 1), (3, 5), (5, 1), (3313, 1), (13043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3313
    · exact prime_13043
  · decide +kernel

theorem prime_105003845861 : Nat.Prime 105003845861 := by
  apply nodeValid_prime [2, 5, 37, 47, 67, 45061] ⟨105003845861, 2, [(2, 2), (5, 1), (37, 1), (47, 1), (67, 1), (45061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_47
    · exact prime_67
    · exact prime_45061
  · decide +kernel

theorem prime_105286822507 : Nat.Prime 105286822507 := by
  apply nodeValid_prime [2, 3, 5849267917] ⟨105286822507, 3, [(2, 1), (3, 2), (5849267917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5849267917
  · decide +kernel

theorem prime_105286822559 : Nat.Prime 105286822559 := by
  apply nodeValid_prime [2, 37633, 1398863] ⟨105286822559, 7, [(2, 1), (37633, 1), (1398863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37633
    · exact prime_1398863
  · decide +kernel

theorem prime_105286840931 : Nat.Prime 105286840931 := by
  apply nodeValid_prime [2, 5, 41, 7057, 36389] ⟨105286840931, 2, [(2, 1), (5, 1), (41, 1), (7057, 1), (36389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_7057
    · exact prime_36389
  · decide +kernel

theorem prime_105570353479 : Nat.Prime 105570353479 := by
  apply nodeValid_prime [2, 3, 3659, 4808707] ⟨105570353479, 21, [(2, 1), (3, 1), (3659, 1), (4808707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3659
    · exact prime_4808707
  · decide +kernel

theorem prime_105570354031 : Nat.Prime 105570354031 := by
  apply nodeValid_prime [2, 3, 5, 101, 1051, 33151] ⟨105570354031, 3, [(2, 1), (3, 1), (5, 1), (101, 1), (1051, 1), (33151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_1051
    · exact prime_33151
  · decide +kernel

theorem prime_105570361867 : Nat.Prime 105570361867 := by
  apply nodeValid_prime [2, 3, 41131, 427781] ⟨105570361867, 3, [(2, 1), (3, 1), (41131, 1), (427781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41131
    · exact prime_427781
  · decide +kernel

theorem prime_105854393191 : Nat.Prime 105854393191 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 4021, 9643] ⟨105854393191, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (4021, 1), (9643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_4021
    · exact prime_9643
  · decide +kernel

theorem prime_105854394193 : Nat.Prime 105854394193 := by
  apply nodeValid_prime [2, 3, 2205299879] ⟨105854394193, 10, [(2, 4), (3, 1), (2205299879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2205299879
  · decide +kernel

theorem prime_105854404099 : Nat.Prime 105854404099 := by
  apply nodeValid_prime [2, 3, 109, 161856887] ⟨105854404099, 2, [(2, 1), (3, 1), (109, 1), (161856887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_161856887
  · decide +kernel

theorem prime_106138955309 : Nat.Prime 106138955309 := by
  apply nodeValid_prime [2, 31, 181, 257, 18401] ⟨106138955309, 2, [(2, 2), (31, 1), (181, 1), (257, 1), (18401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_181
    · exact prime_257
    · exact prime_18401
  · decide +kernel

theorem prime_106138955719 : Nat.Prime 106138955719 := by
  apply nodeValid_prime [2, 3, 53, 4120621] ⟨106138955719, 6, [(2, 1), (3, 5), (53, 1), (4120621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_4120621
  · decide +kernel

theorem prime_106138963993 : Nat.Prime 106138963993 := by
  apply nodeValid_prime [2, 3, 26731, 165443] ⟨106138963993, 5, [(2, 3), (3, 1), (26731, 1), (165443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26731
    · exact prime_165443
  · decide +kernel

theorem prime_106424025377 : Nat.Prime 106424025377 := by
  apply nodeValid_prime [2, 41, 81115873] ⟨106424025377, 3, [(2, 5), (41, 1), (81115873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_81115873
  · decide +kernel

theorem prime_106424025833 : Nat.Prime 106424025833 := by
  apply nodeValid_prime [2, 59, 67, 223, 15091] ⟨106424025833, 3, [(2, 3), (59, 1), (67, 1), (223, 1), (15091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_67
    · exact prime_223
    · exact prime_15091
  · decide +kernel

theorem prime_106424038681 : Nat.Prime 106424038681 := by
  apply nodeValid_prime [2, 3, 5, 19801, 44789] ⟨106424038681, 38, [(2, 3), (3, 1), (5, 1), (19801, 1), (44789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19801
    · exact prime_44789
  · decide +kernel

theorem prime_106709632079 : Nat.Prime 106709632079 := by
  apply nodeValid_prime [2, 7, 7622116577] ⟨106709632079, 7, [(2, 1), (7, 1), (7622116577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7622116577
  · decide +kernel

theorem prime_106709638969 : Nat.Prime 106709638969 := by
  apply nodeValid_prime [2, 3, 1482078319] ⟨106709638969, 7, [(2, 3), (3, 2), (1482078319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1482078319
  · decide +kernel

theorem prime_106709640439 : Nat.Prime 106709640439 := by
  apply nodeValid_prime [2, 3, 17784940073] ⟨106709640439, 19, [(2, 1), (3, 1), (17784940073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17784940073
  · decide +kernel

theorem prime_106995733973 : Nat.Prime 106995733973 := by
  apply nodeValid_prime [2, 29, 922377017] ⟨106995733973, 2, [(2, 2), (29, 1), (922377017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_922377017
  · decide +kernel

theorem prime_106995736163 : Nat.Prime 106995736163 := by
  apply nodeValid_prime [2, 7, 43, 67, 2652743] ⟨106995736163, 2, [(2, 1), (7, 1), (43, 1), (67, 1), (2652743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_67
    · exact prime_2652743
  · decide +kernel

theorem prime_106995746959 : Nat.Prime 106995746959 := by
  apply nodeValid_prime [2, 3, 3881, 4594853] ⟨106995746959, 3, [(2, 1), (3, 1), (3881, 1), (4594853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3881
    · exact prime_4594853
  · decide +kernel

theorem prime_107282380897 : Nat.Prime 107282380897 := by
  apply nodeValid_prime [2, 3, 17, 37, 592223] ⟨107282380897, 7, [(2, 5), (3, 2), (17, 1), (37, 1), (592223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_592223
  · decide +kernel

theorem prime_107282394521 : Nat.Prime 107282394521 := by
  apply nodeValid_prime [2, 5, 7, 1777, 215617] ⟨107282394521, 3, [(2, 3), (5, 1), (7, 1), (1777, 1), (215617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1777
    · exact prime_215617
  · decide +kernel

theorem prime_107282394553 : Nat.Prime 107282394553 := by
  apply nodeValid_prime [2, 3, 4470099773] ⟨107282394553, 5, [(2, 3), (3, 1), (4470099773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4470099773
  · decide +kernel

theorem prime_107569532093 : Nat.Prime 107569532093 := by
  apply nodeValid_prime [2, 11, 89, 229, 119953] ⟨107569532093, 2, [(2, 2), (11, 1), (89, 1), (229, 1), (119953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
    · exact prime_229
    · exact prime_119953
  · decide +kernel

theorem prime_107569533473 : Nat.Prime 107569533473 := by
  apply nodeValid_prime [2, 17, 257, 461, 1669] ⟨107569533473, 3, [(2, 5), (17, 1), (257, 1), (461, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_257
    · exact prime_461
    · exact prime_1669
  · decide +kernel

theorem prime_107569535677 : Nat.Prime 107569535677 := by
  apply nodeValid_prime [2, 3, 37, 271, 893999] ⟨107569535677, 5, [(2, 2), (3, 1), (37, 1), (271, 1), (893999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_271
    · exact prime_893999
  · decide +kernel

theorem prime_107857175213 : Nat.Prime 107857175213 := by
  apply nodeValid_prime [2, 617, 43702259] ⟨107857175213, 2, [(2, 2), (617, 1), (43702259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_617
    · exact prime_43702259
  · decide +kernel

theorem prime_107857175627 : Nat.Prime 107857175627 := by
  apply nodeValid_prime [2, 19, 2838346727] ⟨107857175627, 2, [(2, 1), (19, 1), (2838346727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2838346727
  · decide +kernel

theorem prime_107857203089 : Nat.Prime 107857203089 := by
  apply nodeValid_prime [2, 6741075193] ⟨107857203089, 3, [(2, 4), (6741075193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6741075193
  · decide +kernel

theorem prime_108145391261 : Nat.Prime 108145391261 := by
  apply nodeValid_prime [2, 5, 2909, 1858807] ⟨108145391261, 2, [(2, 2), (5, 1), (2909, 1), (1858807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2909
    · exact prime_1858807
  · decide +kernel

theorem prime_108145411559 : Nat.Prime 108145411559 := by
  apply nodeValid_prime [2, 54072705779] ⟨108145411559, 11, [(2, 1), (54072705779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54072705779
  · decide +kernel

theorem prime_108145414217 : Nat.Prime 108145414217 := by
  apply nodeValid_prime [2, 7, 2063, 936097] ⟨108145414217, 3, [(2, 3), (7, 1), (2063, 1), (936097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2063
    · exact prime_936097
  · decide +kernel

theorem prime_108434101879 : Nat.Prime 108434101879 := by
  apply nodeValid_prime [2, 3, 36721, 164051] ⟨108434101879, 3, [(2, 1), (3, 2), (36721, 1), (164051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36721
    · exact prime_164051
  · decide +kernel

theorem prime_108434111537 : Nat.Prime 108434111537 := by
  apply nodeValid_prime [2, 2719, 2492509] ⟨108434111537, 3, [(2, 4), (2719, 1), (2492509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2719
    · exact prime_2492509
  · decide +kernel

theorem prime_108434112341 : Nat.Prime 108434112341 := by
  apply nodeValid_prime [2, 5, 541, 10021637] ⟨108434112341, 2, [(2, 2), (5, 1), (541, 1), (10021637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_541
    · exact prime_10021637
  · decide +kernel

theorem prime_108723320471 : Nat.Prime 108723320471 := by
  apply nodeValid_prime [2, 5, 23, 472710089] ⟨108723320471, 23, [(2, 1), (5, 1), (23, 1), (472710089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_472710089
  · decide +kernel

theorem prime_108723320987 : Nat.Prime 108723320987 := by
  apply nodeValid_prime [2, 7, 29, 4999, 53569] ⟨108723320987, 2, [(2, 1), (7, 1), (29, 1), (4999, 1), (53569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_4999
    · exact prime_53569
  · decide +kernel

theorem prime_108723333991 : Nat.Prime 108723333991 := by
  apply nodeValid_prime [2, 3, 5, 449, 8071517] ⟨108723333991, 3, [(2, 1), (3, 1), (5, 1), (449, 1), (8071517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_449
    · exact prime_8071517
  · decide +kernel

end Sude.Lucas.Generated
