import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_151 : Nat.Prime 151 := by
  apply nodeValid_prime [2, 3, 5] ⟨151, 6, [(2, 1), (3, 1), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_197 : Nat.Prime 197 := by
  apply nodeValid_prime [2, 7] ⟨197, 2, [(2, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7
  · decide +kernel

theorem prime_211 : Nat.Prime 211 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨211, 2, [(2, 1), (3, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_227 : Nat.Prime 227 := by
  apply nodeValid_prime [2, 113] ⟨227, 2, [(2, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_113
  · decide +kernel

theorem prime_229 : Nat.Prime 229 := by
  apply nodeValid_prime [2, 3, 19] ⟨229, 6, [(2, 2), (3, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_293 : Nat.Prime 293 := by
  apply nodeValid_prime [2, 73] ⟨293, 2, [(2, 2), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73
  · decide +kernel

theorem prime_307 : Nat.Prime 307 := by
  apply nodeValid_prime [2, 3, 17] ⟨307, 5, [(2, 1), (3, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_331 : Nat.Prime 331 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨331, 3, [(2, 1), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_367 : Nat.Prime 367 := by
  apply nodeValid_prime [2, 3, 61] ⟨367, 6, [(2, 1), (3, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel

theorem prime_409 : Nat.Prime 409 := by
  apply nodeValid_prime [2, 3, 17] ⟨409, 21, [(2, 3), (3, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_419 : Nat.Prime 419 := by
  apply nodeValid_prime [2, 11, 19] ⟨419, 2, [(2, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_421 : Nat.Prime 421 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨421, 2, [(2, 2), (3, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_431 : Nat.Prime 431 := by
  apply nodeValid_prime [2, 5, 43] ⟨431, 7, [(2, 1), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_467 : Nat.Prime 467 := by
  apply nodeValid_prime [2, 233] ⟨467, 2, [(2, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_233
  · decide +kernel

theorem prime_659 : Nat.Prime 659 := by
  apply nodeValid_prime [2, 7, 47] ⟨659, 2, [(2, 1), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_743 : Nat.Prime 743 := by
  apply nodeValid_prime [2, 7, 53] ⟨743, 5, [(2, 1), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_787 : Nat.Prime 787 := by
  apply nodeValid_prime [2, 3, 131] ⟨787, 2, [(2, 1), (3, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_797 : Nat.Prime 797 := by
  apply nodeValid_prime [2, 199] ⟨797, 2, [(2, 2), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_199
  · decide +kernel

theorem prime_829 : Nat.Prime 829 := by
  apply nodeValid_prime [2, 3, 23] ⟨829, 2, [(2, 2), (3, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_859 : Nat.Prime 859 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨859, 2, [(2, 1), (3, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_887 : Nat.Prime 887 := by
  apply nodeValid_prime [2, 443] ⟨887, 5, [(2, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_443
  · decide +kernel

theorem prime_907 : Nat.Prime 907 := by
  apply nodeValid_prime [2, 3, 151] ⟨907, 2, [(2, 1), (3, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
  · decide +kernel

theorem prime_937 : Nat.Prime 937 := by
  apply nodeValid_prime [2, 3, 13] ⟨937, 5, [(2, 3), (3, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_953 : Nat.Prime 953 := by
  apply nodeValid_prime [2, 7, 17] ⟨953, 3, [(2, 3), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_971 : Nat.Prime 971 := by
  apply nodeValid_prime [2, 5, 97] ⟨971, 6, [(2, 1), (5, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_1031 : Nat.Prime 1031 := by
  apply nodeValid_prime [2, 5, 103] ⟨1031, 14, [(2, 1), (5, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_1033 : Nat.Prime 1033 := by
  apply nodeValid_prime [2, 3, 43] ⟨1033, 5, [(2, 3), (3, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_1061 : Nat.Prime 1061 := by
  apply nodeValid_prime [2, 5, 53] ⟨1061, 2, [(2, 2), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_1069 : Nat.Prime 1069 := by
  apply nodeValid_prime [2, 3, 89] ⟨1069, 6, [(2, 2), (3, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_1117 : Nat.Prime 1117 := by
  apply nodeValid_prime [2, 3, 31] ⟨1117, 2, [(2, 2), (3, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_1151 : Nat.Prime 1151 := by
  apply nodeValid_prime [2, 5, 23] ⟨1151, 17, [(2, 1), (5, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_1193 : Nat.Prime 1193 := by
  apply nodeValid_prime [2, 149] ⟨1193, 3, [(2, 3), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_149
  · decide +kernel

theorem prime_1231 : Nat.Prime 1231 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨1231, 3, [(2, 1), (3, 1), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_1279 : Nat.Prime 1279 := by
  apply nodeValid_prime [2, 3, 71] ⟨1279, 3, [(2, 1), (3, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_1283 : Nat.Prime 1283 := by
  apply nodeValid_prime [2, 641] ⟨1283, 2, [(2, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_641
  · decide +kernel

theorem prime_1291 : Nat.Prime 1291 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨1291, 2, [(2, 1), (3, 1), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_1361 : Nat.Prime 1361 := by
  apply nodeValid_prime [2, 5, 17] ⟨1361, 3, [(2, 4), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_1531 : Nat.Prime 1531 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨1531, 2, [(2, 1), (3, 2), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_1579 : Nat.Prime 1579 := by
  apply nodeValid_prime [2, 3, 263] ⟨1579, 3, [(2, 1), (3, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
  · decide +kernel

theorem prime_1613 : Nat.Prime 1613 := by
  apply nodeValid_prime [2, 13, 31] ⟨1613, 3, [(2, 2), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_1667 : Nat.Prime 1667 := by
  apply nodeValid_prime [2, 7, 17] ⟨1667, 2, [(2, 1), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_1823 : Nat.Prime 1823 := by
  apply nodeValid_prime [2, 911] ⟨1823, 5, [(2, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_911
  · decide +kernel

theorem prime_1847 : Nat.Prime 1847 := by
  apply nodeValid_prime [2, 13, 71] ⟨1847, 5, [(2, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_1907 : Nat.Prime 1907 := by
  apply nodeValid_prime [2, 953] ⟨1907, 2, [(2, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_953
  · decide +kernel

theorem prime_1979 : Nat.Prime 1979 := by
  apply nodeValid_prime [2, 23, 43] ⟨1979, 2, [(2, 1), (23, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
  · decide +kernel

theorem prime_2069 : Nat.Prime 2069 := by
  apply nodeValid_prime [2, 11, 47] ⟨2069, 2, [(2, 2), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_2083 : Nat.Prime 2083 := by
  apply nodeValid_prime [2, 3, 347] ⟨2083, 2, [(2, 1), (3, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
  · decide +kernel

theorem prime_2153 : Nat.Prime 2153 := by
  apply nodeValid_prime [2, 269] ⟨2153, 3, [(2, 3), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_269
  · decide +kernel

theorem prime_2281 : Nat.Prime 2281 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨2281, 7, [(2, 3), (3, 1), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_2293 : Nat.Prime 2293 := by
  apply nodeValid_prime [2, 3, 191] ⟨2293, 2, [(2, 2), (3, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
  · decide +kernel

theorem prime_2351 : Nat.Prime 2351 := by
  apply nodeValid_prime [2, 5, 47] ⟨2351, 13, [(2, 1), (5, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_2411 : Nat.Prime 2411 := by
  apply nodeValid_prime [2, 5, 241] ⟨2411, 6, [(2, 1), (5, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_2621 : Nat.Prime 2621 := by
  apply nodeValid_prime [2, 5, 131] ⟨2621, 2, [(2, 2), (5, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
  · decide +kernel

theorem prime_2741 : Nat.Prime 2741 := by
  apply nodeValid_prime [2, 5, 137] ⟨2741, 2, [(2, 2), (5, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_2837 : Nat.Prime 2837 := by
  apply nodeValid_prime [2, 709] ⟨2837, 2, [(2, 2), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_709
  · decide +kernel

theorem prime_2917 : Nat.Prime 2917 := by
  apply nodeValid_prime [2, 3] ⟨2917, 5, [(2, 2), (3, 6)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_3691 : Nat.Prime 3691 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨3691, 2, [(2, 1), (3, 2), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_3943 : Nat.Prime 3943 := by
  apply nodeValid_prime [2, 3, 73] ⟨3943, 3, [(2, 1), (3, 3), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_4673 : Nat.Prime 4673 := by
  apply nodeValid_prime [2, 73] ⟨4673, 3, [(2, 6), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73
  · decide +kernel

theorem prime_4703 : Nat.Prime 4703 := by
  apply nodeValid_prime [2, 2351] ⟨4703, 5, [(2, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2351
  · decide +kernel

theorem prime_4793 : Nat.Prime 4793 := by
  apply nodeValid_prime [2, 599] ⟨4793, 3, [(2, 3), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_599
  · decide +kernel

theorem prime_5323 : Nat.Prime 5323 := by
  apply nodeValid_prime [2, 3, 887] ⟨5323, 5, [(2, 1), (3, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_887
  · decide +kernel

theorem prime_5443 : Nat.Prime 5443 := by
  apply nodeValid_prime [2, 3, 907] ⟨5443, 2, [(2, 1), (3, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
  · decide +kernel

theorem prime_5477 : Nat.Prime 5477 := by
  apply nodeValid_prime [2, 37] ⟨5477, 2, [(2, 2), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37
  · decide +kernel

theorem prime_5521 : Nat.Prime 5521 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨5521, 11, [(2, 4), (3, 1), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_5743 : Nat.Prime 5743 := by
  apply nodeValid_prime [2, 3, 11, 29] ⟨5743, 10, [(2, 1), (3, 2), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_5821 : Nat.Prime 5821 := by
  apply nodeValid_prime [2, 3, 5, 97] ⟨5821, 6, [(2, 2), (3, 1), (5, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_5867 : Nat.Prime 5867 := by
  apply nodeValid_prime [2, 7, 419] ⟨5867, 5, [(2, 1), (7, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_419
  · decide +kernel

theorem prime_6317 : Nat.Prime 6317 := by
  apply nodeValid_prime [2, 1579] ⟨6317, 2, [(2, 2), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1579
  · decide +kernel

theorem prime_7151 : Nat.Prime 7151 := by
  apply nodeValid_prime [2, 5, 11, 13] ⟨7151, 7, [(2, 1), (5, 2), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_7393 : Nat.Prime 7393 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨7393, 5, [(2, 5), (3, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_7669 : Nat.Prime 7669 := by
  apply nodeValid_prime [2, 3, 71] ⟨7669, 2, [(2, 2), (3, 3), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_7681 : Nat.Prime 7681 := by
  apply nodeValid_prime [2, 3, 5] ⟨7681, 17, [(2, 9), (3, 1), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_8443 : Nat.Prime 8443 := by
  apply nodeValid_prime [2, 3, 7, 67] ⟨8443, 2, [(2, 1), (3, 2), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_8597 : Nat.Prime 8597 := by
  apply nodeValid_prime [2, 7, 307] ⟨8597, 2, [(2, 2), (7, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_307
  · decide +kernel

theorem prime_8863 : Nat.Prime 8863 := by
  apply nodeValid_prime [2, 3, 7, 211] ⟨8863, 3, [(2, 1), (3, 1), (7, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_211
  · decide +kernel

theorem prime_12547 : Nat.Prime 12547 := by
  apply nodeValid_prime [2, 3, 17, 41] ⟨12547, 2, [(2, 1), (3, 2), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_12911 : Nat.Prime 12911 := by
  apply nodeValid_prime [2, 5, 1291] ⟨12911, 23, [(2, 1), (5, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1291
  · decide +kernel

theorem prime_13759 : Nat.Prime 13759 := by
  apply nodeValid_prime [2, 3, 2293] ⟨13759, 6, [(2, 1), (3, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2293
  · decide +kernel

theorem prime_14813 : Nat.Prime 14813 := by
  apply nodeValid_prime [2, 7, 23] ⟨14813, 2, [(2, 2), (7, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_15727 : Nat.Prime 15727 := by
  apply nodeValid_prime [2, 3, 2621] ⟨15727, 3, [(2, 1), (3, 1), (2621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2621
  · decide +kernel

theorem prime_15739 : Nat.Prime 15739 := by
  apply nodeValid_prime [2, 3, 43, 61] ⟨15739, 2, [(2, 1), (3, 1), (43, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_61
  · decide +kernel

theorem prime_15773 : Nat.Prime 15773 := by
  apply nodeValid_prime [2, 3943] ⟨15773, 2, [(2, 2), (3943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3943
  · decide +kernel

theorem prime_17707 : Nat.Prime 17707 := by
  apply nodeValid_prime [2, 3, 13, 227] ⟨17707, 3, [(2, 1), (3, 1), (13, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_227
  · decide +kernel

theorem prime_20143 : Nat.Prime 20143 := by
  apply nodeValid_prime [2, 3, 373] ⟨20143, 5, [(2, 1), (3, 3), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
  · decide +kernel

theorem prime_21089 : Nat.Prime 21089 := by
  apply nodeValid_prime [2, 659] ⟨21089, 3, [(2, 5), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_659
  · decide +kernel

theorem prime_21773 : Nat.Prime 21773 := by
  apply nodeValid_prime [2, 5443] ⟨21773, 2, [(2, 2), (5443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5443
  · decide +kernel

theorem prime_21929 : Nat.Prime 21929 := by
  apply nodeValid_prime [2, 2741] ⟨21929, 3, [(2, 3), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2741
  · decide +kernel

theorem prime_22973 : Nat.Prime 22973 := by
  apply nodeValid_prime [2, 5743] ⟨22973, 2, [(2, 2), (5743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5743
  · decide +kernel

theorem prime_23563 : Nat.Prime 23563 := by
  apply nodeValid_prime [2, 3, 7, 11, 17] ⟨23563, 2, [(2, 1), (3, 2), (7, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_24179 : Nat.Prime 24179 := by
  apply nodeValid_prime [2, 7, 11, 157] ⟨24179, 2, [(2, 1), (7, 1), (11, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_157
  · decide +kernel

theorem prime_26417 : Nat.Prime 26417 := by
  apply nodeValid_prime [2, 13, 127] ⟨26417, 3, [(2, 4), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_27143 : Nat.Prime 27143 := by
  apply nodeValid_prime [2, 41, 331] ⟨27143, 5, [(2, 1), (41, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_331
  · decide +kernel

theorem prime_28219 : Nat.Prime 28219 := by
  apply nodeValid_prime [2, 3, 4703] ⟨28219, 3, [(2, 1), (3, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4703
  · decide +kernel

theorem prime_29201 : Nat.Prime 29201 := by
  apply nodeValid_prime [2, 5, 73] ⟨29201, 3, [(2, 4), (5, 2), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_31547 : Nat.Prime 31547 := by
  apply nodeValid_prime [2, 15773] ⟨31547, 2, [(2, 1), (15773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15773
  · decide +kernel

theorem prime_33773 : Nat.Prime 33773 := by
  apply nodeValid_prime [2, 8443] ⟨33773, 2, [(2, 2), (8443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8443
  · decide +kernel

theorem prime_37591 : Nat.Prime 37591 := by
  apply nodeValid_prime [2, 3, 5, 7, 179] ⟨37591, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_179
  · decide +kernel

theorem prime_42019 : Nat.Prime 42019 := by
  apply nodeValid_prime [2, 3, 47, 149] ⟨42019, 2, [(2, 1), (3, 1), (47, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_149
  · decide +kernel

theorem prime_46337 : Nat.Prime 46337 := by
  apply nodeValid_prime [2, 181] ⟨46337, 3, [(2, 8), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_181
  · decide +kernel

theorem prime_54287 : Nat.Prime 54287 := by
  apply nodeValid_prime [2, 27143] ⟨54287, 5, [(2, 1), (27143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27143
  · decide +kernel

theorem prime_54377 : Nat.Prime 54377 := by
  apply nodeValid_prime [2, 7, 971] ⟨54377, 5, [(2, 3), (7, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_971
  · decide +kernel

theorem prime_56897 : Nat.Prime 56897 := by
  apply nodeValid_prime [2, 7, 127] ⟨56897, 5, [(2, 6), (7, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_56951 : Nat.Prime 56951 := by
  apply nodeValid_prime [2, 5, 17, 67] ⟨56951, 13, [(2, 1), (5, 2), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_58403 : Nat.Prime 58403 := by
  apply nodeValid_prime [2, 29201] ⟨58403, 2, [(2, 1), (29201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29201
  · decide +kernel

theorem prime_61583 : Nat.Prime 61583 := by
  apply nodeValid_prime [2, 41, 751] ⟨61583, 5, [(2, 1), (41, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_751
  · decide +kernel

theorem prime_67547 : Nat.Prime 67547 := by
  apply nodeValid_prime [2, 33773] ⟨67547, 2, [(2, 1), (33773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33773
  · decide +kernel

theorem prime_69067 : Nat.Prime 69067 := by
  apply nodeValid_prime [2, 3, 1279] ⟨69067, 2, [(2, 1), (3, 3), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
  · decide +kernel

theorem prime_73361 : Nat.Prime 73361 := by
  apply nodeValid_prime [2, 5, 7, 131] ⟨73361, 11, [(2, 4), (5, 1), (7, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_131
  · decide +kernel

theorem prime_79873 : Nat.Prime 79873 := by
  apply nodeValid_prime [2, 3, 13] ⟨79873, 7, [(2, 11), (3, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_82657 : Nat.Prime 82657 := by
  apply nodeValid_prime [2, 3, 7, 41] ⟨82657, 10, [(2, 5), (3, 2), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_86311 : Nat.Prime 86311 := by
  apply nodeValid_prime [2, 3, 5, 7, 137] ⟨86311, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_94771 : Nat.Prime 94771 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨94771, 10, [(2, 1), (3, 6), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_97813 : Nat.Prime 97813 := by
  apply nodeValid_prime [2, 3, 11, 13, 19] ⟨97813, 2, [(2, 2), (3, 2), (11, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_104281 : Nat.Prime 104281 := by
  apply nodeValid_prime [2, 3, 5, 11, 79] ⟨104281, 26, [(2, 3), (3, 1), (5, 1), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_106357 : Nat.Prime 106357 := by
  apply nodeValid_prime [2, 3, 8863] ⟨106357, 2, [(2, 2), (3, 1), (8863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8863
  · decide +kernel

theorem prime_111997 : Nat.Prime 111997 := by
  apply nodeValid_prime [2, 3, 17, 61] ⟨111997, 2, [(2, 2), (3, 3), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_112877 : Nat.Prime 112877 := by
  apply nodeValid_prime [2, 28219] ⟨112877, 2, [(2, 2), (28219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28219
  · decide +kernel

theorem prime_113903 : Nat.Prime 113903 := by
  apply nodeValid_prime [2, 56951] ⟨113903, 5, [(2, 1), (56951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56951
  · decide +kernel

theorem prime_142657 : Nat.Prime 142657 := by
  apply nodeValid_prime [2, 3, 743] ⟨142657, 10, [(2, 6), (3, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_743
  · decide +kernel

theorem prime_151241 : Nat.Prime 151241 := by
  apply nodeValid_prime [2, 5, 19, 199] ⟨151241, 7, [(2, 3), (5, 1), (19, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_199
  · decide +kernel

theorem prime_200041 : Nat.Prime 200041 := by
  apply nodeValid_prime [2, 3, 5, 1667] ⟨200041, 11, [(2, 3), (3, 1), (5, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1667
  · decide +kernel

theorem prime_216037 : Nat.Prime 216037 := by
  apply nodeValid_prime [2, 3, 17, 353] ⟨216037, 2, [(2, 2), (3, 2), (17, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_353
  · decide +kernel

theorem prime_257437 : Nat.Prime 257437 := by
  apply nodeValid_prime [2, 3, 7151] ⟨257437, 2, [(2, 2), (3, 2), (7151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7151
  · decide +kernel

theorem prime_272959 : Nat.Prime 272959 := by
  apply nodeValid_prime [2, 3, 7, 67, 97] ⟨272959, 3, [(2, 1), (3, 1), (7, 1), (67, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
    · exact prime_97
  · decide +kernel

theorem prime_291089 : Nat.Prime 291089 := by
  apply nodeValid_prime [2, 7, 23, 113] ⟨291089, 11, [(2, 4), (7, 1), (23, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_113
  · decide +kernel

theorem prime_302483 : Nat.Prime 302483 := by
  apply nodeValid_prime [2, 151241] ⟨302483, 2, [(2, 1), (151241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_151241
  · decide +kernel

theorem prime_312551 : Nat.Prime 312551 := by
  apply nodeValid_prime [2, 5, 7, 19, 47] ⟨312551, 17, [(2, 1), (5, 2), (7, 1), (19, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_340801 : Nat.Prime 340801 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨340801, 11, [(2, 6), (3, 1), (5, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_352771 : Nat.Prime 352771 := by
  apply nodeValid_prime [2, 3, 5, 11, 1069] ⟨352771, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1069
  · decide +kernel

theorem prime_385631 : Nat.Prime 385631 := by
  apply nodeValid_prime [2, 5, 7, 787] ⟨385631, 7, [(2, 1), (5, 1), (7, 2), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_787
  · decide +kernel

theorem prime_411049 : Nat.Prime 411049 := by
  apply nodeValid_prime [2, 3, 11, 173] ⟨411049, 13, [(2, 3), (3, 3), (11, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_173
  · decide +kernel

theorem prime_604291 : Nat.Prime 604291 := by
  apply nodeValid_prime [2, 3, 5, 20143] ⟨604291, 2, [(2, 1), (3, 1), (5, 1), (20143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20143
  · decide +kernel

theorem prime_723409 : Nat.Prime 723409 := by
  apply nodeValid_prime [2, 3, 7, 2153] ⟨723409, 13, [(2, 4), (3, 1), (7, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2153
  · decide +kernel

theorem prime_848269 : Nat.Prime 848269 := by
  apply nodeValid_prime [2, 3, 23563] ⟨848269, 2, [(2, 2), (3, 2), (23563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23563
  · decide +kernel

theorem prime_903017 : Nat.Prime 903017 := by
  apply nodeValid_prime [2, 112877] ⟨903017, 3, [(2, 3), (112877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_112877
  · decide +kernel

theorem prime_1179419 : Nat.Prime 1179419 := by
  apply nodeValid_prime [2, 47, 12547] ⟨1179419, 2, [(2, 1), (47, 1), (12547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_12547
  · decide +kernel

theorem prime_1312393 : Nat.Prime 1312393 := by
  apply nodeValid_prime [2, 3, 149, 367] ⟨1312393, 5, [(2, 3), (3, 1), (149, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_367
  · decide +kernel

theorem prime_2485187 : Nat.Prime 2485187 := by
  apply nodeValid_prime [2, 11, 83, 1361] ⟨2485187, 2, [(2, 1), (11, 1), (83, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83
    · exact prime_1361
  · decide +kernel

theorem prime_2893637 : Nat.Prime 2893637 := by
  apply nodeValid_prime [2, 723409] ⟨2893637, 2, [(2, 2), (723409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_723409
  · decide +kernel

theorem prime_3072439 : Nat.Prime 3072439 := by
  apply nodeValid_prime [2, 3, 56897] ⟨3072439, 3, [(2, 1), (3, 3), (56897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56897
  · decide +kernel

theorem prime_3222833 : Nat.Prime 3222833 := by
  apply nodeValid_prime [2, 71, 2837] ⟨3222833, 3, [(2, 4), (71, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2837
  · decide +kernel

theorem prime_3891917 : Nat.Prime 3891917 := by
  apply nodeValid_prime [2, 7, 29, 4793] ⟨3891917, 2, [(2, 2), (7, 1), (29, 1), (4793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_4793
  · decide +kernel

theorem prime_4362763 : Nat.Prime 4362763 := by
  apply nodeValid_prime [2, 3, 197, 3691] ⟨4362763, 2, [(2, 1), (3, 1), (197, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_3691
  · decide +kernel

theorem prime_5986163 : Nat.Prime 5986163 := by
  apply nodeValid_prime [2, 7, 13, 31, 1061] ⟨5986163, 2, [(2, 1), (7, 1), (13, 1), (31, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_1061
  · decide +kernel

theorem prime_7457839 : Nat.Prime 7457839 := by
  apply nodeValid_prime [2, 3, 859, 1447] ⟨7457839, 6, [(2, 1), (3, 1), (859, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_859
    · exact prime_1447
  · decide +kernel

theorem prime_9043079 : Nat.Prime 9043079 := by
  apply nodeValid_prime [2, 11, 411049] ⟨9043079, 11, [(2, 1), (11, 1), (411049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_411049
  · decide +kernel

theorem prime_10842859 : Nat.Prime 10842859 := by
  apply nodeValid_prime [2, 3, 13, 46337] ⟨10842859, 2, [(2, 1), (3, 2), (13, 1), (46337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_46337
  · decide +kernel

theorem prime_11972327 : Nat.Prime 11972327 := by
  apply nodeValid_prime [2, 5986163] ⟨11972327, 5, [(2, 1), (5986163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5986163
  · decide +kernel

theorem prime_12289757 : Nat.Prime 12289757 := by
  apply nodeValid_prime [2, 3072439] ⟨12289757, 2, [(2, 2), (3072439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3072439
  · decide +kernel

theorem prime_14327627 : Nat.Prime 14327627 := by
  apply nodeValid_prime [2, 83, 86311] ⟨14327627, 2, [(2, 1), (83, 1), (86311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_86311
  · decide +kernel

theorem prime_20114557 : Nat.Prime 20114557 := by
  apply nodeValid_prime [2, 3, 7, 11, 1979] ⟨20114557, 2, [(2, 2), (3, 1), (7, 1), (11, 2), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1979
  · decide +kernel

theorem prime_26768719 : Nat.Prime 26768719 := by
  apply nodeValid_prime [2, 3, 373, 443] ⟨26768719, 3, [(2, 1), (3, 4), (373, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_443
  · decide +kernel

theorem prime_29831357 : Nat.Prime 29831357 := by
  apply nodeValid_prime [2, 7457839] ⟨29831357, 2, [(2, 2), (7457839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7457839
  · decide +kernel

theorem prime_32851391 : Nat.Prime 32851391 := by
  apply nodeValid_prime [2, 5, 11, 13, 22973] ⟨32851391, 29, [(2, 1), (5, 1), (11, 1), (13, 1), (22973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_22973
  · decide +kernel

theorem prime_33913069 : Nat.Prime 33913069 := by
  apply nodeValid_prime [2, 3, 7, 41, 43, 229] ⟨33913069, 6, [(2, 2), (3, 1), (7, 1), (41, 1), (43, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_43
    · exact prime_229
  · decide +kernel

theorem prime_36025217 : Nat.Prime 36025217 := by
  apply nodeValid_prime [2, 19, 14813] ⟨36025217, 3, [(2, 7), (19, 1), (14813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_14813
  · decide +kernel

theorem prime_62424797 : Nat.Prime 62424797 := by
  apply nodeValid_prime [2, 7, 41, 54377] ⟨62424797, 2, [(2, 2), (7, 1), (41, 1), (54377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_54377
  · decide +kernel

theorem prime_67599619 : Nat.Prime 67599619 := by
  apply nodeValid_prime [2, 3, 2411, 4673] ⟨67599619, 10, [(2, 1), (3, 1), (2411, 1), (4673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2411
    · exact prime_4673
  · decide +kernel

theorem prime_75853429 : Nat.Prime 75853429 := by
  apply nodeValid_prime [2, 3, 7, 903017] ⟨75853429, 6, [(2, 2), (3, 1), (7, 1), (903017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_903017
  · decide +kernel

theorem prime_107115373 : Nat.Prime 107115373 := by
  apply nodeValid_prime [2, 3, 7, 13, 173] ⟨107115373, 6, [(2, 2), (3, 5), (7, 2), (13, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_173
  · decide +kernel

theorem prime_199104877 : Nat.Prime 199104877 := by
  apply nodeValid_prime [2, 3, 19, 291089] ⟨199104877, 2, [(2, 2), (3, 2), (19, 1), (291089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_291089
  · decide +kernel

theorem prime_262336889 : Nat.Prime 262336889 := by
  apply nodeValid_prime [2, 11, 73, 97, 421] ⟨262336889, 3, [(2, 3), (11, 1), (73, 1), (97, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_97
    · exact prime_421
  · decide +kernel

theorem prime_325257169 : Nat.Prime 325257169 := by
  apply nodeValid_prime [2, 3, 23, 101, 2917] ⟨325257169, 7, [(2, 4), (3, 1), (23, 1), (101, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_101
    · exact prime_2917
  · decide +kernel

theorem prime_444510127 : Nat.Prime 444510127 := by
  apply nodeValid_prime [2, 3, 71, 269, 431] ⟨444510127, 6, [(2, 1), (3, 3), (71, 1), (269, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_269
    · exact prime_431
  · decide +kernel

theorem prime_563828669 : Nat.Prime 563828669 := by
  apply nodeValid_prime [2, 13, 10842859] ⟨563828669, 2, [(2, 2), (13, 1), (10842859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10842859
  · decide +kernel

theorem prime_610954973 : Nat.Prime 610954973 := by
  apply nodeValid_prime [2, 6317, 24179] ⟨610954973, 2, [(2, 2), (6317, 1), (24179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6317
    · exact prime_24179
  · decide +kernel

theorem prime_1082563003 : Nat.Prime 1082563003 := by
  apply nodeValid_prime [2, 3, 179, 111997] ⟨1082563003, 2, [(2, 1), (3, 3), (179, 1), (111997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_111997
  · decide +kernel

theorem prime_1166440333 : Nat.Prime 1166440333 := by
  apply nodeValid_prime [2, 3, 311, 312551] ⟨1166440333, 2, [(2, 2), (3, 1), (311, 1), (312551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_312551
  · decide +kernel

theorem prime_1616400473 : Nat.Prime 1616400473 := by
  apply nodeValid_prime [2, 257, 659, 1193] ⟨1616400473, 3, [(2, 3), (257, 1), (659, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_659
    · exact prime_1193
  · decide +kernel

theorem prime_2304957191 : Nat.Prime 2304957191 := by
  apply nodeValid_prime [2, 5, 23, 457, 21929] ⟨2304957191, 11, [(2, 1), (5, 1), (23, 1), (457, 1), (21929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_457
    · exact prime_21929
  · decide +kernel

theorem prime_2706408709 : Nat.Prime 2706408709 := by
  apply nodeValid_prime [2, 3, 47, 271, 17707] ⟨2706408709, 6, [(2, 2), (3, 1), (47, 1), (271, 1), (17707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_271
    · exact prime_17707
  · decide +kernel

theorem prime_4609914383 : Nat.Prime 4609914383 := by
  apply nodeValid_prime [2, 2304957191] ⟨4609914383, 5, [(2, 1), (2304957191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2304957191
  · decide +kernel

theorem prime_4722064003 : Nat.Prime 4722064003 := by
  apply nodeValid_prime [2, 3, 262336889] ⟨4722064003, 3, [(2, 1), (3, 2), (262336889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_262336889
  · decide +kernel

theorem prime_5380509479 : Nat.Prime 5380509479 := by
  apply nodeValid_prime [2, 2281, 1179419] ⟨5380509479, 7, [(2, 1), (2281, 1), (1179419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2281
    · exact prime_1179419
  · decide +kernel

theorem prime_5999449381 : Nat.Prime 5999449381 := by
  apply nodeValid_prime [2, 3, 5, 109, 797, 1151] ⟨5999449381, 10, [(2, 2), (3, 1), (5, 1), (109, 1), (797, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_797
    · exact prime_1151
  · decide +kernel

theorem prime_7309327063 : Nat.Prime 7309327063 := by
  apply nodeValid_prime [2, 3, 421, 2893637] ⟨7309327063, 3, [(2, 1), (3, 1), (421, 1), (2893637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
    · exact prime_2893637
  · decide +kernel

theorem prime_9219828767 : Nat.Prime 9219828767 := by
  apply nodeValid_prime [2, 4609914383] ⟨9219828767, 5, [(2, 1), (4609914383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4609914383
  · decide +kernel

theorem prime_12108662557 : Nat.Prime 12108662557 := by
  apply nodeValid_prime [2, 3, 17, 1579, 37591] ⟨12108662557, 2, [(2, 2), (3, 1), (17, 1), (1579, 1), (37591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1579
    · exact prime_37591
  · decide +kernel

theorem prime_12219099461 : Nat.Prime 12219099461 := by
  apply nodeValid_prime [2, 5, 610954973] ⟨12219099461, 2, [(2, 2), (5, 1), (610954973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_610954973
  · decide +kernel

theorem prime_71121605117 : Nat.Prime 71121605117 := by
  apply nodeValid_prime [2, 69067, 257437] ⟨71121605117, 2, [(2, 2), (69067, 1), (257437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_69067
    · exact prime_257437
  · decide +kernel

theorem prime_71121620321 : Nat.Prime 71121620321 := by
  apply nodeValid_prime [2, 5, 444510127] ⟨71121620321, 3, [(2, 5), (5, 1), (444510127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_444510127
  · decide +kernel

theorem prime_71121620813 : Nat.Prime 71121620813 := by
  apply nodeValid_prime [2, 11, 1616400473] ⟨71121620813, 2, [(2, 2), (11, 1), (1616400473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1616400473
  · decide +kernel

theorem prime_71338838419 : Nat.Prime 71338838419 := by
  apply nodeValid_prime [2, 3, 37, 107115373] ⟨71338838419, 7, [(2, 1), (3, 2), (37, 1), (107115373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_107115373
  · decide +kernel

theorem prime_71338838611 : Nat.Prime 71338838611 := by
  apply nodeValid_prime [2, 3, 5, 13, 47, 3891917] ⟨71338838611, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (47, 1), (3891917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_47
    · exact prime_3891917
  · decide +kernel

theorem prime_71338873993 : Nat.Prime 71338873993 := by
  apply nodeValid_prime [2, 3, 13759, 216037] ⟨71338873993, 5, [(2, 3), (3, 1), (13759, 1), (216037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13759
    · exact prime_216037
  · decide +kernel

theorem prime_71556575591 : Nat.Prime 71556575591 := by
  apply nodeValid_prime [2, 5, 211, 33913069] ⟨71556575591, 7, [(2, 1), (5, 1), (211, 1), (33913069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
    · exact prime_33913069
  · decide +kernel

theorem prime_71556577181 : Nat.Prime 71556577181 := by
  apply nodeValid_prime [2, 5, 11, 325257169] ⟨71556577181, 3, [(2, 2), (5, 1), (11, 1), (325257169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_325257169
  · decide +kernel

theorem prime_71556598273 : Nat.Prime 71556598273 := by
  apply nodeValid_prime [2, 3, 409, 113903] ⟨71556598273, 5, [(2, 9), (3, 1), (409, 1), (113903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_409
    · exact prime_113903
  · decide +kernel

theorem prime_71774773171 : Nat.Prime 71774773171 := by
  apply nodeValid_prime [2, 3, 5, 1823, 1312393] ⟨71774773171, 2, [(2, 1), (3, 1), (5, 1), (1823, 1), (1312393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1823
    · exact prime_1312393
  · decide +kernel

theorem prime_71774808691 : Nat.Prime 71774808691 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 19, 41, 1069] ⟨71774808691, 3, [(2, 1), (3, 1), (5, 1), (13, 2), (17, 1), (19, 1), (41, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_41
    · exact prime_1069
  · decide +kernel

theorem prime_71774808737 : Nat.Prime 71774808737 := by
  apply nodeValid_prime [2, 21089, 106357] ⟨71774808737, 3, [(2, 5), (21089, 1), (106357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21089
    · exact prime_106357
  · decide +kernel

theorem prime_71993392573 : Nat.Prime 71993392573 := by
  apply nodeValid_prime [2, 3, 5999449381] ⟨71993392573, 5, [(2, 2), (3, 1), (5999449381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5999449381
  · decide +kernel

theorem prime_71993393539 : Nat.Prime 71993393539 := by
  apply nodeValid_prime [2, 3, 11, 43, 1613, 15727] ⟨71993393539, 2, [(2, 1), (3, 1), (11, 1), (43, 1), (1613, 1), (15727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_1613
    · exact prime_15727
  · decide +kernel

theorem prime_71993396507 : Nat.Prime 71993396507 := by
  apply nodeValid_prime [2, 29, 101, 12289757] ⟨71993396507, 2, [(2, 1), (29, 1), (101, 1), (12289757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_101
    · exact prime_12289757
  · decide +kernel

theorem prime_72212453177 : Nat.Prime 72212453177 := by
  apply nodeValid_prime [2, 2069, 4362763] ⟨72212453177, 3, [(2, 3), (2069, 1), (4362763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2069
    · exact prime_4362763
  · decide +kernel

theorem prime_72212454521 : Nat.Prime 72212454521 := by
  apply nodeValid_prime [2, 5, 37, 1847, 26417] ⟨72212454521, 3, [(2, 3), (5, 1), (37, 1), (1847, 1), (26417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1847
    · exact prime_26417
  · decide +kernel

theorem prime_72212464409 : Nat.Prime 72212464409 := by
  apply nodeValid_prime [2, 7, 17, 75853429] ⟨72212464409, 3, [(2, 3), (7, 1), (17, 1), (75853429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_75853429
  · decide +kernel

theorem prime_72431983621 : Nat.Prime 72431983621 := by
  apply nodeValid_prime [2, 3, 5, 5821, 7681] ⟨72431983621, 2, [(2, 2), (3, 4), (5, 1), (5821, 1), (7681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5821
    · exact prime_7681
  · decide +kernel

theorem prime_72431999041 : Nat.Prime 72431999041 := by
  apply nodeValid_prime [2, 3, 5, 1117, 67547] ⟨72431999041, 7, [(2, 6), (3, 1), (5, 1), (1117, 1), (67547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1117
    · exact prime_67547
  · decide +kernel

theorem prime_72651956759 : Nat.Prime 72651956759 := by
  apply nodeValid_prime [2, 47, 311, 2485187] ⟨72651956759, 7, [(2, 1), (47, 1), (311, 1), (2485187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_311
    · exact prime_2485187
  · decide +kernel

theorem prime_72651975133 : Nat.Prime 72651975133 := by
  apply nodeValid_prime [2, 3, 11, 17, 331, 97813] ⟨72651975133, 5, [(2, 2), (3, 1), (11, 1), (17, 1), (331, 1), (97813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_331
    · exact prime_97813
  · decide +kernel

theorem prime_72651975343 : Nat.Prime 72651975343 := by
  apply nodeValid_prime [2, 3, 12108662557] ⟨72651975343, 3, [(2, 1), (3, 1), (12108662557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12108662557
  · decide +kernel

theorem prime_72872384983 : Nat.Prime 72872384983 := by
  apply nodeValid_prime [2, 3, 61, 199104877] ⟨72872384983, 3, [(2, 1), (3, 1), (61, 1), (199104877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_199104877
  · decide +kernel

theorem prime_72872389283 : Nat.Prime 72872389283 := by
  apply nodeValid_prime [2, 7, 11, 67599619] ⟨72872389283, 6, [(2, 1), (7, 2), (11, 1), (67599619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_67599619
  · decide +kernel

theorem prime_72872389463 : Nat.Prime 72872389463 := by
  apply nodeValid_prime [2, 163, 739, 302483] ⟨72872389463, 5, [(2, 1), (163, 1), (739, 1), (302483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_739
    · exact prime_302483
  · decide +kernel

theorem prime_73093265213 : Nat.Prime 73093265213 := by
  apply nodeValid_prime [2, 11, 17, 443, 1823] ⟨73093265213, 2, [(2, 2), (11, 3), (17, 1), (443, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_443
    · exact prime_1823
  · decide +kernel

theorem prime_73093270631 : Nat.Prime 73093270631 := by
  apply nodeValid_prime [2, 5, 7309327063] ⟨73093270631, 37, [(2, 1), (5, 1), (7309327063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7309327063
  · decide +kernel

theorem prime_73093271003 : Nat.Prime 73093271003 := by
  apply nodeValid_prime [2, 94771, 385631] ⟨73093271003, 2, [(2, 1), (94771, 1), (385631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_94771
    · exact prime_385631
  · decide +kernel

theorem prime_73314596767 : Nat.Prime 73314596767 := by
  apply nodeValid_prime [2, 3, 12219099461] ⟨73314596767, 3, [(2, 1), (3, 1), (12219099461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12219099461
  · decide +kernel

theorem prime_73314597017 : Nat.Prime 73314597017 := by
  apply nodeValid_prime [2, 139, 7669, 8597] ⟨73314597017, 3, [(2, 3), (139, 1), (7669, 1), (8597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_7669
    · exact prime_8597
  · decide +kernel

theorem prime_73314597061 : Nat.Prime 73314597061 := by
  apply nodeValid_prime [2, 3, 5, 12911, 31547] ⟨73314597061, 7, [(2, 2), (3, 2), (5, 1), (12911, 1), (31547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12911
    · exact prime_31547
  · decide +kernel

theorem prime_73536385361 : Nat.Prime 73536385361 := by
  apply nodeValid_prime [2, 5, 15739, 58403] ⟨73536385361, 6, [(2, 4), (5, 1), (15739, 1), (58403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15739
    · exact prime_58403
  · decide +kernel

theorem prime_73536410183 : Nat.Prime 73536410183 := by
  apply nodeValid_prime [2, 19, 43, 829, 54287] ⟨73536410183, 5, [(2, 1), (19, 1), (43, 1), (829, 1), (54287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_829
    · exact prime_54287
  · decide +kernel

theorem prime_73536410867 : Nat.Prime 73536410867 := by
  apply nodeValid_prime [2, 19, 31, 62424797] ⟨73536410867, 2, [(2, 1), (19, 1), (31, 1), (62424797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_62424797
  · decide +kernel

theorem prime_73758623797 : Nat.Prime 73758623797 := by
  apply nodeValid_prime [2, 3, 11, 13, 14327627] ⟨73758623797, 6, [(2, 2), (3, 2), (11, 1), (13, 1), (14327627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_14327627
  · decide +kernel

theorem prime_73758626251 : Nat.Prime 73758626251 := by
  apply nodeValid_prime [2, 3, 5, 953, 20639] ⟨73758626251, 2, [(2, 1), (3, 1), (5, 4), (953, 1), (20639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_953
    · exact prime_20639
  · decide +kernel

theorem prime_73758630137 : Nat.Prime 73758630137 := by
  apply nodeValid_prime [2, 9219828767] ⟨73758630137, 3, [(2, 3), (9219828767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9219828767
  · decide +kernel

theorem prime_73981332533 : Nat.Prime 73981332533 := by
  apply nodeValid_prime [2, 563, 32851391] ⟨73981332533, 2, [(2, 2), (563, 1), (32851391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_32851391
  · decide +kernel

theorem prime_73981340617 : Nat.Prime 73981340617 := by
  apply nodeValid_prime [2, 3, 42019, 73361] ⟨73981340617, 17, [(2, 3), (3, 1), (42019, 1), (73361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42019
    · exact prime_73361
  · decide +kernel

theorem prime_73981340647 : Nat.Prime 73981340647 := by
  apply nodeValid_prime [2, 3, 613, 20114557] ⟨73981340647, 3, [(2, 1), (3, 1), (613, 1), (20114557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_20114557
  · decide +kernel

theorem prime_74204482543 : Nat.Prime 74204482543 := by
  apply nodeValid_prime [2, 3, 233, 509, 104281] ⟨74204482543, 3, [(2, 1), (3, 1), (233, 1), (509, 1), (104281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_509
    · exact prime_104281
  · decide +kernel

theorem prime_74204482747 : Nat.Prime 74204482747 := by
  apply nodeValid_prime [2, 3, 1033, 11972327] ⟨74204482747, 2, [(2, 1), (3, 1), (1033, 1), (11972327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
    · exact prime_11972327
  · decide +kernel

theorem prime_74204487883 : Nat.Prime 74204487883 := by
  apply nodeValid_prime [2, 3, 7, 73, 1291, 2083] ⟨74204487883, 2, [(2, 1), (3, 3), (7, 1), (73, 1), (1291, 1), (2083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_1291
    · exact prime_2083
  · decide +kernel

theorem prime_74428098323 : Nat.Prime 74428098323 := by
  apply nodeValid_prime [2, 1033, 36025217] ⟨74428098323, 2, [(2, 1), (1033, 1), (36025217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1033
    · exact prime_36025217
  · decide +kernel

theorem prime_74428105303 : Nat.Prime 74428105303 := by
  apply nodeValid_prime [2, 3, 1283, 3222833] ⟨74428105303, 5, [(2, 1), (3, 2), (1283, 1), (3222833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1283
    · exact prime_3222833
  · decide +kernel

theorem prime_74428105307 : Nat.Prime 74428105307 := by
  apply nodeValid_prime [2, 61583, 604291] ⟨74428105307, 2, [(2, 1), (61583, 1), (604291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61583
    · exact prime_604291
  · decide +kernel

theorem prime_74652165493 : Nat.Prime 74652165493 := by
  apply nodeValid_prime [2, 3, 73, 1031, 82657] ⟨74652165493, 2, [(2, 2), (3, 1), (73, 1), (1031, 1), (82657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_1031
    · exact prime_82657
  · decide +kernel

theorem prime_74652181229 : Nat.Prime 74652181229 := by
  apply nodeValid_prime [2, 41, 139, 79873] ⟨74652181229, 2, [(2, 2), (41, 2), (139, 1), (79873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_139
    · exact prime_79873
  · decide +kernel

theorem prime_74652181313 : Nat.Prime 74652181313 := by
  apply nodeValid_prime [2, 1166440333] ⟨74652181313, 3, [(2, 6), (1166440333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1166440333
  · decide +kernel

theorem prime_74876694121 : Nat.Prime 74876694121 := by
  apply nodeValid_prime [2, 3, 5, 23, 9043079] ⟨74876694121, 13, [(2, 3), (3, 2), (5, 1), (23, 1), (9043079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_9043079
  · decide +kernel

theorem prime_74876706071 : Nat.Prime 74876706071 := by
  apply nodeValid_prime [2, 5, 251, 29831357] ⟨74876706071, 13, [(2, 1), (5, 1), (251, 1), (29831357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
    · exact prime_29831357
  · decide +kernel

theorem prime_74876706109 : Nat.Prime 74876706109 := by
  apply nodeValid_prime [2, 3, 17, 359, 340801] ⟨74876706109, 6, [(2, 2), (3, 2), (17, 1), (359, 1), (340801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_359
    · exact prime_340801
  · decide +kernel

theorem prime_75101683771 : Nat.Prime 75101683771 := by
  apply nodeValid_prime [2, 3, 5, 467, 937, 1907] ⟨75101683771, 7, [(2, 1), (3, 2), (5, 1), (467, 1), (937, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
    · exact prime_937
    · exact prime_1907
  · decide +kernel

theorem prime_75101695993 : Nat.Prime 75101695993 := by
  apply nodeValid_prime [2, 3, 5323, 21773] ⟨75101695993, 5, [(2, 3), (3, 4), (5323, 1), (21773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5323
    · exact prime_21773
  · decide +kernel

theorem prime_75101696713 : Nat.Prime 75101696713 := by
  apply nodeValid_prime [2, 3, 7, 97, 107, 293] ⟨75101696713, 10, [(2, 3), (3, 2), (7, 3), (97, 1), (107, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_107
    · exact prime_293
  · decide +kernel

theorem prime_75327132707 : Nat.Prime 75327132707 := by
  apply nodeValid_prime [2, 7, 5380509479] ⟨75327132707, 5, [(2, 1), (7, 1), (5380509479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5380509479
  · decide +kernel

theorem prime_75327175267 : Nat.Prime 75327175267 := by
  apply nodeValid_prime [2, 3, 7, 67, 26768719] ⟨75327175267, 2, [(2, 1), (3, 1), (7, 1), (67, 1), (26768719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
    · exact prime_26768719
  · decide +kernel

theorem prime_75327175711 : Nat.Prime 75327175711 := by
  apply nodeValid_prime [2, 3, 5, 5867, 142657] ⟨75327175711, 3, [(2, 1), (3, 2), (5, 1), (5867, 1), (142657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5867
    · exact prime_142657
  · decide +kernel

theorem prime_75553024049 : Nat.Prime 75553024049 := by
  apply nodeValid_prime [2, 4722064003] ⟨75553024049, 3, [(2, 4), (4722064003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4722064003
  · decide +kernel

theorem prime_75553024201 : Nat.Prime 75553024201 := by
  apply nodeValid_prime [2, 3, 5, 83, 277, 5477] ⟨75553024201, 11, [(2, 3), (3, 1), (5, 2), (83, 1), (277, 1), (5477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_277
    · exact prime_5477
  · decide +kernel

theorem prime_75553041647 : Nat.Prime 75553041647 := by
  apply nodeValid_prime [2, 67, 563828669] ⟨75553041647, 5, [(2, 1), (67, 1), (563828669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_563828669
  · decide +kernel

theorem prime_75779410211 : Nat.Prime 75779410211 := by
  apply nodeValid_prime [2, 5, 7, 1082563003] ⟨75779410211, 2, [(2, 1), (5, 1), (7, 1), (1082563003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1082563003
  · decide +kernel

theorem prime_75779443853 : Nat.Prime 75779443853 := by
  apply nodeValid_prime [2, 7, 2706408709] ⟨75779443853, 2, [(2, 2), (7, 1), (2706408709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2706408709
  · decide +kernel

theorem prime_75779444053 : Nat.Prime 75779444053 := by
  apply nodeValid_prime [2, 3, 13, 17, 352771] ⟨75779444053, 26, [(2, 2), (3, 5), (13, 1), (17, 1), (352771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_352771
  · decide +kernel

theorem prime_76006236191 : Nat.Prime 76006236191 := by
  apply nodeValid_prime [2, 5, 17, 251, 1231, 1447] ⟨76006236191, 7, [(2, 1), (5, 1), (17, 1), (251, 1), (1231, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_251
    · exact prime_1231
    · exact prime_1447
  · decide +kernel

theorem prime_76006237793 : Nat.Prime 76006237793 := by
  apply nodeValid_prime [2, 281, 1531, 5521] ⟨76006237793, 3, [(2, 5), (281, 1), (1531, 1), (5521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_1531
    · exact prime_5521
  · decide +kernel

theorem prime_76233525727 : Nat.Prime 76233525727 := by
  apply nodeValid_prime [2, 3, 41, 167, 251, 7393] ⟨76233525727, 3, [(2, 1), (3, 1), (41, 1), (167, 1), (251, 1), (7393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_167
    · exact prime_251
    · exact prime_7393
  · decide +kernel

theorem prime_76461271123 : Nat.Prime 76461271123 := by
  apply nodeValid_prime [2, 3, 83, 181, 848269] ⟨76461271123, 3, [(2, 1), (3, 1), (83, 1), (181, 1), (848269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_181
    · exact prime_848269
  · decide +kernel

theorem prime_76461271349 : Nat.Prime 76461271349 := by
  apply nodeValid_prime [2, 7, 11, 17, 73, 200041] ⟨76461271349, 2, [(2, 2), (7, 1), (11, 1), (17, 1), (73, 1), (200041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_73
    · exact prime_200041
  · decide +kernel

theorem prime_76461275081 : Nat.Prime 76461275081 := by
  apply nodeValid_prime [2, 5, 47, 149, 272959] ⟨76461275081, 3, [(2, 3), (5, 1), (47, 1), (149, 1), (272959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_149
    · exact prime_272959
  · decide +kernel

end Sude.Lucas.Generated
