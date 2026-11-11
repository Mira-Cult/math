import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0090
import Sude.GeneratedTwinBase.M000

/-! Generated Lucas nodes for the FT base; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_31687 : Nat.Prime 31687 := by
  apply nodeValid_prime [2, 3, 5281] ⟨31687, 3, [(2, 1), (3, 1), (5281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5281
  · decide +kernel

theorem prime_31721 : Nat.Prime 31721 := by
  apply nodeValid_prime [2, 5, 13, 61] ⟨31721, 11, [(2, 3), (5, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_31723 : Nat.Prime 31723 := by
  apply nodeValid_prime [2, 3, 17, 311] ⟨31723, 3, [(2, 1), (3, 1), (17, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_311
  · decide +kernel

theorem prime_31751 : Nat.Prime 31751 := by
  apply nodeValid_prime [2, 5, 127] ⟨31751, 11, [(2, 1), (5, 3), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_31799 : Nat.Prime 31799 := by
  apply nodeValid_prime [2, 13, 1223] ⟨31799, 11, [(2, 1), (13, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1223
  · decide +kernel

theorem prime_31847 : Nat.Prime 31847 := by
  apply nodeValid_prime [2, 15923] ⟨31847, 5, [(2, 1), (15923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15923
  · decide +kernel

theorem prime_31883 : Nat.Prime 31883 := by
  apply nodeValid_prime [2, 19, 839] ⟨31883, 2, [(2, 1), (19, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_839
  · decide +kernel

theorem prime_31907 : Nat.Prime 31907 := by
  apply nodeValid_prime [2, 7, 43, 53] ⟨31907, 2, [(2, 1), (7, 1), (43, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_53
  · decide +kernel

theorem prime_31963 : Nat.Prime 31963 := by
  apply nodeValid_prime [2, 3, 7, 761] ⟨31963, 2, [(2, 1), (3, 1), (7, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_761
  · decide +kernel

theorem prime_32003 : Nat.Prime 32003 := by
  apply nodeValid_prime [2, 16001] ⟨32003, 2, [(2, 1), (16001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16001
  · decide +kernel

theorem prime_32057 : Nat.Prime 32057 := by
  apply nodeValid_prime [2, 4007] ⟨32057, 3, [(2, 3), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4007
  · decide +kernel

theorem prime_32059 : Nat.Prime 32059 := by
  apply nodeValid_prime [2, 3, 13, 137] ⟨32059, 2, [(2, 1), (3, 2), (13, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_137
  · decide +kernel

theorem prime_32063 : Nat.Prime 32063 := by
  apply nodeValid_prime [2, 17, 23, 41] ⟨32063, 5, [(2, 1), (17, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_32077 : Nat.Prime 32077 := by
  apply nodeValid_prime [2, 3, 11] ⟨32077, 2, [(2, 2), (3, 6), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_32083 : Nat.Prime 32083 := by
  apply nodeValid_prime [2, 3, 5347] ⟨32083, 2, [(2, 1), (3, 1), (5347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5347
  · decide +kernel

theorem prime_32089 : Nat.Prime 32089 := by
  apply nodeValid_prime [2, 3, 7, 191] ⟨32089, 13, [(2, 3), (3, 1), (7, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_191
  · decide +kernel

theorem prime_32099 : Nat.Prime 32099 := by
  apply nodeValid_prime [2, 11, 1459] ⟨32099, 2, [(2, 1), (11, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1459
  · decide +kernel

theorem prime_32117 : Nat.Prime 32117 := by
  apply nodeValid_prime [2, 7, 31, 37] ⟨32117, 2, [(2, 2), (7, 1), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_32119 : Nat.Prime 32119 := by
  apply nodeValid_prime [2, 3, 53, 101] ⟨32119, 3, [(2, 1), (3, 1), (53, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_101
  · decide +kernel

theorem prime_32159 : Nat.Prime 32159 := by
  apply nodeValid_prime [2, 7, 2297] ⟨32159, 7, [(2, 1), (7, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2297
  · decide +kernel

theorem prime_32183 : Nat.Prime 32183 := by
  apply nodeValid_prime [2, 16091] ⟨32183, 5, [(2, 1), (16091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16091
  · decide +kernel

theorem prime_32261 : Nat.Prime 32261 := by
  apply nodeValid_prime [2, 5, 1613] ⟨32261, 2, [(2, 2), (5, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1613
  · decide +kernel

theorem prime_32299 : Nat.Prime 32299 := by
  apply nodeValid_prime [2, 3, 7, 769] ⟨32299, 12, [(2, 1), (3, 1), (7, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_769
  · decide +kernel

theorem prime_32303 : Nat.Prime 32303 := by
  apply nodeValid_prime [2, 31, 521] ⟨32303, 5, [(2, 1), (31, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_521
  · decide +kernel

theorem prime_32321 : Nat.Prime 32321 := by
  apply nodeValid_prime [2, 5, 101] ⟨32321, 6, [(2, 6), (5, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_32341 : Nat.Prime 32341 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨32341, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_32353 : Nat.Prime 32353 := by
  apply nodeValid_prime [2, 3, 337] ⟨32353, 15, [(2, 5), (3, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
  · decide +kernel

theorem prime_32359 : Nat.Prime 32359 := by
  apply nodeValid_prime [2, 3, 5393] ⟨32359, 3, [(2, 1), (3, 1), (5393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5393
  · decide +kernel

theorem prime_32363 : Nat.Prime 32363 := by
  apply nodeValid_prime [2, 11, 1471] ⟨32363, 2, [(2, 1), (11, 1), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1471
  · decide +kernel

theorem prime_32371 : Nat.Prime 32371 := by
  apply nodeValid_prime [2, 3, 5, 13, 83] ⟨32371, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_32401 : Nat.Prime 32401 := by
  apply nodeValid_prime [2, 3, 5] ⟨32401, 7, [(2, 4), (3, 4), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_32423 : Nat.Prime 32423 := by
  apply nodeValid_prime [2, 13, 29, 43] ⟨32423, 5, [(2, 1), (13, 1), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_32491 : Nat.Prime 32491 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨32491, 2, [(2, 1), (3, 2), (5, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_32497 : Nat.Prime 32497 := by
  apply nodeValid_prime [2, 3, 677] ⟨32497, 7, [(2, 4), (3, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
  · decide +kernel

theorem prime_32531 : Nat.Prime 32531 := by
  apply nodeValid_prime [2, 5, 3253] ⟨32531, 2, [(2, 1), (5, 1), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3253
  · decide +kernel

theorem prime_32561 : Nat.Prime 32561 := by
  apply nodeValid_prime [2, 5, 11, 37] ⟨32561, 6, [(2, 4), (5, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_32563 : Nat.Prime 32563 := by
  apply nodeValid_prime [2, 3, 67] ⟨32563, 2, [(2, 1), (3, 5), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
  · decide +kernel

theorem prime_32569 : Nat.Prime 32569 := by
  apply nodeValid_prime [2, 3, 23, 59] ⟨32569, 7, [(2, 3), (3, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_32573 : Nat.Prime 32573 := by
  apply nodeValid_prime [2, 17, 479] ⟨32573, 2, [(2, 2), (17, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_479
  · decide +kernel

theorem prime_32587 : Nat.Prime 32587 := by
  apply nodeValid_prime [2, 3, 5431] ⟨32587, 2, [(2, 1), (3, 1), (5431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5431
  · decide +kernel

theorem prime_32603 : Nat.Prime 32603 := by
  apply nodeValid_prime [2, 16301] ⟨32603, 2, [(2, 1), (16301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16301
  · decide +kernel

theorem prime_32633 : Nat.Prime 32633 := by
  apply nodeValid_prime [2, 4079] ⟨32633, 3, [(2, 3), (4079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4079
  · decide +kernel

theorem prime_32653 : Nat.Prime 32653 := by
  apply nodeValid_prime [2, 3, 907] ⟨32653, 2, [(2, 2), (3, 2), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
  · decide +kernel

theorem prime_32687 : Nat.Prime 32687 := by
  apply nodeValid_prime [2, 59, 277] ⟨32687, 5, [(2, 1), (59, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_277
  · decide +kernel

theorem prime_32713 : Nat.Prime 32713 := by
  apply nodeValid_prime [2, 3, 29, 47] ⟨32713, 5, [(2, 3), (3, 1), (29, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_47
  · decide +kernel

end Sude.Lucas.Generated
