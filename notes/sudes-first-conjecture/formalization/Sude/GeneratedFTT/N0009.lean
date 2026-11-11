import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_839 : Nat.Prime 839 := by
  apply nodeValid_prime [2, 419] ⟨839, 11, [(2, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_419
  · decide +kernel

theorem prime_883 : Nat.Prime 883 := by
  apply nodeValid_prime [2, 3, 7] ⟨883, 2, [(2, 1), (3, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_1489 : Nat.Prime 1489 := by
  apply nodeValid_prime [2, 3, 31] ⟨1489, 14, [(2, 4), (3, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_1913 : Nat.Prime 1913 := by
  apply nodeValid_prime [2, 239] ⟨1913, 3, [(2, 3), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_239
  · decide +kernel

theorem prime_2129 : Nat.Prime 2129 := by
  apply nodeValid_prime [2, 7, 19] ⟨2129, 3, [(2, 4), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_2203 : Nat.Prime 2203 := by
  apply nodeValid_prime [2, 3, 367] ⟨2203, 5, [(2, 1), (3, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
  · decide +kernel

theorem prime_2221 : Nat.Prime 2221 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨2221, 2, [(2, 2), (3, 1), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_2551 : Nat.Prime 2551 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨2551, 6, [(2, 1), (3, 1), (5, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_2633 : Nat.Prime 2633 := by
  apply nodeValid_prime [2, 7, 47] ⟨2633, 3, [(2, 3), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_3137 : Nat.Prime 3137 := by
  apply nodeValid_prime [2, 7] ⟨3137, 3, [(2, 6), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7
  · decide +kernel

theorem prime_3467 : Nat.Prime 3467 := by
  apply nodeValid_prime [2, 1733] ⟨3467, 2, [(2, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1733
  · decide +kernel

theorem prime_3623 : Nat.Prime 3623 := by
  apply nodeValid_prime [2, 1811] ⟨3623, 5, [(2, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1811
  · decide +kernel

theorem prime_4297 : Nat.Prime 4297 := by
  apply nodeValid_prime [2, 3, 179] ⟨4297, 5, [(2, 3), (3, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
  · decide +kernel

theorem prime_5441 : Nat.Prime 5441 := by
  apply nodeValid_prime [2, 5, 17] ⟨5441, 3, [(2, 6), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_5623 : Nat.Prime 5623 := by
  apply nodeValid_prime [2, 3, 937] ⟨5623, 5, [(2, 1), (3, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_937
  · decide +kernel

theorem prime_5839 : Nat.Prime 5839 := by
  apply nodeValid_prime [2, 3, 7, 139] ⟨5839, 6, [(2, 1), (3, 1), (7, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_6133 : Nat.Prime 6133 := by
  apply nodeValid_prime [2, 3, 7, 73] ⟨6133, 5, [(2, 2), (3, 1), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_6257 : Nat.Prime 6257 := by
  apply nodeValid_prime [2, 17, 23] ⟨6257, 3, [(2, 4), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_6553 : Nat.Prime 6553 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨6553, 10, [(2, 3), (3, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_6763 : Nat.Prime 6763 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨6763, 2, [(2, 1), (3, 1), (7, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_6833 : Nat.Prime 6833 := by
  apply nodeValid_prime [2, 7, 61] ⟨6833, 3, [(2, 4), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_6869 : Nat.Prime 6869 := by
  apply nodeValid_prime [2, 17, 101] ⟨6869, 2, [(2, 2), (17, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_101
  · decide +kernel

theorem prime_7109 : Nat.Prime 7109 := by
  apply nodeValid_prime [2, 1777] ⟨7109, 2, [(2, 2), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1777
  · decide +kernel

theorem prime_7247 : Nat.Prime 7247 := by
  apply nodeValid_prime [2, 3623] ⟨7247, 5, [(2, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3623
  · decide +kernel

theorem prime_7457 : Nat.Prime 7457 := by
  apply nodeValid_prime [2, 233] ⟨7457, 3, [(2, 5), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_233
  · decide +kernel

theorem prime_7789 : Nat.Prime 7789 := by
  apply nodeValid_prime [2, 3, 11, 59] ⟨7789, 2, [(2, 2), (3, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_8081 : Nat.Prime 8081 := by
  apply nodeValid_prime [2, 5, 101] ⟨8081, 3, [(2, 4), (5, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_9199 : Nat.Prime 9199 := by
  apply nodeValid_prime [2, 3, 7, 73] ⟨9199, 3, [(2, 1), (3, 2), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_10133 : Nat.Prime 10133 := by
  apply nodeValid_prime [2, 17, 149] ⟨10133, 2, [(2, 2), (17, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_149
  · decide +kernel

theorem prime_10223 : Nat.Prime 10223 := by
  apply nodeValid_prime [2, 19, 269] ⟨10223, 5, [(2, 1), (19, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_269
  · decide +kernel

theorem prime_10331 : Nat.Prime 10331 := by
  apply nodeValid_prime [2, 5, 1033] ⟨10331, 2, [(2, 1), (5, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1033
  · decide +kernel

theorem prime_10883 : Nat.Prime 10883 := by
  apply nodeValid_prime [2, 5441] ⟨10883, 2, [(2, 1), (5441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5441
  · decide +kernel

theorem prime_11071 : Nat.Prime 11071 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨11071, 3, [(2, 1), (3, 3), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_11551 : Nat.Prime 11551 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨11551, 7, [(2, 1), (3, 1), (5, 2), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_13879 : Nat.Prime 13879 := by
  apply nodeValid_prime [2, 3, 257] ⟨13879, 6, [(2, 1), (3, 3), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
  · decide +kernel

theorem prime_15053 : Nat.Prime 15053 := by
  apply nodeValid_prime [2, 53, 71] ⟨15053, 2, [(2, 2), (53, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_71
  · decide +kernel

theorem prime_15991 : Nat.Prime 15991 := by
  apply nodeValid_prime [2, 3, 5, 13, 41] ⟨15991, 12, [(2, 1), (3, 1), (5, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_18289 : Nat.Prime 18289 := by
  apply nodeValid_prime [2, 3, 127] ⟨18289, 13, [(2, 4), (3, 2), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
  · decide +kernel

theorem prime_20663 : Nat.Prime 20663 := by
  apply nodeValid_prime [2, 10331] ⟨20663, 5, [(2, 1), (10331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10331
  · decide +kernel

theorem prime_21193 : Nat.Prime 21193 := by
  apply nodeValid_prime [2, 3, 883] ⟨21193, 11, [(2, 3), (3, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_883
  · decide +kernel

theorem prime_22091 : Nat.Prime 22091 := by
  apply nodeValid_prime [2, 5, 47] ⟨22091, 2, [(2, 1), (5, 1), (47, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_22721 : Nat.Prime 22721 := by
  apply nodeValid_prime [2, 5, 71] ⟨22721, 3, [(2, 6), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_23773 : Nat.Prime 23773 := by
  apply nodeValid_prime [2, 3, 7, 283] ⟨23773, 5, [(2, 2), (3, 1), (7, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
  · decide +kernel

theorem prime_25097 : Nat.Prime 25097 := by
  apply nodeValid_prime [2, 3137] ⟨25097, 3, [(2, 3), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3137
  · decide +kernel

theorem prime_26953 : Nat.Prime 26953 := by
  apply nodeValid_prime [2, 3, 1123] ⟨26953, 7, [(2, 3), (3, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1123
  · decide +kernel

theorem prime_34483 : Nat.Prime 34483 := by
  apply nodeValid_prime [2, 3, 7, 821] ⟨34483, 2, [(2, 1), (3, 1), (7, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_821
  · decide +kernel

theorem prime_40289 : Nat.Prime 40289 := by
  apply nodeValid_prime [2, 1259] ⟨40289, 3, [(2, 5), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1259
  · decide +kernel

theorem prime_47381 : Nat.Prime 47381 := by
  apply nodeValid_prime [2, 5, 23, 103] ⟨47381, 2, [(2, 2), (5, 1), (23, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_103
  · decide +kernel

theorem prime_49547 : Nat.Prime 49547 := by
  apply nodeValid_prime [2, 7, 3539] ⟨49547, 2, [(2, 1), (7, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3539
  · decide +kernel

theorem prime_55949 : Nat.Prime 55949 := by
  apply nodeValid_prime [2, 71, 197] ⟨55949, 2, [(2, 2), (71, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_197
  · decide +kernel

theorem prime_62401 : Nat.Prime 62401 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨62401, 17, [(2, 6), (3, 1), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_62969 : Nat.Prime 62969 := by
  apply nodeValid_prime [2, 17, 463] ⟨62969, 3, [(2, 3), (17, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_463
  · decide +kernel

theorem prime_63389 : Nat.Prime 63389 := by
  apply nodeValid_prime [2, 13, 23, 53] ⟨63389, 2, [(2, 2), (13, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_67631 : Nat.Prime 67631 := by
  apply nodeValid_prime [2, 5, 6763] ⟨67631, 7, [(2, 1), (5, 1), (6763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6763
  · decide +kernel

theorem prime_73417 : Nat.Prime 73417 := by
  apply nodeValid_prime [2, 3, 7, 19, 23] ⟨73417, 10, [(2, 3), (3, 1), (7, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_86561 : Nat.Prime 86561 := by
  apply nodeValid_prime [2, 5, 541] ⟨86561, 3, [(2, 5), (5, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_541
  · decide +kernel

theorem prime_95093 : Nat.Prime 95093 := by
  apply nodeValid_prime [2, 23773] ⟨95093, 2, [(2, 2), (23773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23773
  · decide +kernel

theorem prime_99527 : Nat.Prime 99527 := by
  apply nodeValid_prime [2, 7, 7109] ⟨99527, 5, [(2, 1), (7, 1), (7109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7109
  · decide +kernel

theorem prime_103993 : Nat.Prime 103993 := by
  apply nodeValid_prime [2, 3, 7, 619] ⟨103993, 5, [(2, 3), (3, 1), (7, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_619
  · decide +kernel

theorem prime_129097 : Nat.Prime 129097 := by
  apply nodeValid_prime [2, 3, 11, 163] ⟨129097, 5, [(2, 3), (3, 2), (11, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_163
  · decide +kernel

theorem prime_141277 : Nat.Prime 141277 := by
  apply nodeValid_prime [2, 3, 61, 193] ⟨141277, 2, [(2, 2), (3, 1), (61, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_193
  · decide +kernel

theorem prime_141863 : Nat.Prime 141863 := by
  apply nodeValid_prime [2, 7, 10133] ⟨141863, 5, [(2, 1), (7, 1), (10133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10133
  · decide +kernel

theorem prime_144167 : Nat.Prime 144167 := by
  apply nodeValid_prime [2, 11, 6553] ⟨144167, 5, [(2, 1), (11, 1), (6553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6553
  · decide +kernel

theorem prime_152029 : Nat.Prime 152029 := by
  apply nodeValid_prime [2, 3, 41, 103] ⟨152029, 2, [(2, 2), (3, 2), (41, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_103
  · decide +kernel

theorem prime_167597 : Nat.Prime 167597 := by
  apply nodeValid_prime [2, 11, 13, 293] ⟨167597, 2, [(2, 2), (11, 1), (13, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_293
  · decide +kernel

theorem prime_276337 : Nat.Prime 276337 := by
  apply nodeValid_prime [2, 3, 19, 101] ⟨276337, 5, [(2, 4), (3, 2), (19, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_101
  · decide +kernel

theorem prime_282959 : Nat.Prime 282959 := by
  apply nodeValid_prime [2, 13, 10883] ⟨282959, 17, [(2, 1), (13, 1), (10883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10883
  · decide +kernel

theorem prime_315251 : Nat.Prime 315251 := by
  apply nodeValid_prime [2, 5, 13, 97] ⟨315251, 2, [(2, 1), (5, 3), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_467641 : Nat.Prime 467641 := by
  apply nodeValid_prime [2, 3, 5, 433] ⟨467641, 14, [(2, 3), (3, 3), (5, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_433
  · decide +kernel

theorem prime_467941 : Nat.Prime 467941 := by
  apply nodeValid_prime [2, 3, 5, 11, 709] ⟨467941, 10, [(2, 2), (3, 1), (5, 1), (11, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_709
  · decide +kernel

theorem prime_512093 : Nat.Prime 512093 := by
  apply nodeValid_prime [2, 7, 18289] ⟨512093, 3, [(2, 2), (7, 1), (18289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_18289
  · decide +kernel

theorem prime_524941 : Nat.Prime 524941 := by
  apply nodeValid_prime [2, 3, 5, 13, 673] ⟨524941, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_673
  · decide +kernel

theorem prime_543593 : Nat.Prime 543593 := by
  apply nodeValid_prime [2, 7, 17, 571] ⟨543593, 3, [(2, 3), (7, 1), (17, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_571
  · decide +kernel

theorem prime_602713 : Nat.Prime 602713 := by
  apply nodeValid_prime [2, 3, 11, 761] ⟨602713, 7, [(2, 3), (3, 2), (11, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_761
  · decide +kernel

theorem prime_938573 : Nat.Prime 938573 := by
  apply nodeValid_prime [2, 41, 59, 97] ⟨938573, 2, [(2, 2), (41, 1), (59, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_59
    · exact prime_97
  · decide +kernel

theorem prime_1265041 : Nat.Prime 1265041 := by
  apply nodeValid_prime [2, 3, 5, 7, 251] ⟨1265041, 11, [(2, 4), (3, 2), (5, 1), (7, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_251
  · decide +kernel

theorem prime_1635913 : Nat.Prime 1635913 := by
  apply nodeValid_prime [2, 3, 22721] ⟨1635913, 5, [(2, 3), (3, 2), (22721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22721
  · decide +kernel

theorem prime_1875877 : Nat.Prime 1875877 := by
  apply nodeValid_prime [2, 3, 223, 701] ⟨1875877, 2, [(2, 2), (3, 1), (223, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_701
  · decide +kernel

theorem prime_1877147 : Nat.Prime 1877147 := by
  apply nodeValid_prime [2, 938573] ⟨1877147, 2, [(2, 1), (938573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_938573
  · decide +kernel

theorem prime_1987849 : Nat.Prime 1987849 := by
  apply nodeValid_prime [2, 3, 9203] ⟨1987849, 11, [(2, 3), (3, 3), (9203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9203
  · decide +kernel

theorem prime_2028931 : Nat.Prime 2028931 := by
  apply nodeValid_prime [2, 3, 5, 67631] ⟨2028931, 3, [(2, 1), (3, 1), (5, 1), (67631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67631
  · decide +kernel

theorem prime_2584261 : Nat.Prime 2584261 := by
  apply nodeValid_prime [2, 3, 5, 7, 293] ⟨2584261, 6, [(2, 2), (3, 2), (5, 1), (7, 2), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_293
  · decide +kernel

theorem prime_2831317 : Nat.Prime 2831317 := by
  apply nodeValid_prime [2, 3, 17, 13879] ⟨2831317, 5, [(2, 2), (3, 1), (17, 1), (13879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_13879
  · decide +kernel

theorem prime_3057317 : Nat.Prime 3057317 := by
  apply nodeValid_prime [2, 839, 911] ⟨3057317, 2, [(2, 2), (839, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_839
    · exact prime_911
  · decide +kernel

theorem prime_3373151 : Nat.Prime 3373151 := by
  apply nodeValid_prime [2, 5, 11, 6133] ⟨3373151, 11, [(2, 1), (5, 2), (11, 1), (6133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_6133
  · decide +kernel

theorem prime_3993907 : Nat.Prime 3993907 := by
  apply nodeValid_prime [2, 3, 7, 95093] ⟨3993907, 3, [(2, 1), (3, 1), (7, 1), (95093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_95093
  · decide +kernel

theorem prime_4228907 : Nat.Prime 4228907 := by
  apply nodeValid_prime [2, 11, 19, 67, 151] ⟨4228907, 2, [(2, 1), (11, 1), (19, 1), (67, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_67
    · exact prime_151
  · decide +kernel

theorem prime_4728287 : Nat.Prime 4728287 := by
  apply nodeValid_prime [2, 257, 9199] ⟨4728287, 5, [(2, 1), (257, 1), (9199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_9199
  · decide +kernel

theorem prime_4909357 : Nat.Prime 4909357 := by
  apply nodeValid_prime [2, 3, 131, 347] ⟨4909357, 6, [(2, 2), (3, 3), (131, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_347
  · decide +kernel

theorem prime_7870277 : Nat.Prime 7870277 := by
  apply nodeValid_prime [2, 73, 26953] ⟨7870277, 2, [(2, 2), (73, 1), (26953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_26953
  · decide +kernel

theorem prime_8502187 : Nat.Prime 8502187 := by
  apply nodeValid_prime [2, 3, 7, 11, 239] ⟨8502187, 2, [(2, 1), (3, 1), (7, 2), (11, 2), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_239
  · decide +kernel

theorem prime_9157051 : Nat.Prime 9157051 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 19] ⟨9157051, 7, [(2, 1), (3, 4), (5, 2), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_9185893 : Nat.Prime 9185893 := by
  apply nodeValid_prime [2, 3, 19, 40289] ⟨9185893, 2, [(2, 2), (3, 1), (19, 1), (40289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_40289
  · decide +kernel

theorem prime_9325973 : Nat.Prime 9325973 := by
  apply nodeValid_prime [2, 347, 6719] ⟨9325973, 2, [(2, 2), (347, 1), (6719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_6719
  · decide +kernel

theorem prime_9815479 : Nat.Prime 9815479 := by
  apply nodeValid_prime [2, 3, 1635913] ⟨9815479, 3, [(2, 1), (3, 1), (1635913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1635913
  · decide +kernel

theorem prime_16917709 : Nat.Prime 16917709 := by
  apply nodeValid_prime [2, 3, 181, 7789] ⟨16917709, 6, [(2, 2), (3, 1), (181, 1), (7789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_7789
  · decide +kernel

theorem prime_17230981 : Nat.Prime 17230981 := by
  apply nodeValid_prime [2, 3, 5, 13, 22091] ⟨17230981, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (22091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_22091
  · decide +kernel

theorem prime_32869819 : Nat.Prime 32869819 := by
  apply nodeValid_prime [2, 3, 29, 62969] ⟨32869819, 2, [(2, 1), (3, 2), (29, 1), (62969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_62969
  · decide +kernel

theorem prime_34682113 : Nat.Prime 34682113 := by
  apply nodeValid_prime [2, 3, 15053] ⟨34682113, 10, [(2, 8), (3, 2), (15053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15053
  · decide +kernel

theorem prime_37826297 : Nat.Prime 37826297 := by
  apply nodeValid_prime [2, 4728287] ⟨37826297, 3, [(2, 3), (4728287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4728287
  · decide +kernel

theorem prime_41168207 : Nat.Prime 41168207 := by
  apply nodeValid_prime [2, 23, 101, 8861] ⟨41168207, 5, [(2, 1), (23, 1), (101, 1), (8861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_101
    · exact prime_8861
  · decide +kernel

theorem prime_44713607 : Nat.Prime 44713607 := by
  apply nodeValid_prime [2, 7, 1213, 2633] ⟨44713607, 5, [(2, 1), (7, 1), (1213, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1213
    · exact prime_2633
  · decide +kernel

theorem prime_51327481 : Nat.Prime 51327481 := by
  apply nodeValid_prime [2, 3, 5, 619, 691] ⟨51327481, 11, [(2, 3), (3, 1), (5, 1), (619, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_619
    · exact prime_691
  · decide +kernel

theorem prime_62962217 : Nat.Prime 62962217 := by
  apply nodeValid_prime [2, 7870277] ⟨62962217, 3, [(2, 3), (7870277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7870277
  · decide +kernel

theorem prime_63779819 : Nat.Prime 63779819 := by
  apply nodeValid_prime [2, 17, 1875877] ⟨63779819, 2, [(2, 1), (17, 1), (1875877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1875877
  · decide +kernel

theorem prime_77096323 : Nat.Prime 77096323 := by
  apply nodeValid_prime [2, 3, 23, 73, 2551] ⟨77096323, 2, [(2, 1), (3, 2), (23, 1), (73, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_73
    · exact prime_2551
  · decide +kernel

theorem prime_108179213 : Nat.Prime 108179213 := by
  apply nodeValid_prime [2, 23, 31, 83, 457] ⟨108179213, 2, [(2, 2), (23, 1), (31, 1), (83, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_83
    · exact prime_457
  · decide +kernel

theorem prime_109700959 : Nat.Prime 109700959 := by
  apply nodeValid_prime [2, 3, 293, 62401] ⟨109700959, 6, [(2, 1), (3, 1), (293, 1), (62401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_62401
  · decide +kernel

theorem prime_126552611 : Nat.Prime 126552611 := by
  apply nodeValid_prime [2, 5, 367, 34483] ⟨126552611, 6, [(2, 1), (5, 1), (367, 1), (34483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_367
    · exact prime_34483
  · decide +kernel

theorem prime_127559639 : Nat.Prime 127559639 := by
  apply nodeValid_prime [2, 63779819] ⟨127559639, 7, [(2, 1), (63779819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63779819
  · decide +kernel

theorem prime_185256931 : Nat.Prime 185256931 := by
  apply nodeValid_prime [2, 3, 5, 29, 31, 6869] ⟨185256931, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (6869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_31
    · exact prime_6869
  · decide +kernel

theorem prime_216358427 : Nat.Prime 216358427 := by
  apply nodeValid_prime [2, 108179213] ⟨216358427, 2, [(2, 1), (108179213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_108179213
  · decide +kernel

theorem prime_329854747 : Nat.Prime 329854747 := by
  apply nodeValid_prime [2, 3, 13, 4228907] ⟨329854747, 2, [(2, 1), (3, 1), (13, 1), (4228907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4228907
  · decide +kernel

theorem prime_353784877 : Nat.Prime 353784877 := by
  apply nodeValid_prime [2, 3, 2663, 11071] ⟨353784877, 5, [(2, 2), (3, 1), (2663, 1), (11071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2663
    · exact prime_11071
  · decide +kernel

theorem prime_506923609 : Nat.Prime 506923609 := by
  apply nodeValid_prime [2, 3, 67, 315251] ⟨506923609, 21, [(2, 3), (3, 1), (67, 1), (315251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_315251
  · decide +kernel

theorem prime_507530141 : Nat.Prime 507530141 := by
  apply nodeValid_prime [2, 5, 13, 31, 62969] ⟨507530141, 2, [(2, 2), (5, 1), (13, 1), (31, 1), (62969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_62969
  · decide +kernel

theorem prime_518587723 : Nat.Prime 518587723 := by
  apply nodeValid_prime [2, 3, 53, 543593] ⟨518587723, 2, [(2, 1), (3, 2), (53, 1), (543593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_543593
  · decide +kernel

theorem prime_521715079 : Nat.Prime 521715079 := by
  apply nodeValid_prime [2, 3, 41, 163, 4337] ⟨521715079, 3, [(2, 1), (3, 2), (41, 1), (163, 1), (4337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_163
    · exact prime_4337
  · decide +kernel

theorem prime_729770567 : Nat.Prime 729770567 := by
  apply nodeValid_prime [2, 7, 31, 67, 25097] ⟨729770567, 5, [(2, 1), (7, 1), (31, 1), (67, 1), (25097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_67
    · exact prime_25097
  · decide +kernel

theorem prime_809438191 : Nat.Prime 809438191 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 129097] ⟨809438191, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (129097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_129097
  · decide +kernel

theorem prime_865854541 : Nat.Prime 865854541 := by
  apply nodeValid_prime [2, 3, 5, 17, 282959] ⟨865854541, 7, [(2, 2), (3, 2), (5, 1), (17, 1), (282959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_282959
  · decide +kernel

theorem prime_1444637633 : Nat.Prime 1444637633 := by
  apply nodeValid_prime [2, 43, 524941] ⟨1444637633, 3, [(2, 6), (43, 1), (524941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_524941
  · decide +kernel

theorem prime_1828687687 : Nat.Prime 1828687687 := by
  apply nodeValid_prime [2, 3, 7, 503, 86561] ⟨1828687687, 6, [(2, 1), (3, 1), (7, 1), (503, 1), (86561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_503
    · exact prime_86561
  · decide +kernel

theorem prime_1976073937 : Nat.Prime 1976073937 := by
  apply nodeValid_prime [2, 3, 41168207] ⟨1976073937, 5, [(2, 4), (3, 1), (41168207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41168207
  · decide +kernel

theorem prime_1986325769 : Nat.Prime 1986325769 := by
  apply nodeValid_prime [2, 7, 29, 179, 6833] ⟨1986325769, 3, [(2, 3), (7, 1), (29, 1), (179, 1), (6833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_179
    · exact prime_6833
  · decide +kernel

theorem prime_1991465447 : Nat.Prime 1991465447 := by
  apply nodeValid_prime [2, 233, 683, 6257] ⟨1991465447, 5, [(2, 1), (233, 1), (683, 1), (6257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_683
    · exact prime_6257
  · decide +kernel

theorem prime_2027694437 : Nat.Prime 2027694437 := by
  apply nodeValid_prime [2, 506923609] ⟨2027694437, 2, [(2, 2), (506923609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_506923609
  · decide +kernel

theorem prime_2250692263 : Nat.Prime 2250692263 := by
  apply nodeValid_prime [2, 3, 7, 13, 29, 47381] ⟨2250692263, 5, [(2, 1), (3, 2), (7, 1), (13, 1), (29, 1), (47381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_47381
  · decide +kernel

theorem prime_2450953129 : Nat.Prime 2450953129 := by
  apply nodeValid_prime [2, 3, 13, 107, 73417] ⟨2450953129, 19, [(2, 3), (3, 1), (13, 1), (107, 1), (73417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_107
    · exact prime_73417
  · decide +kernel

theorem prime_2457321631 : Nat.Prime 2457321631 := by
  apply nodeValid_prime [2, 3, 5, 823, 99527] ⟨2457321631, 3, [(2, 1), (3, 1), (5, 1), (823, 1), (99527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_823
    · exact prime_99527
  · decide +kernel

theorem prime_11856443623 : Nat.Prime 11856443623 := by
  apply nodeValid_prime [2, 3, 1976073937] ⟨11856443623, 3, [(2, 1), (3, 1), (1976073937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1976073937
  · decide +kernel

theorem prime_60674780339 : Nat.Prime 60674780339 := by
  apply nodeValid_prime [2, 3253, 9325973] ⟨60674780339, 2, [(2, 1), (3253, 1), (9325973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3253
    · exact prime_9325973
  · decide +kernel

theorem prime_61931053001 : Nat.Prime 61931053001 := by
  apply nodeValid_prime [2, 5, 977, 63389] ⟨61931053001, 3, [(2, 3), (5, 3), (977, 1), (63389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_977
    · exact prime_63389
  · decide +kernel

theorem prime_116428402121 : Nat.Prime 116428402121 := by
  apply nodeValid_prime [2, 5, 23, 126552611] ⟨116428402121, 3, [(2, 3), (5, 1), (23, 1), (126552611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_126552611
  · decide +kernel

theorem prime_116428414327 : Nat.Prime 116428414327 := by
  apply nodeValid_prime [2, 3, 7, 49547, 55949] ⟨116428414327, 10, [(2, 1), (3, 1), (7, 1), (49547, 1), (55949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_49547
    · exact prime_55949
  · decide +kernel

theorem prime_116428415107 : Nat.Prime 116428415107 := by
  apply nodeValid_prime [2, 3, 31, 359, 1171, 1489] ⟨116428415107, 3, [(2, 1), (3, 1), (31, 1), (359, 1), (1171, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_359
    · exact prime_1171
    · exact prime_1489
  · decide +kernel

theorem prime_116731932431 : Nat.Prime 116731932431 := by
  apply nodeValid_prime [2, 5, 23, 507530141] ⟨116731932431, 7, [(2, 1), (5, 1), (23, 1), (507530141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_507530141
  · decide +kernel

theorem prime_116731950319 : Nat.Prime 116731950319 := by
  apply nodeValid_prime [2, 3, 103, 62962217] ⟨116731950319, 6, [(2, 1), (3, 2), (103, 1), (62962217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_62962217
  · decide +kernel

theorem prime_116731952543 : Nat.Prime 116731952543 := by
  apply nodeValid_prime [2, 1543, 37826297] ⟨116731952543, 5, [(2, 1), (1543, 1), (37826297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1543
    · exact prime_37826297
  · decide +kernel

theorem prime_117035997677 : Nat.Prime 117035997677 := by
  apply nodeValid_prime [2, 13, 2250692263] ⟨117035997677, 2, [(2, 2), (13, 1), (2250692263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2250692263
  · decide +kernel

theorem prime_117036011969 : Nat.Prime 117036011969 := by
  apply nodeValid_prime [2, 1828687687] ⟨117036011969, 3, [(2, 6), (1828687687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1828687687
  · decide +kernel

theorem prime_117036012169 : Nat.Prime 117036012169 := by
  apply nodeValid_prime [2, 3, 17, 37, 2584261] ⟨117036012169, 7, [(2, 3), (3, 2), (17, 1), (37, 1), (2584261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_2584261
  · decide +kernel

theorem prime_117340597067 : Nat.Prime 117340597067 := by
  apply nodeValid_prime [2, 7, 11, 157, 229, 21193] ⟨117340597067, 2, [(2, 1), (7, 1), (11, 1), (157, 1), (229, 1), (21193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_157
    · exact prime_229
    · exact prime_21193
  · decide +kernel

theorem prime_117340597183 : Nat.Prime 117340597183 := by
  apply nodeValid_prime [2, 3, 2129, 9185893] ⟨117340597183, 3, [(2, 1), (3, 1), (2129, 1), (9185893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2129
    · exact prime_9185893
  · decide +kernel

theorem prime_117340603607 : Nat.Prime 117340603607 := by
  apply nodeValid_prime [2, 761, 77096323] ⟨117340603607, 5, [(2, 1), (761, 1), (77096323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_761
    · exact prime_77096323
  · decide +kernel

theorem prime_117645748387 : Nat.Prime 117645748387 := by
  apply nodeValid_prime [2, 3, 19, 61, 16917709] ⟨117645748387, 2, [(2, 1), (3, 1), (19, 1), (61, 1), (16917709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
    · exact prime_16917709
  · decide +kernel

theorem prime_117645750193 : Nat.Prime 117645750193 := by
  apply nodeValid_prime [2, 3, 2450953129] ⟨117645750193, 5, [(2, 4), (3, 1), (2450953129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2450953129
  · decide +kernel

theorem prime_117645750517 : Nat.Prime 117645750517 := by
  apply nodeValid_prime [2, 3, 7, 311, 503, 1279] ⟨117645750517, 6, [(2, 2), (3, 1), (7, 2), (311, 1), (503, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_311
    · exact prime_503
    · exact prime_1279
  · decide +kernel

theorem prime_117951423283 : Nat.Prime 117951423283 := by
  apply nodeValid_prime [2, 3, 7, 11, 29, 31, 181, 523] ⟨117951423283, 3, [(2, 1), (3, 2), (7, 1), (11, 1), (29, 1), (31, 1), (181, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_31
    · exact prime_181
    · exact prime_523
  · decide +kernel

theorem prime_117951423899 : Nat.Prime 117951423899 := by
  apply nodeValid_prime [2, 7, 11, 5399, 141863] ⟨117951423899, 2, [(2, 1), (7, 1), (11, 1), (5399, 1), (141863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_5399
    · exact prime_141863
  · decide +kernel

theorem prime_117951438289 : Nat.Prime 117951438289 := by
  apply nodeValid_prime [2, 3, 2457321631] ⟨117951438289, 7, [(2, 4), (3, 1), (2457321631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2457321631
  · decide +kernel

theorem prime_118257633803 : Nat.Prime 118257633803 := by
  apply nodeValid_prime [2, 7, 11, 109700959] ⟨118257633803, 5, [(2, 1), (7, 2), (11, 1), (109700959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_109700959
  · decide +kernel

theorem prime_118257636491 : Nat.Prime 118257636491 := by
  apply nodeValid_prime [2, 5, 7, 3299, 512093] ⟨118257636491, 2, [(2, 1), (5, 1), (7, 1), (3299, 1), (512093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3299
    · exact prime_512093
  · decide +kernel

theorem prime_118257659797 : Nat.Prime 118257659797 := by
  apply nodeValid_prime [2, 3, 863, 1373, 8317] ⟨118257659797, 2, [(2, 2), (3, 1), (863, 1), (1373, 1), (8317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863
    · exact prime_1373
    · exact prime_8317
  · decide +kernel

theorem prime_118564417997 : Nat.Prime 118564417997 := by
  apply nodeValid_prime [2, 137, 216358427] ⟨118564417997, 2, [(2, 2), (137, 1), (216358427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_216358427
  · decide +kernel

theorem prime_118564435841 : Nat.Prime 118564435841 := by
  apply nodeValid_prime [2, 5, 185256931] ⟨118564435841, 3, [(2, 7), (5, 1), (185256931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_185256931
  · decide +kernel

theorem prime_118564436231 : Nat.Prime 118564436231 := by
  apply nodeValid_prime [2, 5, 11856443623] ⟨118564436231, 13, [(2, 1), (5, 1), (11856443623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11856443623
  · decide +kernel

theorem prime_118871714677 : Nat.Prime 118871714677 := by
  apply nodeValid_prime [2, 3, 11, 13, 29, 1319, 1811] ⟨118871714677, 2, [(2, 2), (3, 1), (11, 1), (13, 1), (29, 1), (1319, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_29
    · exact prime_1319
    · exact prime_1811
  · decide +kernel

theorem prime_118871717911 : Nat.Prime 118871717911 := by
  apply nodeValid_prime [2, 3, 5, 11, 79, 2053, 2221] ⟨118871717911, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (79, 1), (2053, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_79
    · exact prime_2053
    · exact prime_2221
  · decide +kernel

theorem prime_118871718673 : Nat.Prime 118871718673 := by
  apply nodeValid_prime [2, 3, 7, 353784877] ⟨118871718673, 5, [(2, 4), (3, 1), (7, 1), (353784877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_353784877
  · decide +kernel

theorem prime_119179546019 : Nat.Prime 119179546019 := by
  apply nodeValid_prime [2, 13, 467, 9815479] ⟨119179546019, 2, [(2, 1), (13, 1), (467, 1), (9815479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_467
    · exact prime_9815479
  · decide +kernel

theorem prime_119179546141 : Nat.Prime 119179546141 := by
  apply nodeValid_prime [2, 3, 5, 1986325769] ⟨119179546141, 2, [(2, 2), (3, 1), (5, 1), (1986325769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1986325769
  · decide +kernel

theorem prime_119179550533 : Nat.Prime 119179550533 := by
  apply nodeValid_prime [2, 3, 7, 17, 4909357] ⟨119179550533, 5, [(2, 2), (3, 1), (7, 1), (17, 2), (4909357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_4909357
  · decide +kernel

theorem prime_119487926659 : Nat.Prime 119487926659 := by
  apply nodeValid_prime [2, 3, 23, 865854541] ⟨119487926659, 3, [(2, 1), (3, 1), (23, 1), (865854541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_865854541
  · decide +kernel

theorem prime_119487926821 : Nat.Prime 119487926821 := by
  apply nodeValid_prime [2, 3, 5, 1991465447] ⟨119487926821, 11, [(2, 2), (3, 1), (5, 1), (1991465447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1991465447
  · decide +kernel

theorem prime_119487930101 : Nat.Prime 119487930101 := by
  apply nodeValid_prime [2, 5, 7, 11, 751, 20663] ⟨119487930101, 2, [(2, 2), (5, 2), (7, 1), (11, 1), (751, 1), (20663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_751
    · exact prime_20663
  · decide +kernel

theorem prime_119796849149 : Nat.Prime 119796849149 := by
  apply nodeValid_prime [2, 43, 79, 1091, 8081] ⟨119796849149, 2, [(2, 2), (43, 1), (79, 1), (1091, 1), (8081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_79
    · exact prime_1091
    · exact prime_8081
  · decide +kernel

theorem prime_119796852269 : Nat.Prime 119796852269 := by
  apply nodeValid_prime [2, 37, 809438191] ⟨119796852269, 2, [(2, 2), (37, 1), (809438191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_809438191
  · decide +kernel

theorem prime_119796852619 : Nat.Prime 119796852619 := by
  apply nodeValid_prime [2, 3, 5261, 1265041] ⟨119796852619, 3, [(2, 1), (3, 2), (5261, 1), (1265041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5261
    · exact prime_1265041
  · decide +kernel

theorem prime_120106305541 : Nat.Prime 120106305541 := by
  apply nodeValid_prime [2, 3, 5, 13, 51327481] ⟨120106305541, 7, [(2, 2), (3, 2), (5, 1), (13, 1), (51327481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_51327481
  · decide +kernel

theorem prime_120106318627 : Nat.Prime 120106318627 := by
  apply nodeValid_prime [2, 3, 7, 29, 32869819] ⟨120106318627, 2, [(2, 1), (3, 2), (7, 1), (29, 1), (32869819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_32869819
  · decide +kernel

theorem prime_120416296051 : Nat.Prime 120416296051 := by
  apply nodeValid_prime [2, 3, 5, 67, 3993907] ⟨120416296051, 3, [(2, 1), (3, 2), (5, 2), (67, 1), (3993907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_3993907
  · decide +kernel

theorem prime_120416296337 : Nat.Prime 120416296337 := by
  apply nodeValid_prime [2, 7, 31, 34682113] ⟨120416296337, 3, [(2, 4), (7, 1), (31, 1), (34682113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_34682113
  · decide +kernel

theorem prime_120416299217 : Nat.Prime 120416299217 := by
  apply nodeValid_prime [2, 59, 127559639] ⟨120416299217, 3, [(2, 4), (59, 1), (127559639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_127559639
  · decide +kernel

theorem prime_120726832159 : Nat.Prime 120726832159 := by
  apply nodeValid_prime [2, 3, 397, 1877147] ⟨120726832159, 3, [(2, 1), (3, 4), (397, 1), (1877147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_1877147
  · decide +kernel

theorem prime_120726837017 : Nat.Prime 120726837017 := by
  apply nodeValid_prime [2, 17, 5839, 152029] ⟨120726837017, 3, [(2, 3), (17, 1), (5839, 1), (152029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_5839
    · exact prime_152029
  · decide +kernel

theorem prime_120726837403 : Nat.Prime 120726837403 := by
  apply nodeValid_prime [2, 3, 61, 329854747] ⟨120726837403, 2, [(2, 1), (3, 1), (61, 1), (329854747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_329854747
  · decide +kernel

theorem prime_121037898329 : Nat.Prime 121037898329 := by
  apply nodeValid_prime [2, 29, 521715079] ⟨121037898329, 3, [(2, 3), (29, 1), (521715079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_521715079
  · decide +kernel

theorem prime_121037900119 : Nat.Prime 121037900119 := by
  apply nodeValid_prime [2, 3, 2203, 9157051] ⟨121037900119, 3, [(2, 1), (3, 1), (2203, 1), (9157051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2203
    · exact prime_9157051
  · decide +kernel

theorem prime_121037907737 : Nat.Prime 121037907737 := by
  apply nodeValid_prime [2, 7457, 2028931] ⟨121037907737, 3, [(2, 3), (7457, 1), (2028931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7457
    · exact prime_2028931
  · decide +kernel

theorem prime_121349527183 : Nat.Prime 121349527183 := by
  apply nodeValid_prime [2, 3, 13, 518587723] ⟨121349527183, 11, [(2, 1), (3, 2), (13, 1), (518587723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_518587723
  · decide +kernel

theorem prime_121349560679 : Nat.Prime 121349560679 := by
  apply nodeValid_prime [2, 60674780339] ⟨121349560679, 7, [(2, 1), (60674780339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60674780339
  · decide +kernel

theorem prime_121349561173 : Nat.Prime 121349561173 := by
  apply nodeValid_prime [2, 3, 7, 1444637633] ⟨121349561173, 2, [(2, 2), (3, 1), (7, 1), (1444637633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1444637633
  · decide +kernel

theorem prime_121661666221 : Nat.Prime 121661666221 := by
  apply nodeValid_prime [2, 3, 5, 2027694437] ⟨121661666221, 2, [(2, 2), (3, 1), (5, 1), (2027694437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2027694437
  · decide +kernel

theorem prime_121661666299 : Nat.Prime 121661666299 := by
  apply nodeValid_prime [2, 3, 173, 271, 144167] ⟨121661666299, 2, [(2, 1), (3, 2), (173, 1), (271, 1), (144167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_271
    · exact prime_144167
  · decide +kernel

theorem prime_121661691491 : Nat.Prime 121661691491 := by
  apply nodeValid_prime [2, 5, 4297, 2831317] ⟨121661691491, 2, [(2, 1), (5, 1), (4297, 1), (2831317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4297
    · exact prime_2831317
  · decide +kernel

theorem prime_121974401641 : Nat.Prime 121974401641 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 967, 11551] ⟨121974401641, 17, [(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (967, 1), (11551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_967
    · exact prime_11551
  · decide +kernel

theorem prime_121974414641 : Nat.Prime 121974414641 := by
  apply nodeValid_prime [2, 5, 13, 59, 1987849] ⟨121974414641, 3, [(2, 4), (5, 1), (13, 1), (59, 1), (1987849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_59
    · exact prime_1987849
  · decide +kernel

theorem prime_121974415049 : Nat.Prime 121974415049 := by
  apply nodeValid_prime [2, 29, 3137, 167597] ⟨121974415049, 3, [(2, 3), (29, 1), (3137, 1), (167597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3137
    · exact prime_167597
  · decide +kernel

theorem prime_122287654481 : Nat.Prime 122287654481 := by
  apply nodeValid_prime [2, 5, 17, 5623, 15991] ⟨122287654481, 3, [(2, 4), (5, 1), (17, 1), (5623, 1), (15991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_5623
    · exact prime_15991
  · decide +kernel

theorem prime_122287656499 : Nat.Prime 122287656499 := by
  apply nodeValid_prime [2, 3, 7, 439, 1913, 3467] ⟨122287656499, 3, [(2, 1), (3, 1), (7, 1), (439, 1), (1913, 1), (3467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_439
    · exact prime_1913
    · exact prime_3467
  · decide +kernel

theorem prime_122601440971 : Nat.Prime 122601440971 := by
  apply nodeValid_prime [2, 3, 5, 971, 467641] ⟨122601440971, 7, [(2, 1), (3, 3), (5, 1), (971, 1), (467641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_971
    · exact prime_467641
  · decide +kernel

theorem prime_122601441077 : Nat.Prime 122601441077 := by
  apply nodeValid_prime [2, 31, 491, 953, 2113] ⟨122601441077, 2, [(2, 2), (31, 1), (491, 1), (953, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_491
    · exact prime_953
    · exact prime_2113
  · decide +kernel

theorem prime_122601455257 : Nat.Prime 122601455257 := by
  apply nodeValid_prime [2, 3, 7, 729770567] ⟨122601455257, 5, [(2, 3), (3, 1), (7, 1), (729770567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_729770567
  · decide +kernel

theorem prime_122915793251 : Nat.Prime 122915793251 := by
  apply nodeValid_prime [2, 5, 349, 757, 1861] ⟨122915793251, 2, [(2, 1), (5, 3), (349, 1), (757, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
    · exact prime_757
    · exact prime_1861
  · decide +kernel

theorem prime_122915793419 : Nat.Prime 122915793419 := by
  apply nodeValid_prime [2, 11, 71, 557, 141277] ⟨122915793419, 2, [(2, 1), (11, 1), (71, 1), (557, 1), (141277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_557
    · exact prime_141277
  · decide +kernel

theorem prime_122915802949 : Nat.Prime 122915802949 := by
  apply nodeValid_prime [2, 3, 101, 367, 276337] ⟨122915802949, 2, [(2, 2), (3, 1), (101, 1), (367, 1), (276337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_367
    · exact prime_276337
  · decide +kernel

theorem prime_123230698379 : Nat.Prime 123230698379 := by
  apply nodeValid_prime [2, 7247, 8502187] ⟨123230698379, 2, [(2, 1), (7247, 1), (8502187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7247
    · exact prime_8502187
  · decide +kernel

theorem prime_123230699981 : Nat.Prime 123230699981 := by
  apply nodeValid_prime [2, 5, 10223, 602713] ⟨123230699981, 2, [(2, 2), (5, 1), (10223, 1), (602713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10223
    · exact prime_602713
  · decide +kernel

theorem prime_123230700893 : Nat.Prime 123230700893 := by
  apply nodeValid_prime [2, 13, 53, 44713607] ⟨123230700893, 2, [(2, 2), (13, 1), (53, 1), (44713607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_44713607
  · decide +kernel

theorem prime_123546133771 : Nat.Prime 123546133771 := by
  apply nodeValid_prime [2, 3, 5, 239, 17230981] ⟨123546133771, 2, [(2, 1), (3, 1), (5, 1), (239, 1), (17230981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239
    · exact prime_17230981
  · decide +kernel

theorem prime_123546179833 : Nat.Prime 123546179833 := by
  apply nodeValid_prime [2, 3, 59, 839, 103993] ⟨123546179833, 5, [(2, 3), (3, 1), (59, 1), (839, 1), (103993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_839
    · exact prime_103993
  · decide +kernel

theorem prime_123546179971 : Nat.Prime 123546179971 := by
  apply nodeValid_prime [2, 3, 5, 449, 3057317] ⟨123546179971, 10, [(2, 1), (3, 2), (5, 1), (449, 1), (3057317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_449
    · exact prime_3057317
  · decide +kernel

theorem prime_123862104721 : Nat.Prime 123862104721 := by
  apply nodeValid_prime [2, 3, 5, 17, 3373151] ⟨123862104721, 14, [(2, 4), (3, 3), (5, 1), (17, 1), (3373151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_3373151
  · decide +kernel

theorem prime_123862106003 : Nat.Prime 123862106003 := by
  apply nodeValid_prime [2, 61931053001] ⟨123862106003, 2, [(2, 1), (61931053001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61931053001
  · decide +kernel

theorem prime_123862110937 : Nat.Prime 123862110937 := by
  apply nodeValid_prime [2, 3, 41, 269, 467941] ⟨123862110937, 5, [(2, 3), (3, 1), (41, 1), (269, 1), (467941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_269
    · exact prime_467941
  · decide +kernel

end Sude.Lucas.Generated
