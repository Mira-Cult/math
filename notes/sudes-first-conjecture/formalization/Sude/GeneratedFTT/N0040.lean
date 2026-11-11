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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2579 : Nat.Prime 2579 := by
  apply nodeValid_prime [2, 1289] ⟨2579, 2, [(2, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1289
  · decide +kernel

theorem prime_3221 : Nat.Prime 3221 := by
  apply nodeValid_prime [2, 5, 7, 23] ⟨3221, 10, [(2, 2), (5, 1), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_4157 : Nat.Prime 4157 := by
  apply nodeValid_prime [2, 1039] ⟨4157, 2, [(2, 2), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1039
  · decide +kernel

theorem prime_6653 : Nat.Prime 6653 := by
  apply nodeValid_prime [2, 1663] ⟨6653, 2, [(2, 2), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1663
  · decide +kernel

theorem prime_8053 : Nat.Prime 8053 := by
  apply nodeValid_prime [2, 3, 11, 61] ⟨8053, 2, [(2, 2), (3, 1), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_8719 : Nat.Prime 8719 := by
  apply nodeValid_prime [2, 3, 1453] ⟨8719, 3, [(2, 1), (3, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1453
  · decide +kernel

theorem prime_9403 : Nat.Prime 9403 := by
  apply nodeValid_prime [2, 3, 1567] ⟨9403, 3, [(2, 1), (3, 1), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1567
  · decide +kernel

theorem prime_9631 : Nat.Prime 9631 := by
  apply nodeValid_prime [2, 3, 5, 107] ⟨9631, 3, [(2, 1), (3, 2), (5, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_9851 : Nat.Prime 9851 := by
  apply nodeValid_prime [2, 5, 197] ⟨9851, 2, [(2, 1), (5, 2), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
  · decide +kernel

theorem prime_10501 : Nat.Prime 10501 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨10501, 2, [(2, 2), (3, 1), (5, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_10771 : Nat.Prime 10771 := by
  apply nodeValid_prime [2, 3, 5, 359] ⟨10771, 3, [(2, 1), (3, 1), (5, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_359
  · decide +kernel

theorem prime_11527 : Nat.Prime 11527 := by
  apply nodeValid_prime [2, 3, 17, 113] ⟨11527, 5, [(2, 1), (3, 1), (17, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_113
  · decide +kernel

theorem prime_12049 : Nat.Prime 12049 := by
  apply nodeValid_prime [2, 3, 251] ⟨12049, 13, [(2, 4), (3, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
  · decide +kernel

theorem prime_13339 : Nat.Prime 13339 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨13339, 2, [(2, 1), (3, 3), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_14243 : Nat.Prime 14243 := by
  apply nodeValid_prime [2, 7121] ⟨14243, 2, [(2, 1), (7121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7121
  · decide +kernel

theorem prime_14347 : Nat.Prime 14347 := by
  apply nodeValid_prime [2, 3, 797] ⟨14347, 3, [(2, 1), (3, 2), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_797
  · decide +kernel

theorem prime_18043 : Nat.Prime 18043 := by
  apply nodeValid_prime [2, 3, 31, 97] ⟨18043, 2, [(2, 1), (3, 1), (31, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_97
  · decide +kernel

theorem prime_18301 : Nat.Prime 18301 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨18301, 6, [(2, 2), (3, 1), (5, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_18859 : Nat.Prime 18859 := by
  apply nodeValid_prime [2, 3, 7, 449] ⟨18859, 2, [(2, 1), (3, 1), (7, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_449
  · decide +kernel

theorem prime_23801 : Nat.Prime 23801 := by
  apply nodeValid_prime [2, 5, 7, 17] ⟨23801, 3, [(2, 3), (5, 2), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_24763 : Nat.Prime 24763 := by
  apply nodeValid_prime [2, 3, 4127] ⟨24763, 2, [(2, 1), (3, 1), (4127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4127
  · decide +kernel

theorem prime_27551 : Nat.Prime 27551 := by
  apply nodeValid_prime [2, 5, 19, 29] ⟨27551, 17, [(2, 1), (5, 2), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_28573 : Nat.Prime 28573 := by
  apply nodeValid_prime [2, 3, 2381] ⟨28573, 2, [(2, 2), (3, 1), (2381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2381
  · decide +kernel

theorem prime_28867 : Nat.Prime 28867 := by
  apply nodeValid_prime [2, 3, 17, 283] ⟨28867, 3, [(2, 1), (3, 1), (17, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_283
  · decide +kernel

theorem prime_29077 : Nat.Prime 29077 := by
  apply nodeValid_prime [2, 3, 2423] ⟨29077, 2, [(2, 2), (3, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2423
  · decide +kernel

theorem prime_29243 : Nat.Prime 29243 := by
  apply nodeValid_prime [2, 14621] ⟨29243, 2, [(2, 1), (14621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14621
  · decide +kernel

theorem prime_31699 : Nat.Prime 31699 := by
  apply nodeValid_prime [2, 3, 587] ⟨31699, 2, [(2, 1), (3, 3), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_587
  · decide +kernel

theorem prime_32213 : Nat.Prime 32213 := by
  apply nodeValid_prime [2, 8053] ⟨32213, 2, [(2, 2), (8053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8053
  · decide +kernel

theorem prime_32251 : Nat.Prime 32251 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨32251, 3, [(2, 1), (3, 1), (5, 3), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_34807 : Nat.Prime 34807 := by
  apply nodeValid_prime [2, 3, 5801] ⟨34807, 3, [(2, 1), (3, 1), (5801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5801
  · decide +kernel

theorem prime_39569 : Nat.Prime 39569 := by
  apply nodeValid_prime [2, 2473] ⟨39569, 3, [(2, 4), (2473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2473
  · decide +kernel

theorem prime_41057 : Nat.Prime 41057 := by
  apply nodeValid_prime [2, 1283] ⟨41057, 3, [(2, 5), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1283
  · decide +kernel

theorem prime_41257 : Nat.Prime 41257 := by
  apply nodeValid_prime [2, 3, 191] ⟨41257, 5, [(2, 3), (3, 3), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
  · decide +kernel

theorem prime_43313 : Nat.Prime 43313 := by
  apply nodeValid_prime [2, 2707] ⟨43313, 3, [(2, 4), (2707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2707
  · decide +kernel

theorem prime_44381 : Nat.Prime 44381 := by
  apply nodeValid_prime [2, 5, 7, 317] ⟨44381, 2, [(2, 2), (5, 1), (7, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_317
  · decide +kernel

theorem prime_53549 : Nat.Prime 53549 := by
  apply nodeValid_prime [2, 11, 1217] ⟨53549, 2, [(2, 2), (11, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1217
  · decide +kernel

theorem prime_62627 : Nat.Prime 62627 := by
  apply nodeValid_prime [2, 173, 181] ⟨62627, 2, [(2, 1), (173, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_181
  · decide +kernel

theorem prime_65563 : Nat.Prime 65563 := by
  apply nodeValid_prime [2, 3, 7, 223] ⟨65563, 3, [(2, 1), (3, 1), (7, 2), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_223
  · decide +kernel

theorem prime_70237 : Nat.Prime 70237 := by
  apply nodeValid_prime [2, 3, 1951] ⟨70237, 2, [(2, 2), (3, 2), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1951
  · decide +kernel

theorem prime_72173 : Nat.Prime 72173 := by
  apply nodeValid_prime [2, 18043] ⟨72173, 2, [(2, 2), (18043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18043
  · decide +kernel

theorem prime_72973 : Nat.Prime 72973 := by
  apply nodeValid_prime [2, 3, 2027] ⟨72973, 2, [(2, 2), (3, 2), (2027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2027
  · decide +kernel

theorem prime_79829 : Nat.Prime 79829 := by
  apply nodeValid_prime [2, 7, 2851] ⟨79829, 2, [(2, 2), (7, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2851
  · decide +kernel

theorem prime_91867 : Nat.Prime 91867 := by
  apply nodeValid_prime [2, 3, 61, 251] ⟨91867, 2, [(2, 1), (3, 1), (61, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_251
  · decide +kernel

theorem prime_107099 : Nat.Prime 107099 := by
  apply nodeValid_prime [2, 53549] ⟨107099, 2, [(2, 1), (53549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53549
  · decide +kernel

theorem prime_135319 : Nat.Prime 135319 := by
  apply nodeValid_prime [2, 3, 19, 1187] ⟨135319, 6, [(2, 1), (3, 1), (19, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1187
  · decide +kernel

theorem prime_154991 : Nat.Prime 154991 := by
  apply nodeValid_prime [2, 5, 11, 1409] ⟨154991, 11, [(2, 1), (5, 1), (11, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1409
  · decide +kernel

theorem prime_169553 : Nat.Prime 169553 := by
  apply nodeValid_prime [2, 10597] ⟨169553, 3, [(2, 4), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10597
  · decide +kernel

theorem prime_170263 : Nat.Prime 170263 := by
  apply nodeValid_prime [2, 3, 1051] ⟨170263, 3, [(2, 1), (3, 4), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1051
  · decide +kernel

theorem prime_171439 : Nat.Prime 171439 := by
  apply nodeValid_prime [2, 3, 28573] ⟨171439, 3, [(2, 1), (3, 1), (28573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28573
  · decide +kernel

theorem prime_185327 : Nat.Prime 185327 := by
  apply nodeValid_prime [2, 19, 4877] ⟨185327, 5, [(2, 1), (19, 1), (4877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4877
  · decide +kernel

theorem prime_188389 : Nat.Prime 188389 := by
  apply nodeValid_prime [2, 3, 5233] ⟨188389, 2, [(2, 2), (3, 2), (5233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5233
  · decide +kernel

theorem prime_200579 : Nat.Prime 200579 := by
  apply nodeValid_prime [2, 7, 14327] ⟨200579, 2, [(2, 1), (7, 1), (14327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_14327
  · decide +kernel

theorem prime_205441 : Nat.Prime 205441 := by
  apply nodeValid_prime [2, 3, 5, 107] ⟨205441, 13, [(2, 7), (3, 1), (5, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_219613 : Nat.Prime 219613 := by
  apply nodeValid_prime [2, 3, 18301] ⟨219613, 6, [(2, 2), (3, 1), (18301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18301
  · decide +kernel

theorem prime_221461 : Nat.Prime 221461 := by
  apply nodeValid_prime [2, 3, 5, 3691] ⟨221461, 2, [(2, 2), (3, 1), (5, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3691
  · decide +kernel

theorem prime_229553 : Nat.Prime 229553 := by
  apply nodeValid_prime [2, 14347] ⟨229553, 3, [(2, 4), (14347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14347
  · decide +kernel

theorem prime_256567 : Nat.Prime 256567 := by
  apply nodeValid_prime [2, 3, 61, 701] ⟨256567, 3, [(2, 1), (3, 1), (61, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_701
  · decide +kernel

theorem prime_272171 : Nat.Prime 272171 := by
  apply nodeValid_prime [2, 5, 17, 1601] ⟨272171, 2, [(2, 1), (5, 1), (17, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1601
  · decide +kernel

theorem prime_285613 : Nat.Prime 285613 := by
  apply nodeValid_prime [2, 3, 23801] ⟨285613, 2, [(2, 2), (3, 1), (23801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23801
  · decide +kernel

theorem prime_287167 : Nat.Prime 287167 := by
  apply nodeValid_prime [2, 3, 11, 19, 229] ⟨287167, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_229
  · decide +kernel

theorem prime_355049 : Nat.Prime 355049 := by
  apply nodeValid_prime [2, 44381] ⟨355049, 3, [(2, 3), (44381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44381
  · decide +kernel

theorem prime_380753 : Nat.Prime 380753 := by
  apply nodeValid_prime [2, 53, 449] ⟨380753, 3, [(2, 4), (53, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_449
  · decide +kernel

theorem prime_412571 : Nat.Prime 412571 := by
  apply nodeValid_prime [2, 5, 41257] ⟨412571, 2, [(2, 1), (5, 1), (41257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41257
  · decide +kernel

theorem prime_469457 : Nat.Prime 469457 := by
  apply nodeValid_prime [2, 13, 37, 61] ⟨469457, 3, [(2, 4), (13, 1), (37, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_61
  · decide +kernel

theorem prime_489871 : Nat.Prime 489871 := by
  apply nodeValid_prime [2, 3, 5, 5443] ⟨489871, 6, [(2, 1), (3, 2), (5, 1), (5443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5443
  · decide +kernel

theorem prime_557761 : Nat.Prime 557761 := by
  apply nodeValid_prime [2, 3, 5, 7, 83] ⟨557761, 11, [(2, 6), (3, 1), (5, 1), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_558017 : Nat.Prime 558017 := by
  apply nodeValid_prime [2, 8719] ⟨558017, 3, [(2, 6), (8719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8719
  · decide +kernel

theorem prime_591061 : Nat.Prime 591061 := by
  apply nodeValid_prime [2, 3, 5, 9851] ⟨591061, 23, [(2, 2), (3, 1), (5, 1), (9851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9851
  · decide +kernel

theorem prime_627733 : Nat.Prime 627733 := by
  apply nodeValid_prime [2, 3, 7, 47, 53] ⟨627733, 2, [(2, 2), (3, 2), (7, 1), (47, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_53
  · decide +kernel

theorem prime_638689 : Nat.Prime 638689 := by
  apply nodeValid_prime [2, 3, 6653] ⟨638689, 31, [(2, 5), (3, 1), (6653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6653
  · decide +kernel

theorem prime_697913 : Nat.Prime 697913 := by
  apply nodeValid_prime [2, 23, 3793] ⟨697913, 3, [(2, 3), (23, 1), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3793
  · decide +kernel

theorem prime_877291 : Nat.Prime 877291 := by
  apply nodeValid_prime [2, 3, 5, 29243] ⟨877291, 3, [(2, 1), (3, 1), (5, 1), (29243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29243
  · decide +kernel

theorem prime_878453 : Nat.Prime 878453 := by
  apply nodeValid_prime [2, 219613] ⟨878453, 2, [(2, 2), (219613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_219613
  · decide +kernel

theorem prime_922217 : Nat.Prime 922217 := by
  apply nodeValid_prime [2, 17, 6781] ⟨922217, 3, [(2, 3), (17, 1), (6781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_6781
  · decide +kernel

theorem prime_952709 : Nat.Prime 952709 := by
  apply nodeValid_prime [2, 29, 43, 191] ⟨952709, 2, [(2, 2), (29, 1), (43, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_43
    · exact prime_191
  · decide +kernel

theorem prime_1217521 : Nat.Prime 1217521 := by
  apply nodeValid_prime [2, 3, 5, 19, 89] ⟨1217521, 11, [(2, 4), (3, 2), (5, 1), (19, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_89
  · decide +kernel

theorem prime_1426489 : Nat.Prime 1426489 := by
  apply nodeValid_prime [2, 3, 7, 1213] ⟨1426489, 29, [(2, 3), (3, 1), (7, 2), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1213
  · decide +kernel

theorem prime_1816051 : Nat.Prime 1816051 := by
  apply nodeValid_prime [2, 3, 5, 12107] ⟨1816051, 2, [(2, 1), (3, 1), (5, 2), (12107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12107
  · decide +kernel

theorem prime_2824319 : Nat.Prime 2824319 := by
  apply nodeValid_prime [2, 7, 67, 3011] ⟨2824319, 7, [(2, 1), (7, 1), (67, 1), (3011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_3011
  · decide +kernel

theorem prime_3435577 : Nat.Prime 3435577 := by
  apply nodeValid_prime [2, 3, 257, 557] ⟨3435577, 5, [(2, 3), (3, 1), (257, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_557
  · decide +kernel

theorem prime_3633347 : Nat.Prime 3633347 := by
  apply nodeValid_prime [2, 173, 10501] ⟨3633347, 2, [(2, 1), (173, 1), (10501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_10501
  · decide +kernel

theorem prime_3672283 : Nat.Prime 3672283 := by
  apply nodeValid_prime [2, 3, 19, 32213] ⟨3672283, 2, [(2, 1), (3, 1), (19, 1), (32213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_32213
  · decide +kernel

theorem prime_3954707 : Nat.Prime 3954707 := by
  apply nodeValid_prime [2, 7, 163, 1733] ⟨3954707, 2, [(2, 1), (7, 1), (163, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163
    · exact prime_1733
  · decide +kernel

theorem prime_6315251 : Nat.Prime 6315251 := by
  apply nodeValid_prime [2, 5, 25261] ⟨6315251, 2, [(2, 1), (5, 3), (25261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25261
  · decide +kernel

theorem prime_6693133 : Nat.Prime 6693133 := by
  apply nodeValid_prime [2, 3, 557761] ⟨6693133, 5, [(2, 2), (3, 1), (557761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557761
  · decide +kernel

theorem prime_7613209 : Nat.Prime 7613209 := by
  apply nodeValid_prime [2, 3, 41, 2579] ⟨7613209, 11, [(2, 3), (3, 2), (41, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2579
  · decide +kernel

theorem prime_7621673 : Nat.Prime 7621673 := by
  apply nodeValid_prime [2, 952709] ⟨7621673, 3, [(2, 3), (952709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_952709
  · decide +kernel

theorem prime_8626043 : Nat.Prime 8626043 := by
  apply nodeValid_prime [2, 109, 39569] ⟨8626043, 2, [(2, 1), (109, 1), (39569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_39569
  · decide +kernel

theorem prime_14400877 : Nat.Prime 14400877 := by
  apply nodeValid_prime [2, 3, 7, 171439] ⟨14400877, 5, [(2, 2), (3, 1), (7, 1), (171439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_171439
  · decide +kernel

theorem prime_14508443 : Nat.Prime 14508443 := by
  apply nodeValid_prime [2, 13, 558017] ⟨14508443, 5, [(2, 1), (13, 1), (558017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_558017
  · decide +kernel

theorem prime_15532511 : Nat.Prime 15532511 := by
  apply nodeValid_prime [2, 5, 7, 31699] ⟨15532511, 7, [(2, 1), (5, 1), (7, 2), (31699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31699
  · decide +kernel

theorem prime_16063009 : Nat.Prime 16063009 := by
  apply nodeValid_prime [2, 3, 13, 61, 211] ⟨16063009, 19, [(2, 5), (3, 1), (13, 1), (61, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
    · exact prime_211
  · decide +kernel

theorem prime_16521881 : Nat.Prime 16521881 := by
  apply nodeValid_prime [2, 5, 29, 14243] ⟨16521881, 3, [(2, 3), (5, 1), (29, 1), (14243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_14243
  · decide +kernel

theorem prime_17252087 : Nat.Prime 17252087 := by
  apply nodeValid_prime [2, 8626043] ⟨17252087, 5, [(2, 1), (8626043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8626043
  · decide +kernel

theorem prime_20027213 : Nat.Prime 20027213 := by
  apply nodeValid_prime [2, 37, 135319] ⟨20027213, 2, [(2, 2), (37, 1), (135319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_135319
  · decide +kernel

theorem prime_20984461 : Nat.Prime 20984461 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 2939] ⟨20984461, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (2939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_2939
  · decide +kernel

theorem prime_30452837 : Nat.Prime 30452837 := by
  apply nodeValid_prime [2, 7613209] ⟨30452837, 2, [(2, 2), (7613209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7613209
  · decide +kernel

theorem prime_39731179 : Nat.Prime 39731179 := by
  apply nodeValid_prime [2, 3, 101, 65563] ⟨39731179, 11, [(2, 1), (3, 1), (101, 1), (65563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_65563
  · decide +kernel

theorem prime_43033961 : Nat.Prime 43033961 := by
  apply nodeValid_prime [2, 5, 37, 29077] ⟨43033961, 3, [(2, 3), (5, 1), (37, 1), (29077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_29077
  · decide +kernel

theorem prime_43822351 : Nat.Prime 43822351 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 227] ⟨43822351, 3, [(2, 1), (3, 3), (5, 2), (11, 1), (13, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_227
  · decide +kernel

theorem prime_44298119 : Nat.Prime 44298119 := by
  apply nodeValid_prime [2, 4337, 5107] ⟨44298119, 13, [(2, 1), (4337, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4337
    · exact prime_5107
  · decide +kernel

theorem prime_49817743 : Nat.Prime 49817743 := by
  apply nodeValid_prime [2, 3, 13, 638689] ⟨49817743, 5, [(2, 1), (3, 1), (13, 1), (638689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_638689
  · decide +kernel

theorem prime_61071331 : Nat.Prime 61071331 := by
  apply nodeValid_prime [2, 3, 5, 47, 43313] ⟨61071331, 2, [(2, 1), (3, 1), (5, 1), (47, 1), (43313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_43313
  · decide +kernel

theorem prime_103512523 : Nat.Prime 103512523 := by
  apply nodeValid_prime [2, 3, 17252087] ⟨103512523, 5, [(2, 1), (3, 1), (17252087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17252087
  · decide +kernel

theorem prime_129587273 : Nat.Prime 129587273 := by
  apply nodeValid_prime [2, 47, 107, 3221] ⟨129587273, 3, [(2, 3), (47, 1), (107, 1), (3221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_107
    · exact prime_3221
  · decide +kernel

theorem prime_149055463 : Nat.Prime 149055463 := by
  apply nodeValid_prime [2, 3, 37, 79, 2833] ⟨149055463, 6, [(2, 1), (3, 2), (37, 1), (79, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_79
    · exact prime_2833
  · decide +kernel

theorem prime_206770457 : Nat.Prime 206770457 := by
  apply nodeValid_prime [2, 17, 59, 73, 353] ⟨206770457, 3, [(2, 3), (17, 1), (59, 1), (73, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
    · exact prime_73
    · exact prime_353
  · decide +kernel

theorem prime_257263163 : Nat.Prime 257263163 := by
  apply nodeValid_prime [2, 13, 241, 41057] ⟨257263163, 2, [(2, 1), (13, 1), (241, 1), (41057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_241
    · exact prime_41057
  · decide +kernel

theorem prime_258203767 : Nat.Prime 258203767 := by
  apply nodeValid_prime [2, 3, 43033961] ⟨258203767, 5, [(2, 1), (3, 1), (43033961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43033961
  · decide +kernel

theorem prime_375599563 : Nat.Prime 375599563 := by
  apply nodeValid_prime [2, 3, 13, 19, 13339] ⟨375599563, 2, [(2, 1), (3, 1), (13, 1), (19, 2), (13339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_13339
  · decide +kernel

theorem prime_462707659 : Nat.Prime 462707659 := by
  apply nodeValid_prime [2, 3, 7, 3672283] ⟨462707659, 2, [(2, 1), (3, 2), (7, 1), (3672283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3672283
  · decide +kernel

theorem prime_498177431 : Nat.Prime 498177431 := by
  apply nodeValid_prime [2, 5, 49817743] ⟨498177431, 13, [(2, 1), (5, 1), (49817743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49817743
  · decide +kernel

theorem prime_598932517 : Nat.Prime 598932517 := by
  apply nodeValid_prime [2, 3, 7, 13, 19, 28867] ⟨598932517, 6, [(2, 2), (3, 1), (7, 1), (13, 1), (19, 1), (28867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_28867
  · decide +kernel

theorem prime_825920987 : Nat.Prime 825920987 := by
  apply nodeValid_prime [2, 11, 29, 1009, 1283] ⟨825920987, 5, [(2, 1), (11, 1), (29, 1), (1009, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_1009
    · exact prime_1283
  · decide +kernel

theorem prime_837113401 : Nat.Prime 837113401 := by
  apply nodeValid_prime [2, 3, 5, 19, 41, 199] ⟨837113401, 7, [(2, 3), (3, 3), (5, 2), (19, 1), (41, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_199
  · decide +kernel

theorem prime_874085939 : Nat.Prime 874085939 := by
  apply nodeValid_prime [2, 11, 39731179] ⟨874085939, 2, [(2, 1), (11, 1), (39731179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_39731179
  · decide +kernel

theorem prime_1551359377 : Nat.Prime 1551359377 := by
  apply nodeValid_prime [2, 3, 7, 827, 1861] ⟨1551359377, 10, [(2, 4), (3, 2), (7, 1), (827, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_827
    · exact prime_1861
  · decide +kernel

theorem prime_2016767191 : Nat.Prime 2016767191 := by
  apply nodeValid_prime [2, 3, 5, 23, 953, 3067] ⟨2016767191, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (953, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_953
    · exact prime_3067
  · decide +kernel

theorem prime_4955525923 : Nat.Prime 4955525923 := by
  apply nodeValid_prime [2, 3, 825920987] ⟨4955525923, 2, [(2, 1), (3, 1), (825920987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_825920987
  · decide +kernel

theorem prime_4994669353 : Nat.Prime 4994669353 := by
  apply nodeValid_prime [2, 3, 359, 661, 877] ⟨4994669353, 5, [(2, 3), (3, 1), (359, 1), (661, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_661
    · exact prime_877
  · decide +kernel

theorem prime_19978677413 : Nat.Prime 19978677413 := by
  apply nodeValid_prime [2, 4994669353] ⟨19978677413, 2, [(2, 2), (4994669353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4994669353
  · decide +kernel

theorem prime_25829156893 : Nat.Prime 25829156893 := by
  apply nodeValid_prime [2, 3, 7, 11, 257, 108769] ⟨25829156893, 5, [(2, 2), (3, 1), (7, 1), (11, 1), (257, 1), (108769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_257
    · exact prime_108769
  · decide +kernel

theorem prime_30640466839 : Nat.Prime 30640466839 := by
  apply nodeValid_prime [2, 3, 29, 647, 272171] ⟨30640466839, 6, [(2, 1), (3, 1), (29, 1), (647, 1), (272171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_647
    · exact prime_272171
  · decide +kernel

theorem prime_71363916971 : Nat.Prime 71363916971 := by
  apply nodeValid_prime [2, 5, 19, 375599563] ⟨71363916971, 2, [(2, 1), (5, 1), (19, 1), (375599563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_375599563
  · decide +kernel

theorem prime_277072412381 : Nat.Prime 277072412381 := by
  apply nodeValid_prime [2, 5, 67, 206770457] ⟨277072412381, 2, [(2, 2), (5, 1), (67, 1), (206770457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_206770457
  · decide +kernel

theorem prime_279701483783 : Nat.Prime 279701483783 := by
  apply nodeValid_prime [2, 7, 19978677413] ⟨279701483783, 7, [(2, 1), (7, 1), (19978677413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19978677413
  · decide +kernel

theorem prime_551528389957 : Nat.Prime 551528389957 := by
  apply nodeValid_prime [2, 3, 17, 113, 127, 188389] ⟨551528389957, 2, [(2, 2), (3, 1), (17, 1), (113, 1), (127, 1), (188389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_113
    · exact prime_127
    · exact prime_188389
  · decide +kernel

theorem prime_551528400589 : Nat.Prime 551528400589 := by
  apply nodeValid_prime [2, 3, 11, 269, 15532511] ⟨551528400589, 2, [(2, 2), (3, 1), (11, 1), (269, 1), (15532511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_269
    · exact prime_15532511
  · decide +kernel

theorem prime_551528403103 : Nat.Prime 551528403103 := by
  apply nodeValid_prime [2, 3, 30640466839] ⟨551528403103, 3, [(2, 1), (3, 2), (30640466839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30640466839
  · decide +kernel

theorem prime_552399544493 : Nat.Prime 552399544493 := by
  apply nodeValid_prime [2, 191, 199, 3633347] ⟨552399544493, 2, [(2, 2), (191, 1), (199, 1), (3633347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_199
    · exact prime_3633347
  · decide +kernel

theorem prime_552399545879 : Nat.Prime 552399545879 := by
  apply nodeValid_prime [2, 17, 109, 149055463] ⟨552399545879, 11, [(2, 1), (17, 1), (109, 1), (149055463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_109
    · exact prime_149055463
  · decide +kernel

theorem prime_552399610207 : Nat.Prime 552399610207 := by
  apply nodeValid_prime [2, 3, 17, 18859, 287167] ⟨552399610207, 3, [(2, 1), (3, 1), (17, 1), (18859, 1), (287167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_18859
    · exact prime_287167
  · decide +kernel

theorem prime_553271763511 : Nat.Prime 553271763511 := by
  apply nodeValid_prime [2, 3, 5, 61, 1097, 91867] ⟨553271763511, 19, [(2, 1), (3, 2), (5, 1), (61, 1), (1097, 1), (91867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_1097
    · exact prime_91867
  · decide +kernel

theorem prime_553271785361 : Nat.Prime 553271785361 := by
  apply nodeValid_prime [2, 5, 7, 5827, 169553] ⟨553271785361, 3, [(2, 4), (5, 1), (7, 1), (5827, 1), (169553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_5827
    · exact prime_169553
  · decide +kernel

theorem prime_553271786339 : Nat.Prime 553271786339 := by
  apply nodeValid_prime [2, 19, 727, 20027213] ⟨553271786339, 2, [(2, 1), (19, 1), (727, 1), (20027213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_727
    · exact prime_20027213
  · decide +kernel

theorem prime_554144824763 : Nat.Prime 554144824763 := by
  apply nodeValid_prime [2, 277072412381] ⟨554144824763, 2, [(2, 1), (277072412381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_277072412381
  · decide +kernel

theorem prime_554144827793 : Nat.Prime 554144827793 := by
  apply nodeValid_prime [2, 17, 593, 3435577] ⟨554144827793, 3, [(2, 4), (17, 1), (593, 1), (3435577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_593
    · exact prime_3435577
  · decide +kernel

theorem prime_554144853103 : Nat.Prime 554144853103 := by
  apply nodeValid_prime [2, 3, 359, 257263163] ⟨554144853103, 3, [(2, 1), (3, 1), (359, 1), (257263163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_257263163
  · decide +kernel

theorem prime_555018871529 : Nat.Prime 555018871529 := by
  apply nodeValid_prime [2, 11, 257, 2129, 11527] ⟨555018871529, 3, [(2, 3), (11, 1), (257, 1), (2129, 1), (11527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_257
    · exact prime_2129
    · exact prime_11527
  · decide +kernel

theorem prime_555018903377 : Nat.Prime 555018903377 := by
  apply nodeValid_prime [2, 7, 4955525923] ⟨555018903377, 3, [(2, 4), (7, 1), (4955525923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4955525923
  · decide +kernel

theorem prime_555018903533 : Nat.Prime 555018903533 := by
  apply nodeValid_prime [2, 17, 103, 4373, 18121] ⟨555018903533, 3, [(2, 2), (17, 1), (103, 1), (4373, 1), (18121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
    · exact prime_4373
    · exact prime_18121
  · decide +kernel

theorem prime_555893762497 : Nat.Prime 555893762497 := by
  apply nodeValid_prime [2, 3, 17, 829, 205441] ⟨555893762497, 5, [(2, 6), (3, 1), (17, 1), (829, 1), (205441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_829
    · exact prime_205441
  · decide +kernel

theorem prime_555893762857 : Nat.Prime 555893762857 := by
  apply nodeValid_prime [2, 3, 59, 139, 2824319] ⟨555893762857, 10, [(2, 3), (3, 1), (59, 1), (139, 1), (2824319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_139
    · exact prime_2824319
  · decide +kernel

theorem prime_555893820421 : Nat.Prime 555893820421 := by
  apply nodeValid_prime [2, 3, 5, 23, 113, 154991] ⟨555893820421, 6, [(2, 2), (3, 1), (5, 1), (23, 2), (113, 1), (154991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_113
    · exact prime_154991
  · decide +kernel

theorem prime_556769686751 : Nat.Prime 556769686751 := by
  apply nodeValid_prime [2, 5, 43, 827, 62627] ⟨556769686751, 17, [(2, 1), (5, 3), (43, 1), (827, 1), (62627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_827
    · exact prime_62627
  · decide +kernel

theorem prime_556769687293 : Nat.Prime 556769687293 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 137, 72973] ⟨556769687293, 5, [(2, 2), (3, 2), (7, 1), (13, 1), (17, 1), (137, 1), (72973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_137
    · exact prime_72973
  · decide +kernel

theorem prime_556769706593 : Nat.Prime 556769706593 := by
  apply nodeValid_prime [2, 11, 19, 59, 131, 10771] ⟨556769706593, 3, [(2, 5), (11, 1), (19, 1), (59, 1), (131, 1), (10771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_59
    · exact prime_131
    · exact prime_10771
  · decide +kernel

theorem prime_557646514987 : Nat.Prime 557646514987 := by
  apply nodeValid_prime [2, 3, 11, 9631, 877291] ⟨557646514987, 2, [(2, 1), (3, 1), (11, 1), (9631, 1), (877291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9631
    · exact prime_877291
  · decide +kernel

theorem prime_557646515149 : Nat.Prime 557646515149 := by
  apply nodeValid_prime [2, 3, 3203, 14508443] ⟨557646515149, 2, [(2, 2), (3, 1), (3203, 1), (14508443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3203
    · exact prime_14508443
  · decide +kernel

theorem prime_557646527513 : Nat.Prime 557646527513 := by
  apply nodeValid_prime [2, 4219, 16521881] ⟨557646527513, 3, [(2, 3), (4219, 1), (16521881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4219
    · exact prime_16521881
  · decide +kernel

theorem prime_558524259869 : Nat.Prime 558524259869 := by
  apply nodeValid_prime [2, 43, 6917, 469457] ⟨558524259869, 2, [(2, 2), (43, 1), (6917, 1), (469457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_6917
    · exact prime_469457
  · decide +kernel

theorem prime_558524260241 : Nat.Prime 558524260241 := by
  apply nodeValid_prime [2, 5, 34807, 200579] ⟨558524260241, 3, [(2, 4), (5, 1), (34807, 1), (200579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_34807
    · exact prime_200579
  · decide +kernel

theorem prime_558524275207 : Nat.Prime 558524275207 := by
  apply nodeValid_prime [2, 3, 89, 6143, 170263] ⟨558524275207, 3, [(2, 1), (3, 1), (89, 1), (6143, 1), (170263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_6143
    · exact prime_170263
  · decide +kernel

theorem prime_559402963127 : Nat.Prime 559402963127 := by
  apply nodeValid_prime [2, 7, 23, 24071, 72173] ⟨559402963127, 5, [(2, 1), (7, 1), (23, 1), (24071, 1), (72173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_24071
    · exact prime_72173
  · decide +kernel

theorem prime_559402967567 : Nat.Prime 559402967567 := by
  apply nodeValid_prime [2, 279701483783] ⟨559402967567, 5, [(2, 1), (279701483783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_279701483783
  · decide +kernel

theorem prime_559402970879 : Nat.Prime 559402970879 := by
  apply nodeValid_prime [2, 467, 598932517] ⟨559402970879, 7, [(2, 1), (467, 1), (598932517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_467
    · exact prime_598932517
  · decide +kernel

theorem prime_560282594119 : Nat.Prime 560282594119 := by
  apply nodeValid_prime [2, 3, 13, 17, 37, 878453] ⟨560282594119, 6, [(2, 1), (3, 1), (13, 2), (17, 1), (37, 1), (878453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_37
    · exact prime_878453
  · decide +kernel

theorem prime_560282608537 : Nat.Prime 560282608537 := by
  apply nodeValid_prime [2, 3, 7, 19, 461, 380753] ⟨560282608537, 5, [(2, 3), (3, 1), (7, 1), (19, 1), (461, 1), (380753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_461
    · exact prime_380753
  · decide +kernel

theorem prime_560282609113 : Nat.Prime 560282609113 := by
  apply nodeValid_prime [2, 3, 17, 31, 44298119] ⟨560282609113, 5, [(2, 3), (3, 1), (17, 1), (31, 1), (44298119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_44298119
  · decide +kernel

theorem prime_561163168897 : Nat.Prime 561163168897 := by
  apply nodeValid_prime [2, 3, 11, 337, 479, 823] ⟨561163168897, 5, [(2, 7), (3, 1), (11, 1), (337, 1), (479, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_337
    · exact prime_479
    · exact prime_823
  · decide +kernel

theorem prime_561163170817 : Nat.Prime 561163170817 := by
  apply nodeValid_prime [2, 3, 97, 627733] ⟨561163170817, 10, [(2, 10), (3, 2), (97, 1), (627733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_627733
  · decide +kernel

theorem prime_561163172839 : Nat.Prime 561163172839 := by
  apply nodeValid_prime [2, 3, 107, 874085939] ⟨561163172839, 3, [(2, 1), (3, 1), (107, 1), (874085939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_874085939
  · decide +kernel

theorem prime_562044674173 : Nat.Prime 562044674173 := by
  apply nodeValid_prime [2, 3, 23, 4157, 489871] ⟨562044674173, 5, [(2, 2), (3, 1), (23, 1), (4157, 1), (489871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_4157
    · exact prime_489871
  · decide +kernel

theorem prime_562044684503 : Nat.Prime 562044684503 := by
  apply nodeValid_prime [2, 7, 367, 383, 285613] ⟨562044684503, 5, [(2, 1), (7, 1), (367, 1), (383, 1), (285613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_367
    · exact prime_383
    · exact prime_285613
  · decide +kernel

theorem prime_562044684911 : Nat.Prime 562044684911 := by
  apply nodeValid_prime [2, 5, 3499, 16063009] ⟨562044684911, 13, [(2, 1), (5, 1), (3499, 1), (16063009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3499
    · exact prime_16063009
  · decide +kernel

theorem prime_562927079063 : Nat.Prime 562927079063 := by
  apply nodeValid_prime [2, 23, 613, 619, 32251] ⟨562927079063, 5, [(2, 1), (23, 1), (613, 1), (619, 1), (32251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_613
    · exact prime_619
    · exact prime_32251
  · decide +kernel

theorem prime_562927079161 : Nat.Prime 562927079161 := by
  apply nodeValid_prime [2, 3, 5, 41, 181, 70237] ⟨562927079161, 7, [(2, 3), (3, 3), (5, 1), (41, 1), (181, 1), (70237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_181
    · exact prime_70237
  · decide +kernel

theorem prime_562927113913 : Nat.Prime 562927113913 := by
  apply nodeValid_prime [2, 3, 181, 129587273] ⟨562927113913, 7, [(2, 3), (3, 1), (181, 1), (129587273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_129587273
  · decide +kernel

theorem prime_563810498149 : Nat.Prime 563810498149 := by
  apply nodeValid_prime [2, 3, 2239, 20984461] ⟨563810498149, 2, [(2, 2), (3, 1), (2239, 1), (20984461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2239
    · exact prime_20984461
  · decide +kernel

theorem prime_563810527793 : Nat.Prime 563810527793 := by
  apply nodeValid_prime [2, 577, 61071331] ⟨563810527793, 3, [(2, 4), (577, 1), (61071331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_61071331
  · decide +kernel

theorem prime_563810528339 : Nat.Prime 563810528339 := by
  apply nodeValid_prime [2, 31, 337, 2081, 12967] ⟨563810528339, 2, [(2, 1), (31, 1), (337, 1), (2081, 1), (12967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_337
    · exact prime_2081
    · exact prime_12967
  · decide +kernel

theorem prime_564694813229 : Nat.Prime 564694813229 := by
  apply nodeValid_prime [2, 7, 13, 1551359377] ⟨564694813229, 2, [(2, 2), (7, 1), (13, 1), (1551359377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1551359377
  · decide +kernel

theorem prime_564694813481 : Nat.Prime 564694813481 := by
  apply nodeValid_prime [2, 5, 7, 2016767191] ⟨564694813481, 3, [(2, 3), (5, 1), (7, 1), (2016767191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2016767191
  · decide +kernel

theorem prime_564694814987 : Nat.Prime 564694814987 := by
  apply nodeValid_prime [2, 17, 379, 43822351] ⟨564694814987, 2, [(2, 1), (17, 1), (379, 1), (43822351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_379
    · exact prime_43822351
  · decide +kernel

theorem prime_565580043211 : Nat.Prime 565580043211 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 53, 131, 563] ⟨565580043211, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (53, 2), (131, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_53
    · exact prime_131
    · exact prime_563
  · decide +kernel

theorem prime_565580043299 : Nat.Prime 565580043299 := by
  apply nodeValid_prime [2, 73, 269, 14400877] ⟨565580043299, 2, [(2, 1), (73, 1), (269, 1), (14400877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_269
    · exact prime_14400877
  · decide +kernel

theorem prime_565580064677 : Nat.Prime 565580064677 := by
  apply nodeValid_prime [2, 11, 9011, 1426489] ⟨565580064677, 2, [(2, 2), (11, 1), (9011, 1), (1426489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9011
    · exact prime_1426489
  · decide +kernel

theorem prime_566466255503 : Nat.Prime 566466255503 := by
  apply nodeValid_prime [2, 7, 167, 199, 1217521] ⟨566466255503, 7, [(2, 1), (7, 1), (167, 1), (199, 1), (1217521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_167
    · exact prime_199
    · exact prime_1217521
  · decide +kernel

theorem prime_566466258949 : Nat.Prime 566466258949 := by
  apply nodeValid_prime [2, 3, 17, 3011, 922217] ⟨566466258949, 2, [(2, 2), (3, 1), (17, 1), (3011, 1), (922217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3011
    · exact prime_922217
  · decide +kernel

theorem prime_566466260023 : Nat.Prime 566466260023 := by
  apply nodeValid_prime [2, 3, 13, 31, 43, 1816051] ⟨566466260023, 3, [(2, 1), (3, 2), (13, 1), (31, 1), (43, 1), (1816051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_43
    · exact prime_1816051
  · decide +kernel

theorem prime_567353389943 : Nat.Prime 567353389943 := by
  apply nodeValid_prime [2, 29, 27551, 355049] ⟨567353389943, 5, [(2, 1), (29, 1), (27551, 1), (355049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_27551
    · exact prime_355049
  · decide +kernel

theorem prime_567353406029 : Nat.Prime 567353406029 := by
  apply nodeValid_prime [2, 67, 11423, 185327] ⟨567353406029, 2, [(2, 2), (67, 1), (11423, 1), (185327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_11423
    · exact prime_185327
  · decide +kernel

theorem prime_567353406227 : Nat.Prime 567353406227 := by
  apply nodeValid_prime [2, 17, 151, 499, 221461] ⟨567353406227, 2, [(2, 1), (17, 1), (151, 1), (499, 1), (221461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_151
    · exact prime_499
    · exact prime_221461
  · decide +kernel

theorem prime_568241451647 : Nat.Prime 568241451647 := by
  apply nodeValid_prime [2, 11, 25829156893] ⟨568241451647, 5, [(2, 1), (11, 1), (25829156893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_25829156893
  · decide +kernel

theorem prime_568241452189 : Nat.Prime 568241452189 := by
  apply nodeValid_prime [2, 3, 19, 109, 7621673] ⟨568241452189, 6, [(2, 2), (3, 2), (19, 1), (109, 1), (7621673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_109
    · exact prime_7621673
  · decide +kernel

theorem prime_568241464579 : Nat.Prime 568241464579 := by
  apply nodeValid_prime [2, 3, 229553, 412571] ⟨568241464579, 2, [(2, 1), (3, 1), (229553, 1), (412571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229553
    · exact prime_412571
  · decide +kernel

theorem prime_569130420121 : Nat.Prime 569130420121 := by
  apply nodeValid_prime [2, 3, 5, 751, 6315251] ⟨569130420121, 11, [(2, 3), (3, 1), (5, 1), (751, 1), (6315251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_751
    · exact prime_6315251
  · decide +kernel

theorem prime_569130420571 : Nat.Prime 569130420571 := by
  apply nodeValid_prime [2, 3, 5, 41, 462707659] ⟨569130420571, 14, [(2, 1), (3, 1), (5, 1), (41, 1), (462707659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_462707659
  · decide +kernel

theorem prime_569130485257 : Nat.Prime 569130485257 := by
  apply nodeValid_prime [2, 3, 1181, 6693133] ⟨569130485257, 5, [(2, 3), (3, 2), (1181, 1), (6693133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1181
    · exact prime_6693133
  · decide +kernel

theorem prime_570020410523 : Nat.Prime 570020410523 := by
  apply nodeValid_prime [2, 19, 41, 619, 591061] ⟨570020410523, 2, [(2, 1), (19, 1), (41, 1), (619, 1), (591061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_619
    · exact prime_591061
  · decide +kernel

theorem prime_570020411423 : Nat.Prime 570020411423 := by
  apply nodeValid_prime [2, 7, 11, 199, 233, 79829] ⟨570020411423, 5, [(2, 1), (7, 1), (11, 1), (199, 1), (233, 1), (79829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_199
    · exact prime_233
    · exact prime_79829
  · decide +kernel

theorem prime_570020442751 : Nat.Prime 570020442751 := by
  apply nodeValid_prime [2, 3, 5, 11, 697913] ⟨570020442751, 6, [(2, 1), (3, 3), (5, 3), (11, 2), (697913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_697913
  · decide +kernel

theorem prime_570911335769 : Nat.Prime 570911335769 := by
  apply nodeValid_prime [2, 71363916971] ⟨570911335769, 3, [(2, 3), (71363916971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71363916971
  · decide +kernel

theorem prime_570911335927 : Nat.Prime 570911335927 := by
  apply nodeValid_prime [2, 3, 191, 498177431] ⟨570911335927, 3, [(2, 1), (3, 1), (191, 1), (498177431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_498177431
  · decide +kernel

theorem prime_570911339483 : Nat.Prime 570911339483 := by
  apply nodeValid_prime [2, 11, 31, 837113401] ⟨570911339483, 2, [(2, 1), (11, 1), (31, 1), (837113401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_837113401
  · decide +kernel

theorem prime_571803175717 : Nat.Prime 571803175717 := by
  apply nodeValid_prime [2, 3, 12049, 3954707] ⟨571803175717, 2, [(2, 2), (3, 1), (12049, 1), (3954707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12049
    · exact prime_3954707
  · decide +kernel

theorem prime_571803175891 : Nat.Prime 571803175891 := by
  apply nodeValid_prime [2, 3, 5, 24763, 256567] ⟨571803175891, 10, [(2, 1), (3, 2), (5, 1), (24763, 1), (256567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_24763
    · exact prime_256567
  · decide +kernel

theorem prime_571803177053 : Nat.Prime 571803177053 := by
  apply nodeValid_prime [2, 1381, 103512523] ⟨571803177053, 2, [(2, 2), (1381, 1), (103512523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1381
    · exact prime_103512523
  · decide +kernel

theorem prime_572695955207 : Nat.Prime 572695955207 := by
  apply nodeValid_prime [2, 1109, 258203767] ⟨572695955207, 5, [(2, 1), (1109, 1), (258203767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1109
    · exact prime_258203767
  · decide +kernel

theorem prime_572696051849 : Nat.Prime 572696051849 := by
  apply nodeValid_prime [2, 79, 8461, 107099] ⟨572696051849, 3, [(2, 3), (79, 1), (8461, 1), (107099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_8461
    · exact prime_107099
  · decide +kernel

theorem prime_572696052623 : Nat.Prime 572696052623 := by
  apply nodeValid_prime [2, 9403, 30452837] ⟨572696052623, 5, [(2, 1), (9403, 1), (30452837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9403
    · exact prime_30452837
  · decide +kernel

end Sude.Lucas.Generated
