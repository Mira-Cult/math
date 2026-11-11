import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_853 : Nat.Prime 853 := by
  apply nodeValid_prime [2, 3, 71] ⟨853, 2, [(2, 2), (3, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_947 : Nat.Prime 947 := by
  apply nodeValid_prime [2, 11, 43] ⟨947, 2, [(2, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_1187 : Nat.Prime 1187 := by
  apply nodeValid_prime [2, 593] ⟨1187, 2, [(2, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_593
  · decide +kernel

theorem prime_1201 : Nat.Prime 1201 := by
  apply nodeValid_prime [2, 3, 5] ⟨1201, 11, [(2, 4), (3, 1), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_1229 : Nat.Prime 1229 := by
  apply nodeValid_prime [2, 307] ⟨1229, 2, [(2, 2), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_307
  · decide +kernel

theorem prime_1237 : Nat.Prime 1237 := by
  apply nodeValid_prime [2, 3, 103] ⟨1237, 2, [(2, 2), (3, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_1327 : Nat.Prime 1327 := by
  apply nodeValid_prime [2, 3, 13, 17] ⟨1327, 3, [(2, 1), (3, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_1381 : Nat.Prime 1381 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨1381, 2, [(2, 2), (3, 1), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_1453 : Nat.Prime 1453 := by
  apply nodeValid_prime [2, 3, 11] ⟨1453, 2, [(2, 2), (3, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_1511 : Nat.Prime 1511 := by
  apply nodeValid_prime [2, 5, 151] ⟨1511, 11, [(2, 1), (5, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
  · decide +kernel

theorem prime_1543 : Nat.Prime 1543 := by
  apply nodeValid_prime [2, 3, 257] ⟨1543, 5, [(2, 1), (3, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
  · decide +kernel

theorem prime_1663 : Nat.Prime 1663 := by
  apply nodeValid_prime [2, 3, 277] ⟨1663, 3, [(2, 1), (3, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
  · decide +kernel

theorem prime_1747 : Nat.Prime 1747 := by
  apply nodeValid_prime [2, 3, 97] ⟨1747, 2, [(2, 1), (3, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
  · decide +kernel

theorem prime_1753 : Nat.Prime 1753 := by
  apply nodeValid_prime [2, 3, 73] ⟨1753, 7, [(2, 3), (3, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_2017 : Nat.Prime 2017 := by
  apply nodeValid_prime [2, 3, 7] ⟨2017, 5, [(2, 5), (3, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_2089 : Nat.Prime 2089 := by
  apply nodeValid_prime [2, 3, 29] ⟨2089, 7, [(2, 3), (3, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_2179 : Nat.Prime 2179 := by
  apply nodeValid_prime [2, 3, 11] ⟨2179, 7, [(2, 1), (3, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_2357 : Nat.Prime 2357 := by
  apply nodeValid_prime [2, 19, 31] ⟨2357, 2, [(2, 2), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_2477 : Nat.Prime 2477 := by
  apply nodeValid_prime [2, 619] ⟨2477, 2, [(2, 2), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_619
  · decide +kernel

theorem prime_2647 : Nat.Prime 2647 := by
  apply nodeValid_prime [2, 3, 7] ⟨2647, 3, [(2, 1), (3, 3), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_2699 : Nat.Prime 2699 := by
  apply nodeValid_prime [2, 19, 71] ⟨2699, 2, [(2, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_2797 : Nat.Prime 2797 := by
  apply nodeValid_prime [2, 3, 233] ⟨2797, 2, [(2, 2), (3, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
  · decide +kernel

theorem prime_2843 : Nat.Prime 2843 := by
  apply nodeValid_prime [2, 7, 29] ⟨2843, 2, [(2, 1), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_3359 : Nat.Prime 3359 := by
  apply nodeValid_prime [2, 23, 73] ⟨3359, 11, [(2, 1), (23, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_73
  · decide +kernel

theorem prime_3361 : Nat.Prime 3361 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨3361, 22, [(2, 5), (3, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_3541 : Nat.Prime 3541 := by
  apply nodeValid_prime [2, 3, 5, 59] ⟨3541, 7, [(2, 2), (3, 1), (5, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_3697 : Nat.Prime 3697 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨3697, 5, [(2, 4), (3, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_3793 : Nat.Prime 3793 := by
  apply nodeValid_prime [2, 3, 79] ⟨3793, 5, [(2, 4), (3, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_3989 : Nat.Prime 3989 := by
  apply nodeValid_prime [2, 997] ⟨3989, 2, [(2, 2), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_997
  · decide +kernel

theorem prime_4021 : Nat.Prime 4021 := by
  apply nodeValid_prime [2, 3, 5, 67] ⟨4021, 2, [(2, 2), (3, 1), (5, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_4733 : Nat.Prime 4733 := by
  apply nodeValid_prime [2, 7, 13] ⟨4733, 5, [(2, 2), (7, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_4871 : Nat.Prime 4871 := by
  apply nodeValid_prime [2, 5, 487] ⟨4871, 11, [(2, 1), (5, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_487
  · decide +kernel

theorem prime_4903 : Nat.Prime 4903 := by
  apply nodeValid_prime [2, 3, 19, 43] ⟨4903, 3, [(2, 1), (3, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_5399 : Nat.Prime 5399 := by
  apply nodeValid_prime [2, 2699] ⟨5399, 7, [(2, 1), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2699
  · decide +kernel

theorem prime_5413 : Nat.Prime 5413 := by
  apply nodeValid_prime [2, 3, 11, 41] ⟨5413, 5, [(2, 2), (3, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_5779 : Nat.Prime 5779 := by
  apply nodeValid_prime [2, 3, 107] ⟨5779, 2, [(2, 1), (3, 3), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
  · decide +kernel

theorem prime_6131 : Nat.Prime 6131 := by
  apply nodeValid_prime [2, 5, 613] ⟨6131, 2, [(2, 1), (5, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_613
  · decide +kernel

theorem prime_6367 : Nat.Prime 6367 := by
  apply nodeValid_prime [2, 3, 1061] ⟨6367, 3, [(2, 1), (3, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1061
  · decide +kernel

theorem prime_6373 : Nat.Prime 6373 := by
  apply nodeValid_prime [2, 3, 59] ⟨6373, 2, [(2, 2), (3, 3), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_6577 : Nat.Prime 6577 := by
  apply nodeValid_prime [2, 3, 137] ⟨6577, 5, [(2, 4), (3, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_6719 : Nat.Prime 6719 := by
  apply nodeValid_prime [2, 3359] ⟨6719, 11, [(2, 1), (3359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3359
  · decide +kernel

theorem prime_6917 : Nat.Prime 6917 := by
  apply nodeValid_prime [2, 7, 13, 19] ⟨6917, 2, [(2, 2), (7, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_7039 : Nat.Prime 7039 := by
  apply nodeValid_prime [2, 3, 17, 23] ⟨7039, 3, [(2, 1), (3, 2), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_8069 : Nat.Prime 8069 := by
  apply nodeValid_prime [2, 2017] ⟨8069, 2, [(2, 2), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2017
  · decide +kernel

theorem prime_8377 : Nat.Prime 8377 := by
  apply nodeValid_prime [2, 3, 349] ⟨8377, 5, [(2, 3), (3, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
  · decide +kernel

theorem prime_8527 : Nat.Prime 8527 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨8527, 5, [(2, 1), (3, 1), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_8669 : Nat.Prime 8669 := by
  apply nodeValid_prime [2, 11, 197] ⟨8669, 2, [(2, 2), (11, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_197
  · decide +kernel

theorem prime_9059 : Nat.Prime 9059 := by
  apply nodeValid_prime [2, 7, 647] ⟨9059, 2, [(2, 1), (7, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_647
  · decide +kernel

theorem prime_9067 : Nat.Prime 9067 := by
  apply nodeValid_prime [2, 3, 1511] ⟨9067, 3, [(2, 1), (3, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1511
  · decide +kernel

theorem prime_9133 : Nat.Prime 9133 := by
  apply nodeValid_prime [2, 3, 761] ⟨9133, 6, [(2, 2), (3, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_761
  · decide +kernel

theorem prime_9203 : Nat.Prime 9203 := by
  apply nodeValid_prime [2, 43, 107] ⟨9203, 2, [(2, 1), (43, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_107
  · decide +kernel

theorem prime_9587 : Nat.Prime 9587 := by
  apply nodeValid_prime [2, 4793] ⟨9587, 2, [(2, 1), (4793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4793
  · decide +kernel

theorem prime_10799 : Nat.Prime 10799 := by
  apply nodeValid_prime [2, 5399] ⟨10799, 19, [(2, 1), (5399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5399
  · decide +kernel

theorem prime_10993 : Nat.Prime 10993 := by
  apply nodeValid_prime [2, 3, 229] ⟨10993, 7, [(2, 4), (3, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
  · decide +kernel

theorem prime_11833 : Nat.Prime 11833 := by
  apply nodeValid_prime [2, 3, 17, 29] ⟨11833, 5, [(2, 3), (3, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_12113 : Nat.Prime 12113 := by
  apply nodeValid_prime [2, 757] ⟨12113, 3, [(2, 4), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_757
  · decide +kernel

theorem prime_12263 : Nat.Prime 12263 := by
  apply nodeValid_prime [2, 6131] ⟨12263, 5, [(2, 1), (6131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6131
  · decide +kernel

theorem prime_13183 : Nat.Prime 13183 := by
  apply nodeValid_prime [2, 3, 13] ⟨13183, 3, [(2, 1), (3, 1), (13, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_14717 : Nat.Prime 14717 := by
  apply nodeValid_prime [2, 13, 283] ⟨14717, 2, [(2, 2), (13, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_283
  · decide +kernel

theorem prime_15073 : Nat.Prime 15073 := by
  apply nodeValid_prime [2, 3, 157] ⟨15073, 5, [(2, 5), (3, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
  · decide +kernel

theorem prime_15497 : Nat.Prime 15497 := by
  apply nodeValid_prime [2, 13, 149] ⟨15497, 3, [(2, 3), (13, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_149
  · decide +kernel

theorem prime_16631 : Nat.Prime 16631 := by
  apply nodeValid_prime [2, 5, 1663] ⟨16631, 19, [(2, 1), (5, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1663
  · decide +kernel

theorem prime_17207 : Nat.Prime 17207 := by
  apply nodeValid_prime [2, 7, 1229] ⟨17207, 5, [(2, 1), (7, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1229
  · decide +kernel

theorem prime_17681 : Nat.Prime 17681 := by
  apply nodeValid_prime [2, 5, 13, 17] ⟨17681, 3, [(2, 4), (5, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_20809 : Nat.Prime 20809 := by
  apply nodeValid_prime [2, 3, 17] ⟨20809, 7, [(2, 3), (3, 2), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_22853 : Nat.Prime 22853 := by
  apply nodeValid_prime [2, 29, 197] ⟨22853, 2, [(2, 2), (29, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_197
  · decide +kernel

theorem prime_23117 : Nat.Prime 23117 := by
  apply nodeValid_prime [2, 5779] ⟨23117, 2, [(2, 2), (5779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5779
  · decide +kernel

theorem prime_24527 : Nat.Prime 24527 := by
  apply nodeValid_prime [2, 12263] ⟨24527, 5, [(2, 1), (12263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12263
  · decide +kernel

theorem prime_26399 : Nat.Prime 26399 := by
  apply nodeValid_prime [2, 67, 197] ⟨26399, 7, [(2, 1), (67, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_197
  · decide +kernel

theorem prime_30649 : Nat.Prime 30649 := by
  apply nodeValid_prime [2, 3, 1277] ⟨30649, 7, [(2, 3), (3, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1277
  · decide +kernel

theorem prime_35081 : Nat.Prime 35081 := by
  apply nodeValid_prime [2, 5, 877] ⟨35081, 3, [(2, 3), (5, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_877
  · decide +kernel

theorem prime_35201 : Nat.Prime 35201 := by
  apply nodeValid_prime [2, 5, 11] ⟨35201, 3, [(2, 7), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_35381 : Nat.Prime 35381 := by
  apply nodeValid_prime [2, 5, 29, 61] ⟨35381, 3, [(2, 2), (5, 1), (29, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_61
  · decide +kernel

theorem prime_35837 : Nat.Prime 35837 := by
  apply nodeValid_prime [2, 17, 31] ⟨35837, 2, [(2, 2), (17, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_38851 : Nat.Prime 38851 := by
  apply nodeValid_prime [2, 3, 5, 7, 37] ⟨38851, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_42643 : Nat.Prime 42643 := by
  apply nodeValid_prime [2, 3, 23, 103] ⟨42643, 2, [(2, 1), (3, 2), (23, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_103
  · decide +kernel

theorem prime_44651 : Nat.Prime 44651 := by
  apply nodeValid_prime [2, 5, 19, 47] ⟨44651, 2, [(2, 1), (5, 2), (19, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_45707 : Nat.Prime 45707 := by
  apply nodeValid_prime [2, 22853] ⟨45707, 2, [(2, 1), (22853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22853
  · decide +kernel

theorem prime_50263 : Nat.Prime 50263 := by
  apply nodeValid_prime [2, 3, 8377] ⟨50263, 3, [(2, 1), (3, 1), (8377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8377
  · decide +kernel

theorem prime_53279 : Nat.Prime 53279 := by
  apply nodeValid_prime [2, 17, 1567] ⟨53279, 7, [(2, 1), (17, 1), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1567
  · decide +kernel

theorem prime_55219 : Nat.Prime 55219 := by
  apply nodeValid_prime [2, 3, 9203] ⟨55219, 2, [(2, 1), (3, 1), (9203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9203
  · decide +kernel

theorem prime_69061 : Nat.Prime 69061 := by
  apply nodeValid_prime [2, 3, 5, 1151] ⟨69061, 2, [(2, 2), (3, 1), (5, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1151
  · decide +kernel

theorem prime_86077 : Nat.Prime 86077 := by
  apply nodeValid_prime [2, 3, 797] ⟨86077, 5, [(2, 2), (3, 3), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_797
  · decide +kernel

theorem prime_86837 : Nat.Prime 86837 := by
  apply nodeValid_prime [2, 17, 1277] ⟨86837, 2, [(2, 2), (17, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1277
  · decide +kernel

theorem prime_89303 : Nat.Prime 89303 := by
  apply nodeValid_prime [2, 44651] ⟨89303, 5, [(2, 1), (44651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44651
  · decide +kernel

theorem prime_89909 : Nat.Prime 89909 := by
  apply nodeValid_prime [2, 7, 13, 19] ⟨89909, 2, [(2, 2), (7, 1), (13, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_90271 : Nat.Prime 90271 := by
  apply nodeValid_prime [2, 3, 5, 17, 59] ⟨90271, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_91291 : Nat.Prime 91291 := by
  apply nodeValid_prime [2, 3, 5, 17, 179] ⟨91291, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_179
  · decide +kernel

theorem prime_91331 : Nat.Prime 91331 := by
  apply nodeValid_prime [2, 5, 9133] ⟨91331, 2, [(2, 1), (5, 1), (9133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9133
  · decide +kernel

theorem prime_98713 : Nat.Prime 98713 := by
  apply nodeValid_prime [2, 3, 457] ⟨98713, 5, [(2, 3), (3, 3), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_457
  · decide +kernel

theorem prime_100673 : Nat.Prime 100673 := by
  apply nodeValid_prime [2, 11, 13] ⟨100673, 3, [(2, 6), (11, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_101873 : Nat.Prime 101873 := by
  apply nodeValid_prime [2, 6367] ⟨101873, 3, [(2, 4), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6367
  · decide +kernel

theorem prime_104701 : Nat.Prime 104701 := by
  apply nodeValid_prime [2, 3, 5, 349] ⟨104701, 2, [(2, 2), (3, 1), (5, 2), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_118387 : Nat.Prime 118387 := by
  apply nodeValid_prime [2, 3, 6577] ⟨118387, 2, [(2, 1), (3, 2), (6577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6577
  · decide +kernel

theorem prime_122597 : Nat.Prime 122597 := by
  apply nodeValid_prime [2, 30649] ⟨122597, 2, [(2, 2), (30649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30649
  · decide +kernel

theorem prime_126827 : Nat.Prime 126827 := by
  apply nodeValid_prime [2, 7, 9059] ⟨126827, 2, [(2, 1), (7, 1), (9059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9059
  · decide +kernel

theorem prime_129589 : Nat.Prime 129589 := by
  apply nodeValid_prime [2, 3, 10799] ⟨129589, 6, [(2, 2), (3, 1), (10799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10799
  · decide +kernel

theorem prime_135781 : Nat.Prime 135781 := by
  apply nodeValid_prime [2, 3, 5, 31, 73] ⟨135781, 6, [(2, 2), (3, 1), (5, 1), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_145391 : Nat.Prime 145391 := by
  apply nodeValid_prime [2, 5, 7, 31, 67] ⟨145391, 11, [(2, 1), (5, 1), (7, 1), (31, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_67
  · decide +kernel

theorem prime_287611 : Nat.Prime 287611 := by
  apply nodeValid_prime [2, 3, 5, 9587] ⟨287611, 3, [(2, 1), (3, 1), (5, 1), (9587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9587
  · decide +kernel

theorem prime_301759 : Nat.Prime 301759 := by
  apply nodeValid_prime [2, 3, 19, 2647] ⟨301759, 3, [(2, 1), (3, 1), (19, 1), (2647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2647
  · decide +kernel

theorem prime_304981 : Nat.Prime 304981 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 23] ⟨304981, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_353621 : Nat.Prime 353621 := by
  apply nodeValid_prime [2, 5, 17681] ⟨353621, 2, [(2, 2), (5, 1), (17681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17681
  · decide +kernel

theorem prime_387007 : Nat.Prime 387007 := by
  apply nodeValid_prime [2, 3, 53, 1217] ⟨387007, 5, [(2, 1), (3, 1), (53, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1217
  · decide +kernel

theorem prime_426233 : Nat.Prime 426233 := by
  apply nodeValid_prime [2, 53279] ⟨426233, 3, [(2, 3), (53279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53279
  · decide +kernel

theorem prime_500107 : Nat.Prime 500107 := by
  apply nodeValid_prime [2, 3, 17, 4903] ⟨500107, 2, [(2, 1), (3, 1), (17, 1), (4903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4903
  · decide +kernel

theorem prime_547747 : Nat.Prime 547747 := by
  apply nodeValid_prime [2, 3, 91291] ⟨547747, 2, [(2, 1), (3, 1), (91291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_91291
  · decide +kernel

theorem prime_628207 : Nat.Prime 628207 := by
  apply nodeValid_prime [2, 3, 104701] ⟨628207, 3, [(2, 1), (3, 1), (104701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_104701
  · decide +kernel

theorem prime_672193 : Nat.Prime 672193 := by
  apply nodeValid_prime [2, 3, 389] ⟨672193, 5, [(2, 6), (3, 3), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
  · decide +kernel

theorem prime_754241 : Nat.Prime 754241 := by
  apply nodeValid_prime [2, 5, 2357] ⟨754241, 3, [(2, 6), (5, 1), (2357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2357
  · decide +kernel

theorem prime_1014617 : Nat.Prime 1014617 := by
  apply nodeValid_prime [2, 126827] ⟨1014617, 3, [(2, 3), (126827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_126827
  · decide +kernel

theorem prime_1138567 : Nat.Prime 1138567 := by
  apply nodeValid_prime [2, 3, 11, 13, 1327] ⟨1138567, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1327
  · decide +kernel

theorem prime_1243691 : Nat.Prime 1243691 := by
  apply nodeValid_prime [2, 5, 7, 109, 163] ⟨1243691, 2, [(2, 1), (5, 1), (7, 1), (109, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_109
    · exact prime_163
  · decide +kernel

theorem prime_1250243 : Nat.Prime 1250243 := by
  apply nodeValid_prime [2, 7, 89303] ⟨1250243, 2, [(2, 1), (7, 1), (89303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89303
  · decide +kernel

theorem prime_1374539 : Nat.Prime 1374539 := by
  apply nodeValid_prime [2, 11, 43, 1453] ⟨1374539, 2, [(2, 1), (11, 1), (43, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_1453
  · decide +kernel

theorem prime_1431967 : Nat.Prime 1431967 := by
  apply nodeValid_prime [2, 3, 41, 5821] ⟨1431967, 3, [(2, 1), (3, 1), (41, 1), (5821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_5821
  · decide +kernel

theorem prime_1768421 : Nat.Prime 1768421 := by
  apply nodeValid_prime [2, 5, 29, 3049] ⟨1768421, 2, [(2, 2), (5, 1), (29, 1), (3049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3049
  · decide +kernel

theorem prime_1991449 : Nat.Prime 1991449 := by
  apply nodeValid_prime [2, 3, 17, 1627] ⟨1991449, 7, [(2, 3), (3, 2), (17, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1627
  · decide +kernel

theorem prime_2030947 : Nat.Prime 2030947 := by
  apply nodeValid_prime [2, 3, 23, 14717] ⟨2030947, 2, [(2, 1), (3, 1), (23, 1), (14717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_14717
  · decide +kernel

theorem prime_2476937 : Nat.Prime 2476937 := by
  apply nodeValid_prime [2, 7, 11, 4021] ⟨2476937, 3, [(2, 3), (7, 1), (11, 1), (4021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_4021
  · decide +kernel

theorem prime_3240161 : Nat.Prime 3240161 := by
  apply nodeValid_prime [2, 5, 7, 11, 263] ⟨3240161, 13, [(2, 5), (5, 1), (7, 1), (11, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_263
  · decide +kernel

theorem prime_3769243 : Nat.Prime 3769243 := by
  apply nodeValid_prime [2, 3, 628207] ⟨3769243, 3, [(2, 1), (3, 1), (628207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_628207
  · decide +kernel

theorem prime_3791189 : Nat.Prime 3791189 := by
  apply nodeValid_prime [2, 41, 23117] ⟨3791189, 2, [(2, 2), (41, 1), (23117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_23117
  · decide +kernel

theorem prime_3791383 : Nat.Prime 3791383 := by
  apply nodeValid_prime [2, 3, 7, 90271] ⟨3791383, 5, [(2, 1), (3, 1), (7, 1), (90271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_90271
  · decide +kernel

theorem prime_4417279 : Nat.Prime 4417279 := by
  apply nodeValid_prime [2, 3, 613, 1201] ⟨4417279, 3, [(2, 1), (3, 1), (613, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_1201
  · decide +kernel

theorem prime_5001071 : Nat.Prime 5001071 := by
  apply nodeValid_prime [2, 5, 500107] ⟨5001071, 11, [(2, 1), (5, 1), (500107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_500107
  · decide +kernel

theorem prime_5431241 : Nat.Prime 5431241 := by
  apply nodeValid_prime [2, 5, 135781] ⟨5431241, 3, [(2, 3), (5, 1), (135781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_135781
  · decide +kernel

theorem prime_6060757 : Nat.Prime 6060757 := by
  apply nodeValid_prime [2, 3, 13, 38851] ⟨6060757, 2, [(2, 2), (3, 1), (13, 1), (38851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_38851
  · decide +kernel

theorem prime_6223741 : Nat.Prime 6223741 := by
  apply nodeValid_prime [2, 3, 5, 47, 2207] ⟨6223741, 2, [(2, 2), (3, 1), (5, 1), (47, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_2207
  · decide +kernel

theorem prime_8449253 : Nat.Prime 8449253 := by
  apply nodeValid_prime [2, 7, 301759] ⟨8449253, 2, [(2, 2), (7, 1), (301759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_301759
  · decide +kernel

theorem prime_10755089 : Nat.Prime 10755089 := by
  apply nodeValid_prime [2, 672193] ⟨10755089, 3, [(2, 4), (672193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_672193
  · decide +kernel

theorem prime_12884051 : Nat.Prime 12884051 := by
  apply nodeValid_prime [2, 5, 167, 1543] ⟨12884051, 2, [(2, 1), (5, 2), (167, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_1543
  · decide +kernel

theorem prime_16727257 : Nat.Prime 16727257 := by
  apply nodeValid_prime [2, 3, 7, 13, 23, 37] ⟨16727257, 10, [(2, 3), (3, 3), (7, 1), (13, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_28612583 : Nat.Prime 28612583 := by
  apply nodeValid_prime [2, 313, 45707] ⟨28612583, 5, [(2, 1), (313, 1), (45707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_45707
  · decide +kernel

theorem prime_31611323 : Nat.Prime 31611323 := by
  apply nodeValid_prime [2, 157, 100673] ⟨31611323, 2, [(2, 1), (157, 1), (100673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_100673
  · decide +kernel

theorem prime_35989649 : Nat.Prime 35989649 := by
  apply nodeValid_prime [2, 19, 118387] ⟨35989649, 3, [(2, 4), (19, 1), (118387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_118387
  · decide +kernel

theorem prime_36045689 : Nat.Prime 36045689 := by
  apply nodeValid_prime [2, 7, 101, 6373] ⟨36045689, 3, [(2, 3), (7, 1), (101, 1), (6373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_6373
  · decide +kernel

theorem prime_53272873 : Nat.Prime 53272873 := by
  apply nodeValid_prime [2, 3, 43, 17207] ⟨53272873, 5, [(2, 3), (3, 2), (43, 1), (17207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_17207
  · decide +kernel

theorem prime_57225167 : Nat.Prime 57225167 := by
  apply nodeValid_prime [2, 28612583] ⟨57225167, 5, [(2, 1), (28612583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28612583
  · decide +kernel

theorem prime_66570353 : Nat.Prime 66570353 := by
  apply nodeValid_prime [2, 127, 181] ⟨66570353, 3, [(2, 4), (127, 1), (181, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_181
  · decide +kernel

theorem prime_91874389 : Nat.Prime 91874389 := by
  apply nodeValid_prime [2, 3, 2693, 2843] ⟨91874389, 2, [(2, 2), (3, 1), (2693, 1), (2843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2693
    · exact prime_2843
  · decide +kernel

theorem prime_115280447 : Nat.Prime 115280447 := by
  apply nodeValid_prime [2, 163, 353621] ⟨115280447, 5, [(2, 1), (163, 1), (353621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_353621
  · decide +kernel

theorem prime_167441503 : Nat.Prime 167441503 := by
  apply nodeValid_prime [2, 3, 37, 754241] ⟨167441503, 3, [(2, 1), (3, 1), (37, 1), (754241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_754241
  · decide +kernel

theorem prime_181977073 : Nat.Prime 181977073 := by
  apply nodeValid_prime [2, 3, 3791189] ⟨181977073, 5, [(2, 4), (3, 1), (3791189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3791189
  · decide +kernel

theorem prime_259233641 : Nat.Prime 259233641 := by
  apply nodeValid_prime [2, 5, 1753, 3697] ⟨259233641, 6, [(2, 3), (5, 1), (1753, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1753
    · exact prime_3697
  · decide +kernel

theorem prime_388900649 : Nat.Prime 388900649 := by
  apply nodeValid_prime [2, 1381, 35201] ⟨388900649, 3, [(2, 3), (1381, 1), (35201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1381
    · exact prime_35201
  · decide +kernel

theorem prime_392092243 : Nat.Prime 392092243 := by
  apply nodeValid_prime [2, 3, 1847, 35381] ⟨392092243, 2, [(2, 1), (3, 1), (1847, 1), (35381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1847
    · exact prime_35381
  · decide +kernel

theorem prime_558493553 : Nat.Prime 558493553 := by
  apply nodeValid_prime [2, 61, 401, 1427] ⟨558493553, 3, [(2, 4), (61, 1), (401, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_401
    · exact prime_1427
  · decide +kernel

theorem prime_1086248363 : Nat.Prime 1086248363 := by
  apply nodeValid_prime [2, 269, 373, 5413] ⟨1086248363, 2, [(2, 1), (269, 1), (373, 1), (5413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_373
    · exact prime_5413
  · decide +kernel

theorem prime_1153462049 : Nat.Prime 1153462049 := by
  apply nodeValid_prime [2, 36045689] ⟨1153462049, 3, [(2, 5), (36045689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36045689
  · decide +kernel

theorem prime_1156702727 : Nat.Prime 1156702727 := by
  apply nodeValid_prime [2, 6719, 86077] ⟨1156702727, 5, [(2, 1), (6719, 1), (86077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6719
    · exact prime_86077
  · decide +kernel

theorem prime_1260163843 : Nat.Prime 1260163843 := by
  apply nodeValid_prime [2, 3, 7, 2477, 12113] ⟨1260163843, 2, [(2, 1), (3, 1), (7, 1), (2477, 1), (12113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2477
    · exact prime_12113
  · decide +kernel

theorem prime_1299829591 : Nat.Prime 1299829591 := by
  apply nodeValid_prime [2, 3, 5, 23, 29, 59, 367] ⟨1299829591, 3, [(2, 1), (3, 2), (5, 1), (23, 1), (29, 1), (59, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_29
    · exact prime_59
    · exact prime_367
  · decide +kernel

theorem prime_1503677467 : Nat.Prime 1503677467 := by
  apply nodeValid_prime [2, 3, 653, 42643] ⟨1503677467, 3, [(2, 1), (3, 3), (653, 1), (42643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
    · exact prime_42643
  · decide +kernel

theorem prime_2281121221 : Nat.Prime 2281121221 := by
  apply nodeValid_prime [2, 3, 5, 7, 5431241] ⟨2281121221, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (5431241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_5431241
  · decide +kernel

theorem prime_2548886833 : Nat.Prime 2548886833 := by
  apply nodeValid_prime [2, 3, 853, 6917] ⟨2548886833, 10, [(2, 4), (3, 3), (853, 1), (6917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853
    · exact prime_6917
  · decide +kernel

theorem prime_2932497311 : Nat.Prime 2932497311 := by
  apply nodeValid_prime [2, 5, 127, 149, 15497] ⟨2932497311, 7, [(2, 1), (5, 1), (127, 1), (149, 1), (15497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_149
    · exact prime_15497
  · decide +kernel

theorem prime_4575107333 : Nat.Prime 4575107333 := by
  apply nodeValid_prime [2, 353, 3240161] ⟨4575107333, 2, [(2, 2), (353, 1), (3240161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_3240161
  · decide +kernel

theorem prime_9331695133 : Nat.Prime 9331695133 := by
  apply nodeValid_prime [2, 3, 683, 1138567] ⟨9331695133, 2, [(2, 2), (3, 1), (683, 1), (1138567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_1138567
  · decide +kernel

theorem prime_11697273509 : Nat.Prime 11697273509 := by
  apply nodeValid_prime [2, 2339, 1250243] ⟨11697273509, 2, [(2, 2), (2339, 1), (1250243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2339
    · exact prime_1250243
  · decide +kernel

theorem prime_15036774671 : Nat.Prime 15036774671 := by
  apply nodeValid_prime [2, 5, 1503677467] ⟨15036774671, 14, [(2, 1), (5, 1), (1503677467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1503677467
  · decide +kernel

theorem prime_23722939579 : Nat.Prime 23722939579 := by
  apply nodeValid_prime [2, 3, 13, 17, 3361, 5323] ⟨23722939579, 2, [(2, 1), (3, 1), (13, 1), (17, 1), (3361, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_3361
    · exact prime_5323
  · decide +kernel

theorem prime_47445879179 : Nat.Prime 47445879179 := by
  apply nodeValid_prime [2, 61, 388900649] ⟨47445879179, 2, [(2, 1), (61, 1), (388900649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_388900649
  · decide +kernel

theorem prime_88698994339 : Nat.Prime 88698994339 := by
  apply nodeValid_prime [2, 3, 1049, 1069, 13183] ⟨88698994339, 3, [(2, 1), (3, 1), (1049, 1), (1069, 1), (13183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1049
    · exact prime_1069
    · exact prime_13183
  · decide +kernel

theorem prime_88698995257 : Nat.Prime 88698995257 := by
  apply nodeValid_prime [2, 3, 739, 5001071] ⟨88698995257, 5, [(2, 3), (3, 1), (739, 1), (5001071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_739
    · exact prime_5001071
  · decide +kernel

theorem prime_88699008851 : Nat.Prime 88699008851 := by
  apply nodeValid_prime [2, 5, 31, 57225167] ⟨88699008851, 2, [(2, 1), (5, 2), (31, 1), (57225167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_57225167
  · decide +kernel

theorem prime_88951396733 : Nat.Prime 88951396733 := by
  apply nodeValid_prime [2, 11, 73, 401, 69061] ⟨88951396733, 2, [(2, 2), (11, 1), (73, 1), (401, 1), (69061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_401
    · exact prime_69061
  · decide +kernel

theorem prime_88951416707 : Nat.Prime 88951416707 := by
  apply nodeValid_prime [2, 61, 359, 2030947] ⟨88951416707, 2, [(2, 1), (61, 1), (359, 1), (2030947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_359
    · exact prime_2030947
  · decide +kernel

theorem prime_88951417237 : Nat.Prime 88951417237 := by
  apply nodeValid_prime [2, 3, 11, 17, 31, 426233] ⟨88951417237, 13, [(2, 2), (3, 2), (11, 1), (17, 1), (31, 1), (426233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_31
    · exact prime_426233
  · decide +kernel

theorem prime_89204273021 : Nat.Prime 89204273021 := by
  apply nodeValid_prime [2, 5, 67, 66570353] ⟨89204273021, 2, [(2, 2), (5, 1), (67, 1), (66570353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_66570353
  · decide +kernel

theorem prime_89204277317 : Nat.Prime 89204277317 := by
  apply nodeValid_prime [2, 7, 11, 19, 53, 287611] ⟨89204277317, 2, [(2, 2), (7, 1), (11, 1), (19, 1), (53, 1), (287611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_53
    · exact prime_287611
  · decide +kernel

theorem prime_89204277467 : Nat.Prime 89204277467 := by
  apply nodeValid_prime [2, 37, 11833, 101873] ⟨89204277467, 2, [(2, 1), (37, 1), (11833, 1), (101873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_11833
    · exact prime_101873
  · decide +kernel

theorem prime_89457626873 : Nat.Prime 89457626873 := by
  apply nodeValid_prime [2, 97, 115280447] ⟨89457626873, 3, [(2, 3), (97, 1), (115280447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_115280447
  · decide +kernel

theorem prime_89457628391 : Nat.Prime 89457628391 := by
  apply nodeValid_prime [2, 5, 13, 4733, 145391] ⟨89457628391, 43, [(2, 1), (5, 1), (13, 1), (4733, 1), (145391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4733
    · exact prime_145391
  · decide +kernel

theorem prime_89457636883 : Nat.Prime 89457636883 := by
  apply nodeValid_prime [2, 3, 19, 31, 83, 304981] ⟨89457636883, 2, [(2, 1), (3, 1), (19, 1), (31, 1), (83, 1), (304981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_83
    · exact prime_304981
  · decide +kernel

theorem prime_89711489953 : Nat.Prime 89711489953 := by
  apply nodeValid_prime [2, 3, 7, 59, 71, 3541] ⟨89711489953, 5, [(2, 5), (3, 3), (7, 1), (59, 1), (71, 1), (3541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_71
    · exact prime_3541
  · decide +kernel

theorem prime_89711518133 : Nat.Prime 89711518133 := by
  apply nodeValid_prime [2, 421, 53272873] ⟨89711518133, 2, [(2, 2), (421, 1), (53272873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_421
    · exact prime_53272873
  · decide +kernel

theorem prime_89711518709 : Nat.Prime 89711518709 := by
  apply nodeValid_prime [2, 7, 35081, 91331] ⟨89711518709, 2, [(2, 2), (7, 1), (35081, 1), (91331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_35081
    · exact prime_91331
  · decide +kernel

theorem prime_89965825259 : Nat.Prime 89965825259 := by
  apply nodeValid_prime [2, 1423, 31611323] ⟨89965825259, 2, [(2, 1), (1423, 1), (31611323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1423
    · exact prime_31611323
  · decide +kernel

theorem prime_89965876397 : Nat.Prime 89965876397 := by
  apply nodeValid_prime [2, 11, 163, 1447, 8669] ⟨89965876397, 2, [(2, 2), (11, 1), (163, 1), (1447, 1), (8669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_163
    · exact prime_1447
    · exact prime_8669
  · decide +kernel

theorem prime_89965876909 : Nat.Prime 89965876909 := by
  apply nodeValid_prime [2, 3, 1237, 6060757] ⟨89965876909, 2, [(2, 2), (3, 1), (1237, 1), (6060757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1237
    · exact prime_6060757
  · decide +kernel

theorem prime_90220648027 : Nat.Prime 90220648027 := by
  apply nodeValid_prime [2, 3, 15036774671] ⟨90220648027, 2, [(2, 1), (3, 1), (15036774671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15036774671
  · decide +kernel

theorem prime_90220649999 : Nat.Prime 90220649999 := by
  apply nodeValid_prime [2, 491, 91874389] ⟨90220649999, 7, [(2, 1), (491, 1), (91874389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_91874389
  · decide +kernel

theorem prime_90220650937 : Nat.Prime 90220650937 := by
  apply nodeValid_prime [2, 3, 13, 8069, 35837] ⟨90220650937, 11, [(2, 3), (3, 1), (13, 1), (8069, 1), (35837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_8069
    · exact prime_35837
  · decide +kernel

theorem prime_90475955203 : Nat.Prime 90475955203 := by
  apply nodeValid_prime [2, 3, 8527, 1768421] ⟨90475955203, 2, [(2, 1), (3, 1), (8527, 1), (1768421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8527
    · exact prime_1768421
  · decide +kernel

theorem prime_90475955587 : Nat.Prime 90475955587 := by
  apply nodeValid_prime [2, 3, 558493553] ⟨90475955587, 3, [(2, 1), (3, 4), (558493553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_558493553
  · decide +kernel

theorem prime_90475966201 : Nat.Prime 90475966201 := by
  apply nodeValid_prime [2, 3, 5, 9067, 16631] ⟨90475966201, 21, [(2, 3), (3, 1), (5, 2), (9067, 1), (16631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9067
    · exact prime_16631
  · decide +kernel

theorem prime_90731774351 : Nat.Prime 90731774351 := by
  apply nodeValid_prime [2, 5, 7, 259233641] ⟨90731774351, 7, [(2, 1), (5, 2), (7, 1), (259233641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_259233641
  · decide +kernel

theorem prime_90731795029 : Nat.Prime 90731795029 := by
  apply nodeValid_prime [2, 3, 7, 47, 223, 257, 401] ⟨90731795029, 10, [(2, 2), (3, 1), (7, 1), (47, 1), (223, 1), (257, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_223
    · exact prime_257
    · exact prime_401
  · decide +kernel

theorem prime_90731796697 : Nat.Prime 90731796697 := by
  apply nodeValid_prime [2, 3, 1260163843] ⟨90731796697, 5, [(2, 3), (3, 2), (1260163843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1260163843
  · decide +kernel

theorem prime_90988052941 : Nat.Prime 90988052941 := by
  apply nodeValid_prime [2, 3, 5, 47, 10755089] ⟨90988052941, 10, [(2, 2), (3, 2), (5, 1), (47, 1), (10755089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_10755089
  · decide +kernel

theorem prime_90988054127 : Nat.Prime 90988054127 := by
  apply nodeValid_prime [2, 17, 19, 37, 1747, 2179] ⟨90988054127, 5, [(2, 1), (17, 1), (19, 1), (37, 1), (1747, 1), (2179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_37
    · exact prime_1747
    · exact prime_2179
  · decide +kernel

theorem prime_90988071371 : Nat.Prime 90988071371 := by
  apply nodeValid_prime [2, 5, 7, 1299829591] ⟨90988071371, 7, [(2, 1), (5, 1), (7, 1), (1299829591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1299829591
  · decide +kernel

theorem prime_91244848841 : Nat.Prime 91244848841 := by
  apply nodeValid_prime [2, 5, 2281121221] ⟨91244848841, 7, [(2, 3), (5, 1), (2281121221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2281121221
  · decide +kernel

theorem prime_91244849183 : Nat.Prime 91244849183 := by
  apply nodeValid_prime [2, 3541, 12884051] ⟨91244849183, 5, [(2, 1), (3541, 1), (12884051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3541
    · exact prime_12884051
  · decide +kernel

theorem prime_91244862493 : Nat.Prime 91244862493 := by
  apply nodeValid_prime [2, 3, 7, 1086248363] ⟨91244862493, 6, [(2, 2), (3, 1), (7, 1), (1086248363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1086248363
  · decide +kernel

theorem prime_91502143069 : Nat.Prime 91502143069 := by
  apply nodeValid_prime [2, 3, 7, 17, 3769243] ⟨91502143069, 2, [(2, 2), (3, 1), (7, 1), (17, 2), (3769243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_3769243
  · decide +kernel

theorem prime_91502143091 : Nat.Prime 91502143091 := by
  apply nodeValid_prime [2, 5, 53, 7039, 24527] ⟨91502143091, 2, [(2, 1), (5, 1), (53, 1), (7039, 1), (24527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_7039
    · exact prime_24527
  · decide +kernel

theorem prime_91502146661 : Nat.Prime 91502146661 := by
  apply nodeValid_prime [2, 5, 4575107333] ⟨91502146661, 2, [(2, 2), (5, 1), (4575107333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4575107333
  · decide +kernel

theorem prime_91759925989 : Nat.Prime 91759925989 := by
  apply nodeValid_prime [2, 3, 2548886833] ⟨91759925989, 10, [(2, 2), (3, 2), (2548886833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2548886833
  · decide +kernel

theorem prime_91759931749 : Nat.Prime 91759931749 := by
  apply nodeValid_prime [2, 3, 17, 19, 157, 50263] ⟨91759931749, 2, [(2, 2), (3, 2), (17, 1), (19, 1), (157, 1), (50263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_157
    · exact prime_50263
  · decide +kernel

theorem prime_91759932247 : Nat.Prime 91759932247 := by
  apply nodeValid_prime [2, 3, 15073, 1014617] ⟨91759932247, 3, [(2, 1), (3, 1), (15073, 1), (1014617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15073
    · exact prime_1014617
  · decide +kernel

theorem prime_92018199421 : Nat.Prime 92018199421 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 1431967] ⟨92018199421, 19, [(2, 2), (3, 3), (5, 1), (7, 1), (17, 1), (1431967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_1431967
  · decide +kernel

theorem prime_92018209519 : Nat.Prime 92018209519 := by
  apply nodeValid_prime [2, 3, 17, 61, 547747] ⟨92018209519, 3, [(2, 1), (3, 4), (17, 1), (61, 1), (547747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_547747
  · decide +kernel

theorem prime_92018209709 : Nat.Prime 92018209709 := by
  apply nodeValid_prime [2, 53, 349, 1243691] ⟨92018209709, 2, [(2, 2), (53, 1), (349, 1), (1243691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_349
    · exact prime_1243691
  · decide +kernel

theorem prime_92276957587 : Nat.Prime 92276957587 := by
  apply nodeValid_prime [2, 3, 11, 10789, 129589] ⟨92276957587, 3, [(2, 1), (3, 1), (11, 1), (10789, 1), (129589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_10789
    · exact prime_129589
  · decide +kernel

theorem prime_92276958311 : Nat.Prime 92276958311 := by
  apply nodeValid_prime [2, 5, 2089, 4417279] ⟨92276958311, 19, [(2, 1), (5, 1), (2089, 1), (4417279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2089
    · exact prime_4417279
  · decide +kernel

theorem prime_92276963921 : Nat.Prime 92276963921 := by
  apply nodeValid_prime [2, 5, 1153462049] ⟨92276963921, 3, [(2, 4), (5, 1), (1153462049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1153462049
  · decide +kernel

theorem prime_92536218161 : Nat.Prime 92536218161 := by
  apply nodeValid_prime [2, 5, 1156702727] ⟨92536218161, 3, [(2, 4), (5, 1), (1156702727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1156702727
  · decide +kernel

theorem prime_92536218857 : Nat.Prime 92536218857 := by
  apply nodeValid_prime [2, 37, 8449253] ⟨92536218857, 3, [(2, 3), (37, 2), (8449253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_8449253
  · decide +kernel

theorem prime_92536218937 : Nat.Prime 92536218937 := by
  apply nodeValid_prime [2, 3, 7, 313, 9311] ⟨92536218937, 5, [(2, 3), (3, 4), (7, 2), (313, 1), (9311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_313
    · exact prime_9311
  · decide +kernel

theorem prime_92795967769 : Nat.Prime 92795967769 := by
  apply nodeValid_prime [2, 3, 7, 223, 2476937] ⟨92795967769, 11, [(2, 3), (3, 1), (7, 1), (223, 1), (2476937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_223
    · exact prime_2476937
  · decide +kernel

theorem prime_92795977991 : Nat.Prime 92795977991 := by
  apply nodeValid_prime [2, 5, 29, 3559, 89909] ⟨92795977991, 13, [(2, 1), (5, 1), (29, 1), (3559, 1), (89909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3559
    · exact prime_89909
  · decide +kernel

theorem prime_92795978311 : Nat.Prime 92795978311 := by
  apply nodeValid_prime [2, 3, 5, 7, 71, 6223741] ⟨92795978311, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (71, 1), (6223741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_6223741
  · decide +kernel

theorem prime_93056211011 : Nat.Prime 93056211011 := by
  apply nodeValid_prime [2, 5, 7, 37, 1361, 26399] ⟨93056211011, 2, [(2, 1), (5, 1), (7, 1), (37, 1), (1361, 1), (26399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_1361
    · exact prime_26399
  · decide +kernel

theorem prime_93056265661 : Nat.Prime 93056265661 := by
  apply nodeValid_prime [2, 3, 5, 17, 151, 509, 1187] ⟨93056265661, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (151, 1), (509, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_151
    · exact prime_509
    · exact prime_1187
  · decide +kernel

theorem prime_93056265941 : Nat.Prime 93056265941 := by
  apply nodeValid_prime [2, 5, 11, 4871, 86837] ⟨93056265941, 3, [(2, 2), (5, 1), (11, 1), (4871, 1), (86837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_4871
    · exact prime_86837
  · decide +kernel

theorem prime_93316948717 : Nat.Prime 93316948717 := by
  apply nodeValid_prime [2, 3, 733, 2797, 3793] ⟨93316948717, 2, [(2, 2), (3, 1), (733, 1), (2797, 1), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_733
    · exact prime_2797
    · exact prime_3793
  · decide +kernel

theorem prime_93316951331 : Nat.Prime 93316951331 := by
  apply nodeValid_prime [2, 5, 9331695133] ⟨93316951331, 2, [(2, 1), (5, 1), (9331695133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9331695133
  · decide +kernel

theorem prime_93316952569 : Nat.Prime 93316952569 := by
  apply nodeValid_prime [2, 3, 7, 17, 331, 98713] ⟨93316952569, 31, [(2, 3), (3, 1), (7, 1), (17, 1), (331, 1), (98713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_331
    · exact prime_98713
  · decide +kernel

theorem prime_93578182673 : Nat.Prime 93578182673 := by
  apply nodeValid_prime [2, 13, 83, 1409, 3847] ⟨93578182673, 3, [(2, 4), (13, 1), (83, 1), (1409, 1), (3847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_83
    · exact prime_1409
    · exact prime_3847
  · decide +kernel

theorem prime_93578188073 : Nat.Prime 93578188073 := by
  apply nodeValid_prime [2, 11697273509] ⟨93578188073, 3, [(2, 3), (11697273509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11697273509
  · decide +kernel

theorem prime_93578188511 : Nat.Prime 93578188511 := by
  apply nodeValid_prime [2, 5, 37, 127, 1991449] ⟨93578188511, 17, [(2, 1), (5, 1), (37, 1), (127, 1), (1991449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_127
    · exact prime_1991449
  · decide +kernel

theorem prime_93839911771 : Nat.Prime 93839911771 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 16727257] ⟨93839911771, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (16727257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_16727257
  · decide +kernel

theorem prime_93839911873 : Nat.Prime 93839911873 := by
  apply nodeValid_prime [2, 3, 7, 17, 947, 4337] ⟨93839911873, 10, [(2, 6), (3, 1), (7, 1), (17, 1), (947, 1), (4337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_947
    · exact prime_4337
  · decide +kernel

theorem prime_93839913953 : Nat.Prime 93839913953 := by
  apply nodeValid_prime [2, 2932497311] ⟨93839913953, 3, [(2, 5), (2932497311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2932497311
  · decide +kernel

theorem prime_94102124687 : Nat.Prime 94102124687 := by
  apply nodeValid_prime [2, 281, 167441503] ⟨94102124687, 5, [(2, 1), (281, 1), (167441503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_167441503
  · decide +kernel

theorem prime_94102126061 : Nat.Prime 94102126061 := by
  apply nodeValid_prime [2, 5, 17, 73, 3791383] ⟨94102126061, 2, [(2, 2), (5, 1), (17, 1), (73, 1), (3791383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_73
    · exact prime_3791383
  · decide +kernel

theorem prime_94102138321 : Nat.Prime 94102138321 := by
  apply nodeValid_prime [2, 3, 5, 392092243] ⟨94102138321, 19, [(2, 4), (3, 1), (5, 1), (392092243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_392092243
  · decide +kernel

theorem prime_94364851429 : Nat.Prime 94364851429 := by
  apply nodeValid_prime [2, 3, 1907, 1374539] ⟨94364851429, 2, [(2, 2), (3, 2), (1907, 1), (1374539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1907
    · exact prime_1374539
  · decide +kernel

theorem prime_94364853481 : Nat.Prime 94364853481 := by
  apply nodeValid_prime [2, 3, 5, 47, 101, 55219] ⟨94364853481, 11, [(2, 3), (3, 2), (5, 1), (47, 1), (101, 1), (55219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_101
    · exact prime_55219
  · decide +kernel

theorem prime_94364859679 : Nat.Prime 94364859679 := by
  apply nodeValid_prime [2, 3, 19, 23, 35989649] ⟨94364859679, 12, [(2, 1), (3, 1), (19, 1), (23, 1), (35989649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_35989649
  · decide +kernel

theorem prime_94628077961 : Nat.Prime 94628077961 := by
  apply nodeValid_prime [2, 5, 13, 181977073] ⟨94628077961, 3, [(2, 3), (5, 1), (13, 1), (181977073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_181977073
  · decide +kernel

theorem prime_94628095141 : Nat.Prime 94628095141 := by
  apply nodeValid_prime [2, 3, 5, 19, 3989, 20809] ⟨94628095141, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (3989, 1), (20809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_3989
    · exact prime_20809
  · decide +kernel

theorem prime_94628095777 : Nat.Prime 94628095777 := by
  apply nodeValid_prime [2, 3, 41, 10993] ⟨94628095777, 5, [(2, 5), (3, 8), (41, 1), (10993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_10993
  · decide +kernel

theorem prime_94891758317 : Nat.Prime 94891758317 := by
  apply nodeValid_prime [2, 23722939579] ⟨94891758317, 2, [(2, 2), (23722939579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23722939579
  · decide +kernel

theorem prime_94891758359 : Nat.Prime 94891758359 := by
  apply nodeValid_prime [2, 47445879179] ⟨94891758359, 13, [(2, 1), (47445879179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_47445879179
  · decide +kernel

theorem prime_94891794359 : Nat.Prime 94891794359 := by
  apply nodeValid_prime [2, 122597, 387007] ⟨94891794359, 13, [(2, 1), (122597, 1), (387007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_122597
    · exact prime_387007
  · decide +kernel

end Sude.Lucas.Generated
