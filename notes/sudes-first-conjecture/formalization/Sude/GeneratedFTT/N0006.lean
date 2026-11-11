import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_239 : Nat.Prime 239 := by
  apply nodeValid_prime [2, 7, 17] ⟨239, 7, [(2, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_383 : Nat.Prime 383 := by
  apply nodeValid_prime [2, 191] ⟨383, 5, [(2, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_191
  · decide +kernel

theorem prime_449 : Nat.Prime 449 := by
  apply nodeValid_prime [2, 7] ⟨449, 3, [(2, 6), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7
  · decide +kernel

theorem prime_557 : Nat.Prime 557 := by
  apply nodeValid_prime [2, 139] ⟨557, 2, [(2, 2), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_139
  · decide +kernel

theorem prime_569 : Nat.Prime 569 := by
  apply nodeValid_prime [2, 71] ⟨569, 3, [(2, 3), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71
  · decide +kernel

theorem prime_827 : Nat.Prime 827 := by
  apply nodeValid_prime [2, 7, 59] ⟨827, 2, [(2, 1), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_991 : Nat.Prime 991 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨991, 6, [(2, 1), (3, 2), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_1223 : Nat.Prime 1223 := by
  apply nodeValid_prime [2, 13, 47] ⟨1223, 5, [(2, 1), (13, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_1319 : Nat.Prime 1319 := by
  apply nodeValid_prime [2, 659] ⟨1319, 13, [(2, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_659
  · decide +kernel

theorem prime_1867 : Nat.Prime 1867 := by
  apply nodeValid_prime [2, 3, 311] ⟨1867, 2, [(2, 1), (3, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
  · decide +kernel

theorem prime_1901 : Nat.Prime 1901 := by
  apply nodeValid_prime [2, 5, 19] ⟨1901, 2, [(2, 2), (5, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_2029 : Nat.Prime 2029 := by
  apply nodeValid_prime [2, 3, 13] ⟨2029, 2, [(2, 2), (3, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_2053 : Nat.Prime 2053 := by
  apply nodeValid_prime [2, 3, 19] ⟨2053, 2, [(2, 2), (3, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_2311 : Nat.Prime 2311 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨2311, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_2393 : Nat.Prime 2393 := by
  apply nodeValid_prime [2, 13, 23] ⟨2393, 3, [(2, 3), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_2447 : Nat.Prime 2447 := by
  apply nodeValid_prime [2, 1223] ⟨2447, 5, [(2, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1223
  · decide +kernel

theorem prime_2539 : Nat.Prime 2539 := by
  apply nodeValid_prime [2, 3, 47] ⟨2539, 2, [(2, 1), (3, 3), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_3037 : Nat.Prime 3037 := by
  apply nodeValid_prime [2, 3, 11, 23] ⟨3037, 2, [(2, 2), (3, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_3301 : Nat.Prime 3301 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨3301, 6, [(2, 2), (3, 1), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_3593 : Nat.Prime 3593 := by
  apply nodeValid_prime [2, 449] ⟨3593, 3, [(2, 3), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_449
  · decide +kernel

theorem prime_3821 : Nat.Prime 3821 := by
  apply nodeValid_prime [2, 5, 191] ⟨3821, 3, [(2, 2), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_3907 : Nat.Prime 3907 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨3907, 2, [(2, 1), (3, 2), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_4003 : Nat.Prime 4003 := by
  apply nodeValid_prime [2, 3, 23, 29] ⟨4003, 2, [(2, 1), (3, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_4057 : Nat.Prime 4057 := by
  apply nodeValid_prime [2, 3, 13] ⟨4057, 5, [(2, 3), (3, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_4099 : Nat.Prime 4099 := by
  apply nodeValid_prime [2, 3, 683] ⟨4099, 2, [(2, 1), (3, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
  · decide +kernel

theorem prime_4231 : Nat.Prime 4231 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨4231, 3, [(2, 1), (3, 2), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_4457 : Nat.Prime 4457 := by
  apply nodeValid_prime [2, 557] ⟨4457, 3, [(2, 3), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_557
  · decide +kernel

theorem prime_4787 : Nat.Prime 4787 := by
  apply nodeValid_prime [2, 2393] ⟨4787, 2, [(2, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2393
  · decide +kernel

theorem prime_4933 : Nat.Prime 4933 := by
  apply nodeValid_prime [2, 3, 137] ⟨4933, 2, [(2, 2), (3, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_5153 : Nat.Prime 5153 := by
  apply nodeValid_prime [2, 7, 23] ⟨5153, 5, [(2, 5), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_5197 : Nat.Prime 5197 := by
  apply nodeValid_prime [2, 3, 433] ⟨5197, 7, [(2, 2), (3, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_433
  · decide +kernel

theorem prime_6323 : Nat.Prime 6323 := by
  apply nodeValid_prime [2, 29, 109] ⟨6323, 2, [(2, 1), (29, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_109
  · decide +kernel

theorem prime_6803 : Nat.Prime 6803 := by
  apply nodeValid_prime [2, 19, 179] ⟨6803, 2, [(2, 1), (19, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_179
  · decide +kernel

theorem prime_6841 : Nat.Prime 6841 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨6841, 22, [(2, 3), (3, 2), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_7349 : Nat.Prime 7349 := by
  apply nodeValid_prime [2, 11, 167] ⟨7349, 2, [(2, 2), (11, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_167
  · decide +kernel

theorem prime_7877 : Nat.Prime 7877 := by
  apply nodeValid_prime [2, 11, 179] ⟨7877, 2, [(2, 2), (11, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_179
  · decide +kernel

theorem prime_8011 : Nat.Prime 8011 := by
  apply nodeValid_prime [2, 3, 5, 89] ⟨8011, 14, [(2, 1), (3, 2), (5, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_8089 : Nat.Prime 8089 := by
  apply nodeValid_prime [2, 3, 337] ⟨8089, 17, [(2, 3), (3, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
  · decide +kernel

theorem prime_8513 : Nat.Prime 8513 := by
  apply nodeValid_prime [2, 7, 19] ⟨8513, 5, [(2, 6), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_8861 : Nat.Prime 8861 := by
  apply nodeValid_prime [2, 5, 443] ⟨8861, 2, [(2, 2), (5, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_443
  · decide +kernel

theorem prime_10589 : Nat.Prime 10589 := by
  apply nodeValid_prime [2, 2647] ⟨10589, 2, [(2, 2), (2647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2647
  · decide +kernel

theorem prime_11257 : Nat.Prime 11257 := by
  apply nodeValid_prime [2, 3, 7, 67] ⟨11257, 10, [(2, 3), (3, 1), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_11411 : Nat.Prime 11411 := by
  apply nodeValid_prime [2, 5, 7, 163] ⟨11411, 7, [(2, 1), (5, 1), (7, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_163
  · decide +kernel

theorem prime_11447 : Nat.Prime 11447 := by
  apply nodeValid_prime [2, 59, 97] ⟨11447, 5, [(2, 1), (59, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_97
  · decide +kernel

theorem prime_11701 : Nat.Prime 11701 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨11701, 6, [(2, 2), (3, 2), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_12149 : Nat.Prime 12149 := by
  apply nodeValid_prime [2, 3037] ⟨12149, 2, [(2, 2), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3037
  · decide +kernel

theorem prime_12539 : Nat.Prime 12539 := by
  apply nodeValid_prime [2, 6269] ⟨12539, 2, [(2, 1), (6269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6269
  · decide +kernel

theorem prime_12799 : Nat.Prime 12799 := by
  apply nodeValid_prime [2, 3, 79] ⟨12799, 13, [(2, 1), (3, 4), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_13841 : Nat.Prime 13841 := by
  apply nodeValid_prime [2, 5, 173] ⟨13841, 6, [(2, 4), (5, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_15629 : Nat.Prime 15629 := by
  apply nodeValid_prime [2, 3907] ⟨15629, 2, [(2, 2), (3907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3907
  · decide +kernel

theorem prime_16363 : Nat.Prime 16363 := by
  apply nodeValid_prime [2, 3, 101] ⟨16363, 2, [(2, 1), (3, 4), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_16649 : Nat.Prime 16649 := by
  apply nodeValid_prime [2, 2081] ⟨16649, 3, [(2, 3), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2081
  · decide +kernel

theorem prime_16657 : Nat.Prime 16657 := by
  apply nodeValid_prime [2, 3, 347] ⟨16657, 5, [(2, 4), (3, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
  · decide +kernel

theorem prime_19553 : Nat.Prime 19553 := by
  apply nodeValid_prime [2, 13, 47] ⟨19553, 3, [(2, 5), (13, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_19571 : Nat.Prime 19571 := by
  apply nodeValid_prime [2, 5, 19, 103] ⟨19571, 2, [(2, 1), (5, 1), (19, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_103
  · decide +kernel

theorem prime_21559 : Nat.Prime 21559 := by
  apply nodeValid_prime [2, 3, 3593] ⟨21559, 15, [(2, 1), (3, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3593
  · decide +kernel

theorem prime_22111 : Nat.Prime 22111 := by
  apply nodeValid_prime [2, 3, 5, 11, 67] ⟨22111, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_22573 : Nat.Prime 22573 := by
  apply nodeValid_prime [2, 3, 11, 19] ⟨22573, 6, [(2, 2), (3, 3), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_24103 : Nat.Prime 24103 := by
  apply nodeValid_prime [2, 3, 13, 103] ⟨24103, 5, [(2, 1), (3, 2), (13, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
  · decide +kernel

theorem prime_24877 : Nat.Prime 24877 := by
  apply nodeValid_prime [2, 3, 691] ⟨24877, 5, [(2, 2), (3, 2), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
  · decide +kernel

theorem prime_28631 : Nat.Prime 28631 := by
  apply nodeValid_prime [2, 5, 7, 409] ⟨28631, 11, [(2, 1), (5, 1), (7, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_409
  · decide +kernel

theorem prime_29129 : Nat.Prime 29129 := by
  apply nodeValid_prime [2, 11, 331] ⟨29129, 3, [(2, 3), (11, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_331
  · decide +kernel

theorem prime_31481 : Nat.Prime 31481 := by
  apply nodeValid_prime [2, 5, 787] ⟨31481, 6, [(2, 3), (5, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_787
  · decide +kernel

theorem prime_32323 : Nat.Prime 32323 := by
  apply nodeValid_prime [2, 3, 5387] ⟨32323, 2, [(2, 1), (3, 1), (5387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5387
  · decide +kernel

theorem prime_32993 : Nat.Prime 32993 := by
  apply nodeValid_prime [2, 1031] ⟨32993, 3, [(2, 5), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1031
  · decide +kernel

theorem prime_34283 : Nat.Prime 34283 := by
  apply nodeValid_prime [2, 61, 281] ⟨34283, 2, [(2, 1), (61, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_281
  · decide +kernel

theorem prime_34471 : Nat.Prime 34471 := by
  apply nodeValid_prime [2, 3, 5, 383] ⟨34471, 6, [(2, 1), (3, 2), (5, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
  · decide +kernel

theorem prime_34871 : Nat.Prime 34871 := by
  apply nodeValid_prime [2, 5, 11, 317] ⟨34871, 7, [(2, 1), (5, 1), (11, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_317
  · decide +kernel

theorem prime_37847 : Nat.Prime 37847 := by
  apply nodeValid_prime [2, 127, 149] ⟨37847, 5, [(2, 1), (127, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_149
  · decide +kernel

theorem prime_39733 : Nat.Prime 39733 := by
  apply nodeValid_prime [2, 3, 7, 11, 43] ⟨39733, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_41761 : Nat.Prime 41761 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨41761, 19, [(2, 5), (3, 2), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_44641 : Nat.Prime 44641 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨44641, 19, [(2, 5), (3, 2), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_51133 : Nat.Prime 51133 := by
  apply nodeValid_prime [2, 3, 4261] ⟨51133, 2, [(2, 2), (3, 1), (4261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4261
  · decide +kernel

theorem prime_52697 : Nat.Prime 52697 := by
  apply nodeValid_prime [2, 7, 941] ⟨52697, 3, [(2, 3), (7, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_941
  · decide +kernel

theorem prime_60937 : Nat.Prime 60937 := by
  apply nodeValid_prime [2, 3, 2539] ⟨60937, 10, [(2, 3), (3, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2539
  · decide +kernel

theorem prime_64109 : Nat.Prime 64109 := by
  apply nodeValid_prime [2, 11, 31, 47] ⟨64109, 2, [(2, 2), (11, 1), (31, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_47
  · decide +kernel

theorem prime_68567 : Nat.Prime 68567 := by
  apply nodeValid_prime [2, 34283] ⟨68567, 5, [(2, 1), (34283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34283
  · decide +kernel

theorem prime_72613 : Nat.Prime 72613 := by
  apply nodeValid_prime [2, 3, 2017] ⟨72613, 2, [(2, 2), (3, 2), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2017
  · decide +kernel

theorem prime_80111 : Nat.Prime 80111 := by
  apply nodeValid_prime [2, 5, 8011] ⟨80111, 11, [(2, 1), (5, 1), (8011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8011
  · decide +kernel

theorem prime_81637 : Nat.Prime 81637 := by
  apply nodeValid_prime [2, 3, 6803] ⟨81637, 2, [(2, 2), (3, 1), (6803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6803
  · decide +kernel

theorem prime_104683 : Nat.Prime 104683 := by
  apply nodeValid_prime [2, 3, 73, 239] ⟨104683, 2, [(2, 1), (3, 1), (73, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_239
  · decide +kernel

theorem prime_110597 : Nat.Prime 110597 := by
  apply nodeValid_prime [2, 43, 643] ⟨110597, 2, [(2, 2), (43, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_643
  · decide +kernel

theorem prime_110729 : Nat.Prime 110729 := by
  apply nodeValid_prime [2, 13841] ⟨110729, 3, [(2, 3), (13841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13841
  · decide +kernel

theorem prime_114997 : Nat.Prime 114997 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨114997, 2, [(2, 2), (3, 1), (7, 1), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_194977 : Nat.Prime 194977 := by
  apply nodeValid_prime [2, 3, 677] ⟨194977, 10, [(2, 5), (3, 2), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
  · decide +kernel

theorem prime_195787 : Nat.Prime 195787 := by
  apply nodeValid_prime [2, 3, 73, 149] ⟨195787, 7, [(2, 1), (3, 2), (73, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_149
  · decide +kernel

theorem prime_211801 : Nat.Prime 211801 := by
  apply nodeValid_prime [2, 3, 5, 353] ⟨211801, 13, [(2, 3), (3, 1), (5, 2), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
  · decide +kernel

theorem prime_250709 : Nat.Prime 250709 := by
  apply nodeValid_prime [2, 233, 269] ⟨250709, 2, [(2, 2), (233, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_269
  · decide +kernel

theorem prime_252457 : Nat.Prime 252457 := by
  apply nodeValid_prime [2, 3, 67, 157] ⟨252457, 10, [(2, 3), (3, 1), (67, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_157
  · decide +kernel

theorem prime_297019 : Nat.Prime 297019 := by
  apply nodeValid_prime [2, 3, 29, 569] ⟨297019, 2, [(2, 1), (3, 2), (29, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_569
  · decide +kernel

theorem prime_316051 : Nat.Prime 316051 := by
  apply nodeValid_prime [2, 3, 5, 7, 43] ⟨316051, 3, [(2, 1), (3, 1), (5, 2), (7, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_346589 : Nat.Prime 346589 := by
  apply nodeValid_prime [2, 11, 7877] ⟨346589, 2, [(2, 2), (11, 1), (7877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_7877
  · decide +kernel

theorem prime_347183 : Nat.Prime 347183 := by
  apply nodeValid_prime [2, 11, 43, 367] ⟨347183, 5, [(2, 1), (11, 1), (43, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_367
  · decide +kernel

theorem prime_376241 : Nat.Prime 376241 := by
  apply nodeValid_prime [2, 5, 4703] ⟨376241, 3, [(2, 4), (5, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4703
  · decide +kernel

theorem prime_435679 : Nat.Prime 435679 := by
  apply nodeValid_prime [2, 3, 72613] ⟨435679, 3, [(2, 1), (3, 1), (72613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_72613
  · decide +kernel

theorem prime_440537 : Nat.Prime 440537 := by
  apply nodeValid_prime [2, 53, 1039] ⟨440537, 3, [(2, 3), (53, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1039
  · decide +kernel

theorem prime_519907 : Nat.Prime 519907 := by
  apply nodeValid_prime [2, 3, 73, 1187] ⟨519907, 2, [(2, 1), (3, 1), (73, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_1187
  · decide +kernel

theorem prime_535349 : Nat.Prime 535349 := by
  apply nodeValid_prime [2, 11, 23] ⟨535349, 2, [(2, 2), (11, 1), (23, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_551717 : Nat.Prime 551717 := by
  apply nodeValid_prime [2, 11, 12539] ⟨551717, 2, [(2, 2), (11, 1), (12539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12539
  · decide +kernel

theorem prime_606653 : Nat.Prime 606653 := by
  apply nodeValid_prime [2, 37, 4099] ⟨606653, 2, [(2, 2), (37, 1), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_4099
  · decide +kernel

theorem prime_613597 : Nat.Prime 613597 := by
  apply nodeValid_prime [2, 3, 51133] ⟨613597, 5, [(2, 2), (3, 1), (51133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51133
  · decide +kernel

theorem prime_783149 : Nat.Prime 783149 := by
  apply nodeValid_prime [2, 195787] ⟨783149, 2, [(2, 2), (195787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_195787
  · decide +kernel

theorem prime_802159 : Nat.Prime 802159 := by
  apply nodeValid_prime [2, 3, 7, 71, 269] ⟨802159, 3, [(2, 1), (3, 1), (7, 1), (71, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_269
  · decide +kernel

theorem prime_906929 : Nat.Prime 906929 := by
  apply nodeValid_prime [2, 11, 5153] ⟨906929, 3, [(2, 4), (11, 1), (5153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_5153
  · decide +kernel

theorem prime_948547 : Nat.Prime 948547 := by
  apply nodeValid_prime [2, 3, 52697] ⟨948547, 3, [(2, 1), (3, 2), (52697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52697
  · decide +kernel

theorem prime_971921 : Nat.Prime 971921 := by
  apply nodeValid_prime [2, 5, 12149] ⟨971921, 3, [(2, 4), (5, 1), (12149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12149
  · decide +kernel

theorem prime_1753963 : Nat.Prime 1753963 := by
  apply nodeValid_prime [2, 3, 7, 41761] ⟨1753963, 2, [(2, 1), (3, 1), (7, 1), (41761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41761
  · decide +kernel

theorem prime_1917959 : Nat.Prime 1917959 := by
  apply nodeValid_prime [2, 7, 19571] ⟨1917959, 7, [(2, 1), (7, 2), (19571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19571
  · decide +kernel

theorem prime_1951823 : Nat.Prime 1951823 := by
  apply nodeValid_prime [2, 31, 31481] ⟨1951823, 5, [(2, 1), (31, 1), (31481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_31481
  · decide +kernel

theorem prime_2542913 : Nat.Prime 2542913 := by
  apply nodeValid_prime [2, 39733] ⟨2542913, 3, [(2, 6), (39733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39733
  · decide +kernel

theorem prime_2565161 : Nat.Prime 2565161 := by
  apply nodeValid_prime [2, 5, 13, 4933] ⟨2565161, 3, [(2, 3), (5, 1), (13, 1), (4933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4933
  · decide +kernel

theorem prime_3974759 : Nat.Prime 3974759 := by
  apply nodeValid_prime [2, 31, 64109] ⟨3974759, 17, [(2, 1), (31, 1), (64109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_64109
  · decide +kernel

theorem prime_4009001 : Nat.Prime 4009001 := by
  apply nodeValid_prime [2, 5, 19, 211] ⟨4009001, 3, [(2, 3), (5, 3), (19, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_211
  · decide +kernel

theorem prime_4075133 : Nat.Prime 4075133 := by
  apply nodeValid_prime [2, 89, 11447] ⟨4075133, 2, [(2, 2), (89, 1), (11447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_11447
  · decide +kernel

theorem prime_4112971 : Nat.Prime 4112971 := by
  apply nodeValid_prime [2, 3, 5, 47, 2917] ⟨4112971, 3, [(2, 1), (3, 1), (5, 1), (47, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_2917
  · decide +kernel

theorem prime_7498937 : Nat.Prime 7498937 := by
  apply nodeValid_prime [2, 29, 32323] ⟨7498937, 3, [(2, 3), (29, 1), (32323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_32323
  · decide +kernel

theorem prime_7806797 : Nat.Prime 7806797 := by
  apply nodeValid_prime [2, 19, 139, 739] ⟨7806797, 2, [(2, 2), (19, 1), (139, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_139
    · exact prime_739
  · decide +kernel

theorem prime_10041643 : Nat.Prime 10041643 := by
  apply nodeValid_prime [2, 3, 13, 3301] ⟨10041643, 5, [(2, 1), (3, 2), (13, 2), (3301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3301
  · decide +kernel

theorem prime_10572889 : Nat.Prime 10572889 := by
  apply nodeValid_prime [2, 3, 440537] ⟨10572889, 7, [(2, 3), (3, 1), (440537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_440537
  · decide +kernel

theorem prime_11065333 : Nat.Prime 11065333 := by
  apply nodeValid_prime [2, 3, 59, 15629] ⟨11065333, 5, [(2, 2), (3, 1), (59, 1), (15629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_15629
  · decide +kernel

theorem prime_11656391 : Nat.Prime 11656391 := by
  apply nodeValid_prime [2, 5, 17, 68567] ⟨11656391, 19, [(2, 1), (5, 1), (17, 1), (68567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_68567
  · decide +kernel

theorem prime_12848377 : Nat.Prime 12848377 := by
  apply nodeValid_prime [2, 3, 535349] ⟨12848377, 7, [(2, 3), (3, 1), (535349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_535349
  · decide +kernel

theorem prime_12908851 : Nat.Prime 12908851 := by
  apply nodeValid_prime [2, 3, 5, 41, 2099] ⟨12908851, 3, [(2, 1), (3, 1), (5, 2), (41, 1), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_2099
  · decide +kernel

theorem prime_14557397 : Nat.Prime 14557397 := by
  apply nodeValid_prime [2, 7, 519907] ⟨14557397, 2, [(2, 2), (7, 1), (519907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_519907
  · decide +kernel

theorem prime_15772979 : Nat.Prime 15772979 := by
  apply nodeValid_prime [2, 13, 606653] ⟨15772979, 6, [(2, 1), (13, 1), (606653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_606653
  · decide +kernel

theorem prime_17200723 : Nat.Prime 17200723 := by
  apply nodeValid_prime [2, 3, 7, 11, 31, 1201] ⟨17200723, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (31, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_1201
  · decide +kernel

theorem prime_19171337 : Nat.Prime 19171337 := by
  apply nodeValid_prime [2, 379, 6323] ⟨19171337, 3, [(2, 3), (379, 1), (6323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_6323
  · decide +kernel

theorem prime_24054007 : Nat.Prime 24054007 := by
  apply nodeValid_prime [2, 3, 4009001] ⟨24054007, 6, [(2, 1), (3, 1), (4009001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4009001
  · decide +kernel

theorem prime_31545959 : Nat.Prime 31545959 := by
  apply nodeValid_prime [2, 15772979] ⟨31545959, 7, [(2, 1), (15772979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15772979
  · decide +kernel

theorem prime_35795351 : Nat.Prime 35795351 := by
  apply nodeValid_prime [2, 5, 43, 16649] ⟨35795351, 11, [(2, 1), (5, 2), (43, 1), (16649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_16649
  · decide +kernel

theorem prime_35867179 : Nat.Prime 35867179 := by
  apply nodeValid_prime [2, 3, 17, 89, 439] ⟨35867179, 2, [(2, 1), (3, 3), (17, 1), (89, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_89
    · exact prime_439
  · decide +kernel

theorem prime_49132823 : Nat.Prime 49132823 := by
  apply nodeValid_prime [2, 17, 19, 4003] ⟨49132823, 5, [(2, 1), (17, 1), (19, 2), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_4003
  · decide +kernel

theorem prime_49912127 : Nat.Prime 49912127 := by
  apply nodeValid_prime [2, 11, 19, 97, 1231] ⟨49912127, 5, [(2, 1), (11, 1), (19, 1), (97, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_97
    · exact prime_1231
  · decide +kernel

theorem prime_55492867 : Nat.Prime 55492867 := by
  apply nodeValid_prime [2, 3, 11, 13, 21559] ⟨55492867, 2, [(2, 1), (3, 2), (11, 1), (13, 1), (21559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_21559
  · decide +kernel

theorem prime_55809001 : Nat.Prime 55809001 := by
  apply nodeValid_prime [2, 3, 5, 13, 53] ⟨55809001, 11, [(2, 3), (3, 4), (5, 3), (13, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_59991497 : Nat.Prime 59991497 := by
  apply nodeValid_prime [2, 7498937] ⟨59991497, 3, [(2, 3), (7498937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7498937
  · decide +kernel

theorem prime_138863369 : Nat.Prime 138863369 := by
  apply nodeValid_prime [2, 7, 29, 37, 2311] ⟨138863369, 3, [(2, 3), (7, 1), (29, 1), (37, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_37
    · exact prime_2311
  · decide +kernel

theorem prime_163953133 : Nat.Prime 163953133 := by
  apply nodeValid_prime [2, 3, 7, 1951823] ⟨163953133, 2, [(2, 2), (3, 1), (7, 1), (1951823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1951823
  · decide +kernel

theorem prime_193503589 : Nat.Prime 193503589 := by
  apply nodeValid_prime [2, 3, 17, 948547] ⟨193503589, 2, [(2, 2), (3, 1), (17, 1), (948547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_948547
  · decide +kernel

theorem prime_273280157 : Nat.Prime 273280157 := by
  apply nodeValid_prime [2, 83, 433, 1901] ⟨273280157, 2, [(2, 2), (83, 1), (433, 1), (1901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_433
    · exact prime_1901
  · decide +kernel

theorem prime_294796939 : Nat.Prime 294796939 := by
  apply nodeValid_prime [2, 3, 49132823] ⟨294796939, 2, [(2, 1), (3, 1), (49132823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49132823
  · decide +kernel

theorem prime_295987007 : Nat.Prime 295987007 := by
  apply nodeValid_prime [2, 7, 61, 346589] ⟨295987007, 7, [(2, 1), (7, 1), (61, 1), (346589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_346589
  · decide +kernel

theorem prime_412165597 : Nat.Prime 412165597 := by
  apply nodeValid_prime [2, 3, 137, 250709] ⟨412165597, 5, [(2, 2), (3, 1), (137, 1), (250709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_250709
  · decide +kernel

theorem prime_413374937 : Nat.Prime 413374937 := by
  apply nodeValid_prime [2, 13, 3974759] ⟨413374937, 3, [(2, 3), (13, 1), (3974759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3974759
  · decide +kernel

theorem prime_534686231 : Nat.Prime 534686231 := by
  apply nodeValid_prime [2, 5, 13, 4112971] ⟨534686231, 7, [(2, 1), (5, 1), (13, 1), (4112971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4112971
  · decide +kernel

theorem prime_722640799 : Nat.Prime 722640799 := by
  apply nodeValid_prime [2, 3, 11, 110597] ⟨722640799, 3, [(2, 1), (3, 3), (11, 2), (110597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_110597
  · decide +kernel

theorem prime_905204317 : Nat.Prime 905204317 := by
  apply nodeValid_prime [2, 3, 8513, 8861] ⟨905204317, 2, [(2, 2), (3, 1), (8513, 1), (8861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8513
    · exact prime_8861
  · decide +kernel

theorem prime_1203522013 : Nat.Prime 1203522013 := by
  apply nodeValid_prime [2, 3, 7, 11, 23, 43, 439] ⟨1203522013, 5, [(2, 2), (3, 2), (7, 1), (11, 1), (23, 1), (43, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_43
    · exact prime_439
  · decide +kernel

theorem prime_1579622899 : Nat.Prime 1579622899 := by
  apply nodeValid_prime [2, 3, 7, 17, 316051] ⟨1579622899, 3, [(2, 1), (3, 1), (7, 2), (17, 1), (316051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_316051
  · decide +kernel

theorem prime_1836655277 : Nat.Prime 1836655277 := by
  apply nodeValid_prime [2, 179, 2565161] ⟨1836655277, 2, [(2, 2), (179, 1), (2565161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_2565161
  · decide +kernel

theorem prime_1935035891 : Nat.Prime 1935035891 := by
  apply nodeValid_prime [2, 5, 193503589] ⟨1935035891, 2, [(2, 1), (5, 1), (193503589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193503589
  · decide +kernel

theorem prime_2278237349 : Nat.Prime 2278237349 := by
  apply nodeValid_prime [2, 19553, 29129] ⟨2278237349, 2, [(2, 2), (19553, 1), (29129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19553
    · exact prime_29129
  · decide +kernel

theorem prime_3513058651 : Nat.Prime 3513058651 := by
  apply nodeValid_prime [2, 3, 5, 7806797] ⟨3513058651, 2, [(2, 1), (3, 2), (5, 2), (7806797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7806797
  · decide +kernel

theorem prime_4557793711 : Nat.Prime 4557793711 := by
  apply nodeValid_prime [2, 3, 5, 1861, 81637] ⟨4557793711, 3, [(2, 1), (3, 1), (5, 1), (1861, 1), (81637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1861
    · exact prime_81637
  · decide +kernel

theorem prime_7929666751 : Nat.Prime 7929666751 := by
  apply nodeValid_prime [2, 3, 5, 10572889] ⟨7929666751, 3, [(2, 1), (3, 1), (5, 3), (10572889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10572889
  · decide +kernel

theorem prime_8152142321 : Nat.Prime 8152142321 := by
  apply nodeValid_prime [2, 5, 7, 14557397] ⟨8152142321, 3, [(2, 4), (5, 1), (7, 1), (14557397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_14557397
  · decide +kernel

theorem prime_9972440689 : Nat.Prime 9972440689 := by
  apply nodeValid_prime [2, 3, 7, 37, 802159] ⟨9972440689, 11, [(2, 4), (3, 1), (7, 1), (37, 1), (802159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_802159
  · decide +kernel

theorem prime_48108955733 : Nat.Prime 48108955733 := by
  apply nodeValid_prime [2, 29, 43, 1279, 7541] ⟨48108955733, 2, [(2, 2), (29, 1), (43, 1), (1279, 1), (7541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_43
    · exact prime_1279
    · exact prime_7541
  · decide +kernel

theorem prime_50547931853 : Nat.Prime 50547931853 := by
  apply nodeValid_prime [2, 11, 17, 4057, 16657] ⟨50547931853, 2, [(2, 2), (11, 1), (17, 1), (4057, 1), (16657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_4057
    · exact prime_16657
  · decide +kernel

theorem prime_95156000677 : Nat.Prime 95156000677 := by
  apply nodeValid_prime [2, 3, 11, 137, 1753963] ⟨95156000677, 2, [(2, 2), (3, 2), (11, 1), (137, 1), (1753963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
    · exact prime_1753963
  · decide +kernel

theorem prime_95156001013 : Nat.Prime 95156001013 := by
  apply nodeValid_prime [2, 3, 7929666751] ⟨95156001013, 2, [(2, 2), (3, 1), (7929666751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7929666751
  · decide +kernel

theorem prime_95156009537 : Nat.Prime 95156009537 := by
  apply nodeValid_prime [2, 7, 2029, 104683] ⟨95156009537, 3, [(2, 6), (7, 1), (2029, 1), (104683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2029
    · exact prime_104683
  · decide +kernel

theorem prime_95420723407 : Nat.Prime 95420723407 := by
  apply nodeValid_prime [2, 3, 97, 163953133] ⟨95420723407, 5, [(2, 1), (3, 1), (97, 1), (163953133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_163953133
  · decide +kernel

theorem prime_95420742323 : Nat.Prime 95420742323 := by
  apply nodeValid_prime [2, 31, 103, 1277, 11701] ⟨95420742323, 2, [(2, 1), (31, 1), (103, 1), (1277, 1), (11701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_103
    · exact prime_1277
    · exact prime_11701
  · decide +kernel

theorem prime_95420744693 : Nat.Prime 95420744693 := by
  apply nodeValid_prime [2, 7, 13, 11411, 22973] ⟨95420744693, 2, [(2, 2), (7, 1), (13, 1), (11411, 1), (22973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_11411
    · exact prime_22973
  · decide +kernel

theorem prime_95685940897 : Nat.Prime 95685940897 := by
  apply nodeValid_prime [2, 3, 7, 13, 139, 11257] ⟨95685940897, 5, [(2, 5), (3, 1), (7, 2), (13, 1), (139, 1), (11257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_139
    · exact prime_11257
  · decide +kernel

theorem prime_95685968659 : Nat.Prime 95685968659 := by
  apply nodeValid_prime [2, 3, 7, 2278237349] ⟨95685968659, 2, [(2, 1), (3, 1), (7, 1), (2278237349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2278237349
  · decide +kernel

theorem prime_95685968671 : Nat.Prime 95685968671 := by
  apply nodeValid_prime [2, 3, 5, 277, 349, 32993] ⟨95685968671, 6, [(2, 1), (3, 1), (5, 1), (277, 1), (349, 1), (32993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_277
    · exact prime_349
    · exact prime_32993
  · decide +kernel

theorem prime_95951657603 : Nat.Prime 95951657603 := by
  apply nodeValid_prime [2, 53, 905204317] ⟨95951657603, 2, [(2, 1), (53, 1), (905204317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_905204317
  · decide +kernel

theorem prime_95951679437 : Nat.Prime 95951679437 := by
  apply nodeValid_prime [2, 1867, 12848377] ⟨95951679437, 2, [(2, 2), (1867, 1), (12848377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1867
    · exact prime_12848377
  · decide +kernel

theorem prime_95951680907 : Nat.Prime 95951680907 := by
  apply nodeValid_prime [2, 383, 5197, 24103] ⟨95951680907, 2, [(2, 1), (383, 1), (5197, 1), (24103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_5197
    · exact prime_24103
  · decide +kernel

theorem prime_96217876493 : Nat.Prime 96217876493 := by
  apply nodeValid_prime [2, 83, 8311, 34871] ⟨96217876493, 2, [(2, 2), (83, 1), (8311, 1), (34871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_8311
    · exact prime_34871
  · decide +kernel

theorem prime_96217911467 : Nat.Prime 96217911467 := by
  apply nodeValid_prime [2, 48108955733] ⟨96217911467, 2, [(2, 1), (48108955733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48108955733
  · decide +kernel

theorem prime_96217911469 : Nat.Prime 96217911469 := by
  apply nodeValid_prime [2, 3, 7, 421, 906929] ⟨96217911469, 2, [(2, 2), (3, 2), (7, 1), (421, 1), (906929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_421
    · exact prime_906929
  · decide +kernel

theorem prime_96484593131 : Nat.Prime 96484593131 := by
  apply nodeValid_prime [2, 5, 23, 31, 827, 16363] ⟨96484593131, 6, [(2, 1), (5, 1), (23, 1), (31, 1), (827, 1), (16363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_31
    · exact prime_827
    · exact prime_16363
  · decide +kernel

theorem prime_96484598747 : Nat.Prime 96484598747 := by
  apply nodeValid_prime [2, 37, 67, 2053, 9479] ⟨96484598747, 2, [(2, 1), (37, 1), (67, 1), (2053, 1), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_67
    · exact prime_2053
    · exact prime_9479
  · decide +kernel

theorem prime_96484599983 : Nat.Prime 96484599983 := by
  apply nodeValid_prime [2, 110729, 435679] ⟨96484599983, 5, [(2, 1), (110729, 1), (435679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_110729
    · exact prime_435679
  · decide +kernel

theorem prime_96751793759 : Nat.Prime 96751793759 := by
  apply nodeValid_prime [2, 223, 277, 783149] ⟨96751793759, 11, [(2, 1), (223, 1), (277, 1), (783149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_277
    · exact prime_783149
  · decide +kernel

theorem prime_96751794551 : Nat.Prime 96751794551 := by
  apply nodeValid_prime [2, 5, 1935035891] ⟨96751794551, 11, [(2, 1), (5, 2), (1935035891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1935035891
  · decide +kernel

theorem prime_96751807687 : Nat.Prime 96751807687 := by
  apply nodeValid_prime [2, 3, 1319, 4075133] ⟨96751807687, 5, [(2, 1), (3, 2), (1319, 1), (4075133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1319
    · exact prime_4075133
  · decide +kernel

theorem prime_97019503253 : Nat.Prime 97019503253 := by
  apply nodeValid_prime [2, 7, 5647, 613597] ⟨97019503253, 2, [(2, 2), (7, 1), (5647, 1), (613597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5647
    · exact prime_613597
  · decide +kernel

theorem prime_97019503937 : Nat.Prime 97019503937 := by
  apply nodeValid_prime [2, 24877, 60937] ⟨97019503937, 3, [(2, 6), (24877, 1), (60937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_24877
    · exact prime_60937
  · decide +kernel

theorem prime_97019518991 : Nat.Prime 97019518991 := by
  apply nodeValid_prime [2, 5, 239, 353, 114997] ⟨97019518991, 13, [(2, 1), (5, 1), (239, 1), (353, 1), (114997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_353
    · exact prime_114997
  · decide +kernel

theorem prime_97287735893 : Nat.Prime 97287735893 := by
  apply nodeValid_prime [2, 89, 273280157] ⟨97287735893, 2, [(2, 2), (89, 1), (273280157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_273280157
  · decide +kernel

theorem prime_97287737167 : Nat.Prime 97287737167 := by
  apply nodeValid_prime [2, 3, 311, 607, 28631] ⟨97287737167, 3, [(2, 1), (3, 2), (311, 1), (607, 1), (28631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_607
    · exact prime_28631
  · decide +kernel

theorem prime_97287737557 : Nat.Prime 97287737557 := by
  apply nodeValid_prime [2, 3, 257, 31545959] ⟨97287737557, 5, [(2, 2), (3, 1), (257, 1), (31545959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_31545959
  · decide +kernel

theorem prime_97556460187 : Nat.Prime 97556460187 := by
  apply nodeValid_prime [2, 3, 293, 55492867] ⟨97556460187, 3, [(2, 1), (3, 1), (293, 1), (55492867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_55492867
  · decide +kernel

theorem prime_97556484589 : Nat.Prime 97556484589 := by
  apply nodeValid_prime [2, 3, 101, 271, 297019] ⟨97556484589, 2, [(2, 2), (3, 1), (101, 1), (271, 1), (297019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_271
    · exact prime_297019
  · decide +kernel

theorem prime_97556485133 : Nat.Prime 97556485133 := by
  apply nodeValid_prime [2, 59, 413374937] ⟨97556485133, 2, [(2, 2), (59, 1), (413374937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_413374937
  · decide +kernel

theorem prime_97825686107 : Nat.Prime 97825686107 := by
  apply nodeValid_prime [2, 4871, 10041643] ⟨97825686107, 2, [(2, 1), (4871, 1), (10041643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4871
    · exact prime_10041643
  · decide +kernel

theorem prime_97825705891 : Nat.Prime 97825705891 := by
  apply nodeValid_prime [2, 3, 5, 11, 167, 257, 6907] ⟨97825705891, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (167, 1), (257, 1), (6907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_167
    · exact prime_257
    · exact prime_6907
  · decide +kernel

theorem prime_97825707853 : Nat.Prime 97825707853 := by
  apply nodeValid_prime [2, 3, 8152142321] ⟨97825707853, 2, [(2, 2), (3, 1), (8152142321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8152142321
  · decide +kernel

theorem prime_98095411889 : Nat.Prime 98095411889 := by
  apply nodeValid_prime [2, 2411, 2542913] ⟨98095411889, 3, [(2, 4), (2411, 1), (2542913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2411
    · exact prime_2542913
  · decide +kernel

theorem prime_98095412087 : Nat.Prime 98095412087 := by
  apply nodeValid_prime [2, 7, 17, 412165597] ⟨98095412087, 5, [(2, 1), (7, 1), (17, 1), (412165597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_412165597
  · decide +kernel

theorem prime_98095412231 : Nat.Prime 98095412231 := by
  apply nodeValid_prime [2, 5, 41, 199, 569, 2113] ⟨98095412231, 11, [(2, 1), (5, 1), (41, 1), (199, 1), (569, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_199
    · exact prime_569
    · exact prime_2113
  · decide +kernel

theorem prime_98365623931 : Nat.Prime 98365623931 := by
  apply nodeValid_prime [2, 3, 5, 7, 283, 551717] ⟨98365623931, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (283, 1), (551717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_283
    · exact prime_551717
  · decide +kernel

theorem prime_98365624549 : Nat.Prime 98365624549 := by
  apply nodeValid_prime [2, 3, 229, 35795351] ⟨98365624549, 6, [(2, 2), (3, 1), (229, 1), (35795351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_35795351
  · decide +kernel

theorem prime_98365642229 : Nat.Prime 98365642229 := by
  apply nodeValid_prime [2, 7, 3513058651] ⟨98365642229, 3, [(2, 2), (7, 1), (3513058651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3513058651
  · decide +kernel

theorem prime_98636374607 : Nat.Prime 98636374607 := by
  apply nodeValid_prime [2, 7, 11, 659, 971921] ⟨98636374607, 5, [(2, 1), (7, 1), (11, 1), (659, 1), (971921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_659
    · exact prime_971921
  · decide +kernel

theorem prime_98636378363 : Nat.Prime 98636378363 := by
  apply nodeValid_prime [2, 4457, 11065333] ⟨98636378363, 2, [(2, 1), (4457, 1), (11065333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4457
    · exact prime_11065333
  · decide +kernel

theorem prime_98636380643 : Nat.Prime 98636380643 := by
  apply nodeValid_prime [2, 4231, 11656391] ⟨98636380643, 2, [(2, 1), (4231, 1), (11656391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4231
    · exact prime_11656391
  · decide +kernel

theorem prime_98907603461 : Nat.Prime 98907603461 := by
  apply nodeValid_prime [2, 5, 19, 1031, 252457] ⟨98907603461, 2, [(2, 2), (5, 1), (19, 1), (1031, 1), (252457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1031
    · exact prime_252457
  · decide +kernel

theorem prime_98907604153 : Nat.Prime 98907604153 := by
  apply nodeValid_prime [2, 3, 7, 7349, 80111] ⟨98907604153, 13, [(2, 3), (3, 1), (7, 1), (7349, 1), (80111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7349
    · exact prime_80111
  · decide +kernel

theorem prime_98907616363 : Nat.Prime 98907616363 := by
  apply nodeValid_prime [2, 3, 1277, 12908851] ⟨98907616363, 5, [(2, 1), (3, 1), (1277, 1), (12908851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1277
    · exact prime_12908851
  · decide +kernel

theorem prime_99179368819 : Nat.Prime 99179368819 := by
  apply nodeValid_prime [2, 3, 31, 17200723] ⟨99179368819, 3, [(2, 1), (3, 1), (31, 2), (17200723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_17200723
  · decide +kernel

theorem prime_99179384959 : Nat.Prime 99179384959 := by
  apply nodeValid_prime [2, 3, 1836655277] ⟨99179384959, 6, [(2, 1), (3, 3), (1836655277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1836655277
  · decide +kernel

theorem prime_99179385047 : Nat.Prime 99179385047 := by
  apply nodeValid_prime [2, 7, 19, 991, 376241] ⟨99179385047, 5, [(2, 1), (7, 1), (19, 1), (991, 1), (376241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_991
    · exact prime_376241
  · decide +kernel

theorem prime_99451634353 : Nat.Prime 99451634353 := by
  apply nodeValid_prime [2, 3, 7, 295987007] ⟨99451634353, 5, [(2, 4), (3, 1), (7, 1), (295987007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_295987007
  · decide +kernel

theorem prime_99451638967 : Nat.Prime 99451638967 := by
  apply nodeValid_prime [2, 3, 31, 534686231] ⟨99451638967, 3, [(2, 1), (3, 1), (31, 1), (534686231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_534686231
  · decide +kernel

theorem prime_99451639783 : Nat.Prime 99451639783 := by
  apply nodeValid_prime [2, 3, 11, 55809001] ⟨99451639783, 3, [(2, 1), (3, 4), (11, 1), (55809001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_55809001
  · decide +kernel

theorem prime_99724406891 : Nat.Prime 99724406891 := by
  apply nodeValid_prime [2, 5, 9972440689] ⟨99724406891, 2, [(2, 1), (5, 1), (9972440689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9972440689
  · decide +kernel

theorem prime_99724429747 : Nat.Prime 99724429747 := by
  apply nodeValid_prime [2, 3, 37, 49912127] ⟨99724429747, 5, [(2, 1), (3, 3), (37, 1), (49912127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_49912127
  · decide +kernel

theorem prime_99724430263 : Nat.Prime 99724430263 := by
  apply nodeValid_prime [2, 3, 23, 722640799] ⟨99724430263, 6, [(2, 1), (3, 1), (23, 1), (722640799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_722640799
  · decide +kernel

theorem prime_99997682263 : Nat.Prime 99997682263 := by
  apply nodeValid_prime [2, 3, 101, 4787, 34471] ⟨99997682263, 5, [(2, 1), (3, 1), (101, 1), (4787, 1), (34471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_4787
    · exact prime_34471
  · decide +kernel

theorem prime_99997693793 : Nat.Prime 99997693793 := by
  apply nodeValid_prime [2, 163, 19171337] ⟨99997693793, 3, [(2, 5), (163, 1), (19171337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_19171337
  · decide +kernel

theorem prime_99997695053 : Nat.Prime 99997695053 := by
  apply nodeValid_prime [2, 17, 41, 35867179] ⟨99997695053, 2, [(2, 2), (17, 1), (41, 1), (35867179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_35867179
  · decide +kernel

theorem prime_100271461621 : Nat.Prime 100271461621 := by
  apply nodeValid_prime [2, 3, 5, 11, 1861, 81637] ⟨100271461621, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (1861, 1), (81637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1861
    · exact prime_81637
  · decide +kernel

theorem prime_100271461643 : Nat.Prime 100271461643 := by
  apply nodeValid_prime [2, 11, 4557793711] ⟨100271461643, 2, [(2, 1), (11, 1), (4557793711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4557793711
  · decide +kernel

theorem prime_100271461681 : Nat.Prime 100271461681 := by
  apply nodeValid_prime [2, 3, 5, 13, 31, 12799] ⟨100271461681, 7, [(2, 4), (3, 5), (5, 1), (13, 1), (31, 1), (12799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_12799
  · decide +kernel

theorem prime_100545747119 : Nat.Prime 100545747119 := by
  apply nodeValid_prime [2, 97, 2447, 211801] ⟨100545747119, 11, [(2, 1), (97, 1), (2447, 1), (211801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_2447
    · exact prime_211801
  · decide +kernel

theorem prime_100545748973 : Nat.Prime 100545748973 := by
  apply nodeValid_prime [2, 419, 59991497] ⟨100545748973, 2, [(2, 2), (419, 1), (59991497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_59991497
  · decide +kernel

theorem prime_100545749261 : Nat.Prime 100545749261 := by
  apply nodeValid_prime [2, 5, 11, 19, 24054007] ⟨100545749261, 2, [(2, 2), (5, 1), (11, 1), (19, 1), (24054007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_24054007
  · decide +kernel

theorem prime_100820543807 : Nat.Prime 100820543807 := by
  apply nodeValid_prime [2, 101, 22111, 22573] ⟨100820543807, 5, [(2, 1), (101, 1), (22111, 1), (22573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_22111
    · exact prime_22573
  · decide +kernel

theorem prime_100820553139 : Nat.Prime 100820553139 := by
  apply nodeValid_prime [2, 3, 19, 294796939] ⟨100820553139, 2, [(2, 1), (3, 2), (19, 1), (294796939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_294796939
  · decide +kernel

theorem prime_100820554469 : Nat.Prime 100820554469 := by
  apply nodeValid_prime [2, 19, 3821, 347183] ⟨100820554469, 2, [(2, 2), (19, 1), (3821, 1), (347183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3821
    · exact prime_347183
  · decide +kernel

theorem prime_101095849093 : Nat.Prime 101095849093 := by
  apply nodeValid_prime [2, 3, 7, 1203522013] ⟨101095849093, 5, [(2, 2), (3, 1), (7, 1), (1203522013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1203522013
  · decide +kernel

theorem prime_101095863707 : Nat.Prime 101095863707 := by
  apply nodeValid_prime [2, 50547931853] ⟨101095863707, 2, [(2, 1), (50547931853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_50547931853
  · decide +kernel

theorem prime_101095865537 : Nat.Prime 101095865537 := by
  apply nodeValid_prime [2, 1579622899] ⟨101095865537, 3, [(2, 6), (1579622899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1579622899
  · decide +kernel

theorem prime_101371661933 : Nat.Prime 101371661933 := by
  apply nodeValid_prime [2, 19, 6841, 194977] ⟨101371661933, 2, [(2, 2), (19, 1), (6841, 1), (194977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_6841
    · exact prime_194977
  · decide +kernel

theorem prime_101371673701 : Nat.Prime 101371673701 := by
  apply nodeValid_prime [2, 3, 5, 11, 967, 10589] ⟨101371673701, 2, [(2, 2), (3, 2), (5, 2), (11, 1), (967, 1), (10589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_967
    · exact prime_10589
  · decide +kernel

theorem prime_101371675621 : Nat.Prime 101371675621 := by
  apply nodeValid_prime [2, 3, 5, 37847, 44641] ⟨101371675621, 6, [(2, 2), (3, 1), (5, 1), (37847, 1), (44641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37847
    · exact prime_44641
  · decide +kernel

theorem prime_101647986109 : Nat.Prime 101647986109 := by
  apply nodeValid_prime [2, 3, 61, 138863369] ⟨101647986109, 6, [(2, 2), (3, 1), (61, 1), (138863369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_138863369
  · decide +kernel

theorem prime_101647991083 : Nat.Prime 101647991083 := by
  apply nodeValid_prime [2, 3, 11, 73, 1917959] ⟨101647991083, 7, [(2, 1), (3, 1), (11, 2), (73, 1), (1917959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_1917959
  · decide +kernel

theorem prime_101647991801 : Nat.Prime 101647991801 := by
  apply nodeValid_prime [2, 5, 83, 757, 8089] ⟨101647991801, 3, [(2, 3), (5, 2), (83, 1), (757, 1), (8089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_757
    · exact prime_8089
  · decide +kernel

end Sude.Lucas.Generated
