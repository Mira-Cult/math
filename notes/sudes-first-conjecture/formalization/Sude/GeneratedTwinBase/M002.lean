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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0077
import Sude.GeneratedTwinBase.M000

/-! Generated Lucas nodes for the FT base; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_24109 : Nat.Prime 24109 := by
  apply nodeValid_prime [2, 3, 7, 41] ⟨24109, 2, [(2, 2), (3, 1), (7, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_24121 : Nat.Prime 24121 := by
  apply nodeValid_prime [2, 3, 5, 67] ⟨24121, 13, [(2, 3), (3, 2), (5, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_24337 : Nat.Prime 24337 := by
  apply nodeValid_prime [2, 3, 13] ⟨24337, 5, [(2, 4), (3, 2), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_24391 : Nat.Prime 24391 := by
  apply nodeValid_prime [2, 3, 5, 271] ⟨24391, 3, [(2, 1), (3, 2), (5, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
  · decide +kernel

theorem prime_24407 : Nat.Prime 24407 := by
  apply nodeValid_prime [2, 12203] ⟨24407, 5, [(2, 1), (12203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12203
  · decide +kernel

theorem prime_24419 : Nat.Prime 24419 := by
  apply nodeValid_prime [2, 29, 421] ⟨24419, 2, [(2, 1), (29, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_421
  · decide +kernel

theorem prime_24421 : Nat.Prime 24421 := by
  apply nodeValid_prime [2, 3, 5, 11, 37] ⟨24421, 7, [(2, 2), (3, 1), (5, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_24443 : Nat.Prime 24443 := by
  apply nodeValid_prime [2, 11, 101] ⟨24443, 2, [(2, 1), (11, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_101
  · decide +kernel

theorem prime_24509 : Nat.Prime 24509 := by
  apply nodeValid_prime [2, 11, 557] ⟨24509, 2, [(2, 2), (11, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_557
  · decide +kernel

theorem prime_24517 : Nat.Prime 24517 := by
  apply nodeValid_prime [2, 3, 227] ⟨24517, 5, [(2, 2), (3, 3), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
  · decide +kernel

theorem prime_24533 : Nat.Prime 24533 := by
  apply nodeValid_prime [2, 6133] ⟨24533, 2, [(2, 2), (6133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6133
  · decide +kernel

theorem prime_24659 : Nat.Prime 24659 := by
  apply nodeValid_prime [2, 12329] ⟨24659, 2, [(2, 1), (12329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12329
  · decide +kernel

theorem prime_24671 : Nat.Prime 24671 := by
  apply nodeValid_prime [2, 5, 2467] ⟨24671, 11, [(2, 1), (5, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2467
  · decide +kernel

theorem prime_24683 : Nat.Prime 24683 := by
  apply nodeValid_prime [2, 7, 41, 43] ⟨24683, 2, [(2, 1), (7, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_24691 : Nat.Prime 24691 := by
  apply nodeValid_prime [2, 3, 5, 823] ⟨24691, 2, [(2, 1), (3, 1), (5, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_823
  · decide +kernel

theorem prime_24697 : Nat.Prime 24697 := by
  apply nodeValid_prime [2, 3, 7] ⟨24697, 5, [(2, 3), (3, 2), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_24709 : Nat.Prime 24709 := by
  apply nodeValid_prime [2, 3, 29, 71] ⟨24709, 2, [(2, 2), (3, 1), (29, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_71
  · decide +kernel

theorem prime_24767 : Nat.Prime 24767 := by
  apply nodeValid_prime [2, 7, 29, 61] ⟨24767, 5, [(2, 1), (7, 1), (29, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_61
  · decide +kernel

theorem prime_24781 : Nat.Prime 24781 := by
  apply nodeValid_prime [2, 3, 5, 7, 59] ⟨24781, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_24809 : Nat.Prime 24809 := by
  apply nodeValid_prime [2, 7, 443] ⟨24809, 6, [(2, 3), (7, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_443
  · decide +kernel

theorem prime_24847 : Nat.Prime 24847 := by
  apply nodeValid_prime [2, 3, 41, 101] ⟨24847, 3, [(2, 1), (3, 1), (41, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_101
  · decide +kernel

theorem prime_24851 : Nat.Prime 24851 := by
  apply nodeValid_prime [2, 5, 7, 71] ⟨24851, 2, [(2, 1), (5, 2), (7, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_24917 : Nat.Prime 24917 := by
  apply nodeValid_prime [2, 6229] ⟨24917, 2, [(2, 2), (6229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6229
  · decide +kernel

theorem prime_24953 : Nat.Prime 24953 := by
  apply nodeValid_prime [2, 3119] ⟨24953, 3, [(2, 3), (3119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3119
  · decide +kernel

theorem prime_24977 : Nat.Prime 24977 := by
  apply nodeValid_prime [2, 7, 223] ⟨24977, 3, [(2, 4), (7, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_223
  · decide +kernel

theorem prime_25031 : Nat.Prime 25031 := by
  apply nodeValid_prime [2, 5, 2503] ⟨25031, 13, [(2, 1), (5, 1), (2503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2503
  · decide +kernel

theorem prime_25037 : Nat.Prime 25037 := by
  apply nodeValid_prime [2, 11, 569] ⟨25037, 2, [(2, 2), (11, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_569
  · decide +kernel

theorem prime_25057 : Nat.Prime 25057 := by
  apply nodeValid_prime [2, 3, 29] ⟨25057, 5, [(2, 5), (3, 3), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_25073 : Nat.Prime 25073 := by
  apply nodeValid_prime [2, 1567] ⟨25073, 3, [(2, 4), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1567
  · decide +kernel

theorem prime_25127 : Nat.Prime 25127 := by
  apply nodeValid_prime [2, 17, 739] ⟨25127, 5, [(2, 1), (17, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_739
  · decide +kernel

theorem prime_25153 : Nat.Prime 25153 := by
  apply nodeValid_prime [2, 3, 131] ⟨25153, 10, [(2, 6), (3, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_25163 : Nat.Prime 25163 := by
  apply nodeValid_prime [2, 23, 547] ⟨25163, 2, [(2, 1), (23, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_547
  · decide +kernel

theorem prime_25219 : Nat.Prime 25219 := by
  apply nodeValid_prime [2, 3, 467] ⟨25219, 2, [(2, 1), (3, 3), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
  · decide +kernel

theorem prime_25229 : Nat.Prime 25229 := by
  apply nodeValid_prime [2, 7, 17, 53] ⟨25229, 2, [(2, 2), (7, 1), (17, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_53
  · decide +kernel

theorem prime_25243 : Nat.Prime 25243 := by
  apply nodeValid_prime [2, 3, 7, 601] ⟨25243, 2, [(2, 1), (3, 1), (7, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_601
  · decide +kernel

theorem prime_25247 : Nat.Prime 25247 := by
  apply nodeValid_prime [2, 13, 971] ⟨25247, 5, [(2, 1), (13, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_971
  · decide +kernel

theorem prime_25253 : Nat.Prime 25253 := by
  apply nodeValid_prime [2, 59, 107] ⟨25253, 2, [(2, 2), (59, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_107
  · decide +kernel

theorem prime_25303 : Nat.Prime 25303 := by
  apply nodeValid_prime [2, 3, 4217] ⟨25303, 3, [(2, 1), (3, 1), (4217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4217
  · decide +kernel

theorem prime_25309 : Nat.Prime 25309 := by
  apply nodeValid_prime [2, 3, 19, 37] ⟨25309, 13, [(2, 2), (3, 2), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_25339 : Nat.Prime 25339 := by
  apply nodeValid_prime [2, 3, 41, 103] ⟨25339, 3, [(2, 1), (3, 1), (41, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_103
  · decide +kernel

theorem prime_25343 : Nat.Prime 25343 := by
  apply nodeValid_prime [2, 12671] ⟨25343, 5, [(2, 1), (12671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12671
  · decide +kernel

theorem prime_25357 : Nat.Prime 25357 := by
  apply nodeValid_prime [2, 3, 2113] ⟨25357, 2, [(2, 2), (3, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2113
  · decide +kernel

theorem prime_25367 : Nat.Prime 25367 := by
  apply nodeValid_prime [2, 11, 1153] ⟨25367, 5, [(2, 1), (11, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1153
  · decide +kernel

theorem prime_25411 : Nat.Prime 25411 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨25411, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_25439 : Nat.Prime 25439 := by
  apply nodeValid_prime [2, 7, 23, 79] ⟨25439, 7, [(2, 1), (7, 1), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_25463 : Nat.Prime 25463 := by
  apply nodeValid_prime [2, 29, 439] ⟨25463, 5, [(2, 1), (29, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_439
  · decide +kernel

theorem prime_25469 : Nat.Prime 25469 := by
  apply nodeValid_prime [2, 6367] ⟨25469, 2, [(2, 2), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6367
  · decide +kernel

theorem prime_25523 : Nat.Prime 25523 := by
  apply nodeValid_prime [2, 7, 1823] ⟨25523, 2, [(2, 1), (7, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1823
  · decide +kernel

theorem prime_25541 : Nat.Prime 25541 := by
  apply nodeValid_prime [2, 5, 1277] ⟨25541, 2, [(2, 2), (5, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1277
  · decide +kernel

theorem prime_25577 : Nat.Prime 25577 := by
  apply nodeValid_prime [2, 23, 139] ⟨25577, 3, [(2, 3), (23, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_139
  · decide +kernel

theorem prime_25601 : Nat.Prime 25601 := by
  apply nodeValid_prime [2, 5] ⟨25601, 3, [(2, 10), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_25603 : Nat.Prime 25603 := by
  apply nodeValid_prime [2, 3, 17, 251] ⟨25603, 2, [(2, 1), (3, 1), (17, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_251
  · decide +kernel

theorem prime_25609 : Nat.Prime 25609 := by
  apply nodeValid_prime [2, 3, 11, 97] ⟨25609, 7, [(2, 3), (3, 1), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_25633 : Nat.Prime 25633 := by
  apply nodeValid_prime [2, 3, 89] ⟨25633, 5, [(2, 5), (3, 2), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_25643 : Nat.Prime 25643 := by
  apply nodeValid_prime [2, 12821] ⟨25643, 2, [(2, 1), (12821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12821
  · decide +kernel

theorem prime_25703 : Nat.Prime 25703 := by
  apply nodeValid_prime [2, 71, 181] ⟨25703, 5, [(2, 1), (71, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_181
  · decide +kernel

theorem prime_25741 : Nat.Prime 25741 := by
  apply nodeValid_prime [2, 3, 5, 11, 13] ⟨25741, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_25747 : Nat.Prime 25747 := by
  apply nodeValid_prime [2, 3, 7, 613] ⟨25747, 2, [(2, 1), (3, 1), (7, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_613
  · decide +kernel

theorem prime_25771 : Nat.Prime 25771 := by
  apply nodeValid_prime [2, 3, 5, 859] ⟨25771, 2, [(2, 1), (3, 1), (5, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_859
  · decide +kernel

theorem prime_25793 : Nat.Prime 25793 := by
  apply nodeValid_prime [2, 13, 31] ⟨25793, 3, [(2, 6), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_25801 : Nat.Prime 25801 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨25801, 7, [(2, 3), (3, 1), (5, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_25847 : Nat.Prime 25847 := by
  apply nodeValid_prime [2, 12923] ⟨25847, 5, [(2, 1), (12923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12923
  · decide +kernel

theorem prime_25873 : Nat.Prime 25873 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨25873, 10, [(2, 4), (3, 1), (7, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_25903 : Nat.Prime 25903 := by
  apply nodeValid_prime [2, 3, 1439] ⟨25903, 5, [(2, 1), (3, 2), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1439
  · decide +kernel

theorem prime_25913 : Nat.Prime 25913 := by
  apply nodeValid_prime [2, 41, 79] ⟨25913, 3, [(2, 3), (41, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_79
  · decide +kernel

theorem prime_25931 : Nat.Prime 25931 := by
  apply nodeValid_prime [2, 5, 2593] ⟨25931, 2, [(2, 1), (5, 1), (2593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2593
  · decide +kernel

theorem prime_25933 : Nat.Prime 25933 := by
  apply nodeValid_prime [2, 3, 2161] ⟨25933, 2, [(2, 2), (3, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2161
  · decide +kernel

theorem prime_25951 : Nat.Prime 25951 := by
  apply nodeValid_prime [2, 3, 5, 173] ⟨25951, 3, [(2, 1), (3, 1), (5, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_25997 : Nat.Prime 25997 := by
  apply nodeValid_prime [2, 67, 97] ⟨25997, 2, [(2, 2), (67, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_97
  · decide +kernel

theorem prime_26017 : Nat.Prime 26017 := by
  apply nodeValid_prime [2, 3, 271] ⟨26017, 5, [(2, 5), (3, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
  · decide +kernel

theorem prime_26029 : Nat.Prime 26029 := by
  apply nodeValid_prime [2, 3, 241] ⟨26029, 6, [(2, 2), (3, 3), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel

theorem prime_26041 : Nat.Prime 26041 := by
  apply nodeValid_prime [2, 3, 5, 7, 31] ⟨26041, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_26053 : Nat.Prime 26053 := by
  apply nodeValid_prime [2, 3, 13, 167] ⟨26053, 2, [(2, 2), (3, 1), (13, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_167
  · decide +kernel

theorem prime_26141 : Nat.Prime 26141 := by
  apply nodeValid_prime [2, 5, 1307] ⟨26141, 2, [(2, 2), (5, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1307
  · decide +kernel

theorem prime_26153 : Nat.Prime 26153 := by
  apply nodeValid_prime [2, 7, 467] ⟨26153, 3, [(2, 3), (7, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_467
  · decide +kernel

theorem prime_26203 : Nat.Prime 26203 := by
  apply nodeValid_prime [2, 3, 11, 397] ⟨26203, 3, [(2, 1), (3, 1), (11, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_397
  · decide +kernel

theorem prime_26209 : Nat.Prime 26209 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨26209, 11, [(2, 5), (3, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_26237 : Nat.Prime 26237 := by
  apply nodeValid_prime [2, 7, 937] ⟨26237, 2, [(2, 2), (7, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_937
  · decide +kernel

theorem prime_26261 : Nat.Prime 26261 := by
  apply nodeValid_prime [2, 5, 13, 101] ⟨26261, 2, [(2, 2), (5, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_26263 : Nat.Prime 26263 := by
  apply nodeValid_prime [2, 3, 1459] ⟨26263, 3, [(2, 1), (3, 2), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1459
  · decide +kernel

theorem prime_26267 : Nat.Prime 26267 := by
  apply nodeValid_prime [2, 23, 571] ⟨26267, 2, [(2, 1), (23, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_571
  · decide +kernel

theorem prime_26309 : Nat.Prime 26309 := by
  apply nodeValid_prime [2, 6577] ⟨26309, 2, [(2, 2), (6577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6577
  · decide +kernel

theorem prime_26317 : Nat.Prime 26317 := by
  apply nodeValid_prime [2, 3, 17, 43] ⟨26317, 6, [(2, 2), (3, 2), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_26339 : Nat.Prime 26339 := by
  apply nodeValid_prime [2, 13, 1013] ⟨26339, 2, [(2, 1), (13, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1013
  · decide +kernel

theorem prime_26357 : Nat.Prime 26357 := by
  apply nodeValid_prime [2, 11, 599] ⟨26357, 2, [(2, 2), (11, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_599
  · decide +kernel

theorem prime_26479 : Nat.Prime 26479 := by
  apply nodeValid_prime [2, 3, 1471] ⟨26479, 3, [(2, 1), (3, 2), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1471
  · decide +kernel

theorem prime_26489 : Nat.Prime 26489 := by
  apply nodeValid_prime [2, 7, 11, 43] ⟨26489, 3, [(2, 3), (7, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_26501 : Nat.Prime 26501 := by
  apply nodeValid_prime [2, 5, 53] ⟨26501, 2, [(2, 2), (5, 3), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_26513 : Nat.Prime 26513 := by
  apply nodeValid_prime [2, 1657] ⟨26513, 3, [(2, 4), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1657
  · decide +kernel

theorem prime_26539 : Nat.Prime 26539 := by
  apply nodeValid_prime [2, 3, 4423] ⟨26539, 2, [(2, 1), (3, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4423
  · decide +kernel

theorem prime_26557 : Nat.Prime 26557 := by
  apply nodeValid_prime [2, 3, 2213] ⟨26557, 2, [(2, 2), (3, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2213
  · decide +kernel

theorem prime_26561 : Nat.Prime 26561 := by
  apply nodeValid_prime [2, 5, 83] ⟨26561, 3, [(2, 6), (5, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
  · decide +kernel

theorem prime_26573 : Nat.Prime 26573 := by
  apply nodeValid_prime [2, 7, 13, 73] ⟨26573, 2, [(2, 2), (7, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_26641 : Nat.Prime 26641 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨26641, 7, [(2, 4), (3, 2), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_26647 : Nat.Prime 26647 := by
  apply nodeValid_prime [2, 3, 4441] ⟨26647, 3, [(2, 1), (3, 1), (4441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4441
  · decide +kernel

theorem prime_26683 : Nat.Prime 26683 := by
  apply nodeValid_prime [2, 3, 4447] ⟨26683, 2, [(2, 1), (3, 1), (4447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4447
  · decide +kernel

theorem prime_26687 : Nat.Prime 26687 := by
  apply nodeValid_prime [2, 11, 1213] ⟨26687, 5, [(2, 1), (11, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1213
  · decide +kernel

theorem prime_26701 : Nat.Prime 26701 := by
  apply nodeValid_prime [2, 3, 5, 89] ⟨26701, 22, [(2, 2), (3, 1), (5, 2), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_26777 : Nat.Prime 26777 := by
  apply nodeValid_prime [2, 3347] ⟨26777, 3, [(2, 3), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3347
  · decide +kernel

theorem prime_26783 : Nat.Prime 26783 := by
  apply nodeValid_prime [2, 7, 1913] ⟨26783, 5, [(2, 1), (7, 1), (1913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1913
  · decide +kernel

theorem prime_26801 : Nat.Prime 26801 := by
  apply nodeValid_prime [2, 5, 67] ⟨26801, 3, [(2, 4), (5, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_26813 : Nat.Prime 26813 := by
  apply nodeValid_prime [2, 6703] ⟨26813, 2, [(2, 2), (6703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6703
  · decide +kernel

theorem prime_26821 : Nat.Prime 26821 := by
  apply nodeValid_prime [2, 3, 5, 149] ⟨26821, 2, [(2, 2), (3, 2), (5, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
  · decide +kernel

theorem prime_26861 : Nat.Prime 26861 := by
  apply nodeValid_prime [2, 5, 17, 79] ⟨26861, 2, [(2, 2), (5, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_26863 : Nat.Prime 26863 := by
  apply nodeValid_prime [2, 3, 11, 37] ⟨26863, 5, [(2, 1), (3, 1), (11, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_26891 : Nat.Prime 26891 := by
  apply nodeValid_prime [2, 5, 2689] ⟨26891, 6, [(2, 1), (5, 1), (2689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2689
  · decide +kernel

theorem prime_26903 : Nat.Prime 26903 := by
  apply nodeValid_prime [2, 13451] ⟨26903, 5, [(2, 1), (13451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13451
  · decide +kernel

theorem prime_26921 : Nat.Prime 26921 := by
  apply nodeValid_prime [2, 5, 673] ⟨26921, 13, [(2, 3), (5, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_673
  · decide +kernel

theorem prime_26947 : Nat.Prime 26947 := by
  apply nodeValid_prime [2, 3, 499] ⟨26947, 2, [(2, 1), (3, 3), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_499
  · decide +kernel

theorem prime_27011 : Nat.Prime 27011 := by
  apply nodeValid_prime [2, 5, 37, 73] ⟨27011, 2, [(2, 1), (5, 1), (37, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_73
  · decide +kernel

theorem prime_27031 : Nat.Prime 27031 := by
  apply nodeValid_prime [2, 3, 5, 17, 53] ⟨27031, 6, [(2, 1), (3, 1), (5, 1), (17, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_53
  · decide +kernel

theorem prime_27043 : Nat.Prime 27043 := by
  apply nodeValid_prime [2, 3, 4507] ⟨27043, 2, [(2, 1), (3, 1), (4507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4507
  · decide +kernel

theorem prime_27059 : Nat.Prime 27059 := by
  apply nodeValid_prime [2, 83, 163] ⟨27059, 2, [(2, 1), (83, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_163
  · decide +kernel

theorem prime_27061 : Nat.Prime 27061 := by
  apply nodeValid_prime [2, 3, 5, 11, 41] ⟨27061, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_27067 : Nat.Prime 27067 := by
  apply nodeValid_prime [2, 3, 13, 347] ⟨27067, 2, [(2, 1), (3, 1), (13, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_347
  · decide +kernel

theorem prime_27077 : Nat.Prime 27077 := by
  apply nodeValid_prime [2, 7, 967] ⟨27077, 2, [(2, 2), (7, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_967
  · decide +kernel

theorem prime_27103 : Nat.Prime 27103 := by
  apply nodeValid_prime [2, 3, 4517] ⟨27103, 3, [(2, 1), (3, 1), (4517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4517
  · decide +kernel

theorem prime_27107 : Nat.Prime 27107 := by
  apply nodeValid_prime [2, 13553] ⟨27107, 2, [(2, 1), (13553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13553
  · decide +kernel

theorem prime_27109 : Nat.Prime 27109 := by
  apply nodeValid_prime [2, 3, 251] ⟨27109, 7, [(2, 2), (3, 3), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
  · decide +kernel

theorem prime_27179 : Nat.Prime 27179 := by
  apply nodeValid_prime [2, 107, 127] ⟨27179, 2, [(2, 1), (107, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_127
  · decide +kernel

theorem prime_27191 : Nat.Prime 27191 := by
  apply nodeValid_prime [2, 5, 2719] ⟨27191, 26, [(2, 1), (5, 1), (2719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2719
  · decide +kernel

theorem prime_27239 : Nat.Prime 27239 := by
  apply nodeValid_prime [2, 13619] ⟨27239, 7, [(2, 1), (13619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13619
  · decide +kernel

theorem prime_27241 : Nat.Prime 27241 := by
  apply nodeValid_prime [2, 3, 5, 227] ⟨27241, 17, [(2, 3), (3, 1), (5, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_227
  · decide +kernel

theorem prime_27253 : Nat.Prime 27253 := by
  apply nodeValid_prime [2, 3, 757] ⟨27253, 2, [(2, 2), (3, 2), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_757
  · decide +kernel

theorem prime_27283 : Nat.Prime 27283 := by
  apply nodeValid_prime [2, 3, 4547] ⟨27283, 5, [(2, 1), (3, 1), (4547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4547
  · decide +kernel

theorem prime_27397 : Nat.Prime 27397 := by
  apply nodeValid_prime [2, 3, 761] ⟨27397, 2, [(2, 2), (3, 2), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_761
  · decide +kernel

theorem prime_27409 : Nat.Prime 27409 := by
  apply nodeValid_prime [2, 3, 571] ⟨27409, 13, [(2, 4), (3, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
  · decide +kernel

theorem prime_27437 : Nat.Prime 27437 := by
  apply nodeValid_prime [2, 19] ⟨27437, 2, [(2, 2), (19, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19
  · decide +kernel

theorem prime_27509 : Nat.Prime 27509 := by
  apply nodeValid_prime [2, 13, 23] ⟨27509, 2, [(2, 2), (13, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_27529 : Nat.Prime 27529 := by
  apply nodeValid_prime [2, 3, 31, 37] ⟨27529, 7, [(2, 3), (3, 1), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_27541 : Nat.Prime 27541 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨27541, 19, [(2, 2), (3, 4), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_27581 : Nat.Prime 27581 := by
  apply nodeValid_prime [2, 5, 7, 197] ⟨27581, 2, [(2, 2), (5, 1), (7, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_197
  · decide +kernel

theorem prime_27583 : Nat.Prime 27583 := by
  apply nodeValid_prime [2, 3, 4597] ⟨27583, 3, [(2, 1), (3, 1), (4597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4597
  · decide +kernel

theorem prime_27617 : Nat.Prime 27617 := by
  apply nodeValid_prime [2, 863] ⟨27617, 3, [(2, 5), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_863
  · decide +kernel

theorem prime_27631 : Nat.Prime 27631 := by
  apply nodeValid_prime [2, 3, 5, 307] ⟨27631, 6, [(2, 1), (3, 2), (5, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_307
  · decide +kernel

theorem prime_27673 : Nat.Prime 27673 := by
  apply nodeValid_prime [2, 3, 1153] ⟨27673, 11, [(2, 3), (3, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1153
  · decide +kernel

theorem prime_27691 : Nat.Prime 27691 := by
  apply nodeValid_prime [2, 3, 5, 13, 71] ⟨27691, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_27737 : Nat.Prime 27737 := by
  apply nodeValid_prime [2, 3467] ⟨27737, 3, [(2, 3), (3467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3467
  · decide +kernel

theorem prime_27767 : Nat.Prime 27767 := by
  apply nodeValid_prime [2, 13883] ⟨27767, 5, [(2, 1), (13883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13883
  · decide +kernel

theorem prime_27791 : Nat.Prime 27791 := by
  apply nodeValid_prime [2, 5, 7, 397] ⟨27791, 7, [(2, 1), (5, 1), (7, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_397
  · decide +kernel

theorem prime_27793 : Nat.Prime 27793 := by
  apply nodeValid_prime [2, 3, 193] ⟨27793, 5, [(2, 4), (3, 2), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
  · decide +kernel

theorem prime_27803 : Nat.Prime 27803 := by
  apply nodeValid_prime [2, 13901] ⟨27803, 2, [(2, 1), (13901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13901
  · decide +kernel

theorem prime_27809 : Nat.Prime 27809 := by
  apply nodeValid_prime [2, 11, 79] ⟨27809, 3, [(2, 5), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_27823 : Nat.Prime 27823 := by
  apply nodeValid_prime [2, 3, 4637] ⟨27823, 6, [(2, 1), (3, 1), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4637
  · decide +kernel

theorem prime_27883 : Nat.Prime 27883 := by
  apply nodeValid_prime [2, 3, 1549] ⟨27883, 3, [(2, 1), (3, 2), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1549
  · decide +kernel

theorem prime_27901 : Nat.Prime 27901 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨27901, 2, [(2, 2), (3, 2), (5, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_27917 : Nat.Prime 27917 := by
  apply nodeValid_prime [2, 7, 997] ⟨27917, 2, [(2, 2), (7, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_997
  · decide +kernel

theorem prime_27947 : Nat.Prime 27947 := by
  apply nodeValid_prime [2, 89, 157] ⟨27947, 2, [(2, 1), (89, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_157
  · decide +kernel

theorem prime_27953 : Nat.Prime 27953 := by
  apply nodeValid_prime [2, 1747] ⟨27953, 3, [(2, 4), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1747
  · decide +kernel

theorem prime_27983 : Nat.Prime 27983 := by
  apply nodeValid_prime [2, 17, 823] ⟨27983, 5, [(2, 1), (17, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_823
  · decide +kernel

end Sude.Lucas.Generated
