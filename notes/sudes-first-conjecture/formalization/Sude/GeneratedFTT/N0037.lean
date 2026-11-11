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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2879 : Nat.Prime 2879 := by
  apply nodeValid_prime [2, 1439] ⟨2879, 7, [(2, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1439
  · decide +kernel

theorem prime_3571 : Nat.Prime 3571 := by
  apply nodeValid_prime [2, 3, 5, 7, 17] ⟨3571, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_3739 : Nat.Prime 3739 := by
  apply nodeValid_prime [2, 3, 7, 89] ⟨3739, 7, [(2, 1), (3, 1), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_4723 : Nat.Prime 4723 := by
  apply nodeValid_prime [2, 3, 787] ⟨4723, 2, [(2, 1), (3, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_787
  · decide +kernel

theorem prime_7127 : Nat.Prime 7127 := by
  apply nodeValid_prime [2, 7, 509] ⟨7127, 5, [(2, 1), (7, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_509
  · decide +kernel

theorem prime_7643 : Nat.Prime 7643 := by
  apply nodeValid_prime [2, 3821] ⟨7643, 2, [(2, 1), (3821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3821
  · decide +kernel

theorem prime_8147 : Nat.Prime 8147 := by
  apply nodeValid_prime [2, 4073] ⟨8147, 2, [(2, 1), (4073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4073
  · decide +kernel

theorem prime_8161 : Nat.Prime 8161 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨8161, 7, [(2, 5), (3, 1), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_8641 : Nat.Prime 8641 := by
  apply nodeValid_prime [2, 3, 5] ⟨8641, 17, [(2, 6), (3, 3), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_9029 : Nat.Prime 9029 := by
  apply nodeValid_prime [2, 37, 61] ⟨9029, 2, [(2, 2), (37, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_61
  · decide +kernel

theorem prime_10007 : Nat.Prime 10007 := by
  apply nodeValid_prime [2, 5003] ⟨10007, 5, [(2, 1), (5003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5003
  · decide +kernel

theorem prime_10301 : Nat.Prime 10301 := by
  apply nodeValid_prime [2, 5, 103] ⟨10301, 2, [(2, 2), (5, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_10321 : Nat.Prime 10321 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨10321, 7, [(2, 4), (3, 1), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_11467 : Nat.Prime 11467 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨11467, 5, [(2, 1), (3, 2), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_12583 : Nat.Prime 12583 := by
  apply nodeValid_prime [2, 3, 233] ⟨12583, 5, [(2, 1), (3, 3), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
  · decide +kernel

theorem prime_12907 : Nat.Prime 12907 := by
  apply nodeValid_prime [2, 3, 239] ⟨12907, 2, [(2, 1), (3, 3), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
  · decide +kernel

theorem prime_13873 : Nat.Prime 13873 := by
  apply nodeValid_prime [2, 3, 17] ⟨13873, 5, [(2, 4), (3, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_14369 : Nat.Prime 14369 := by
  apply nodeValid_prime [2, 449] ⟨14369, 3, [(2, 5), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_449
  · decide +kernel

theorem prime_15619 : Nat.Prime 15619 := by
  apply nodeValid_prime [2, 3, 19, 137] ⟨15619, 7, [(2, 1), (3, 1), (19, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_17467 : Nat.Prime 17467 := by
  apply nodeValid_prime [2, 3, 41, 71] ⟨17467, 3, [(2, 1), (3, 1), (41, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_71
  · decide +kernel

theorem prime_17747 : Nat.Prime 17747 := by
  apply nodeValid_prime [2, 19, 467] ⟨17747, 2, [(2, 1), (19, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_467
  · decide +kernel

theorem prime_18059 : Nat.Prime 18059 := by
  apply nodeValid_prime [2, 9029] ⟨18059, 2, [(2, 1), (9029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9029
  · decide +kernel

theorem prime_18121 : Nat.Prime 18121 := by
  apply nodeValid_prime [2, 3, 5, 151] ⟨18121, 23, [(2, 3), (3, 1), (5, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
  · decide +kernel

theorem prime_18451 : Nat.Prime 18451 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨18451, 3, [(2, 1), (3, 2), (5, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_18503 : Nat.Prime 18503 := by
  apply nodeValid_prime [2, 11, 29] ⟨18503, 5, [(2, 1), (11, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_21001 : Nat.Prime 21001 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨21001, 11, [(2, 3), (3, 1), (5, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_25889 : Nat.Prime 25889 := by
  apply nodeValid_prime [2, 809] ⟨25889, 3, [(2, 5), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_809
  · decide +kernel

theorem prime_27773 : Nat.Prime 27773 := by
  apply nodeValid_prime [2, 53, 131] ⟨27773, 2, [(2, 2), (53, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_131
  · decide +kernel

theorem prime_28513 : Nat.Prime 28513 := by
  apply nodeValid_prime [2, 3, 11] ⟨28513, 5, [(2, 5), (3, 4), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_28687 : Nat.Prime 28687 := by
  apply nodeValid_prime [2, 3, 7, 683] ⟨28687, 6, [(2, 1), (3, 1), (7, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_683
  · decide +kernel

theorem prime_32999 : Nat.Prime 32999 := by
  apply nodeValid_prime [2, 7, 2357] ⟨32999, 7, [(2, 1), (7, 1), (2357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2357
  · decide +kernel

theorem prime_40189 : Nat.Prime 40189 := by
  apply nodeValid_prime [2, 3, 17, 197] ⟨40189, 2, [(2, 2), (3, 1), (17, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_197
  · decide +kernel

theorem prime_41513 : Nat.Prime 41513 := by
  apply nodeValid_prime [2, 5189] ⟨41513, 3, [(2, 3), (5189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5189
  · decide +kernel

theorem prime_44221 : Nat.Prime 44221 := by
  apply nodeValid_prime [2, 3, 5, 11, 67] ⟨44221, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_55117 : Nat.Prime 55117 := by
  apply nodeValid_prime [2, 3, 1531] ⟨55117, 5, [(2, 2), (3, 2), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1531
  · decide +kernel

theorem prime_55661 : Nat.Prime 55661 := by
  apply nodeValid_prime [2, 5, 11, 23] ⟨55661, 2, [(2, 2), (5, 1), (11, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_61843 : Nat.Prime 61843 := by
  apply nodeValid_prime [2, 3, 11, 937] ⟨61843, 2, [(2, 1), (3, 1), (11, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_937
  · decide +kernel

theorem prime_65929 : Nat.Prime 65929 := by
  apply nodeValid_prime [2, 3, 41, 67] ⟨65929, 7, [(2, 3), (3, 1), (41, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_67
  · decide +kernel

theorem prime_67939 : Nat.Prime 67939 := by
  apply nodeValid_prime [2, 3, 13, 67] ⟨67939, 3, [(2, 1), (3, 1), (13, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_76603 : Nat.Prime 76603 := by
  apply nodeValid_prime [2, 3, 17, 751] ⟨76603, 2, [(2, 1), (3, 1), (17, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_751
  · decide +kernel

theorem prime_77171 : Nat.Prime 77171 := by
  apply nodeValid_prime [2, 5, 7717] ⟨77171, 2, [(2, 1), (5, 1), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7717
  · decide +kernel

theorem prime_81901 : Nat.Prime 81901 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨81901, 2, [(2, 2), (3, 2), (5, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_90947 : Nat.Prime 90947 := by
  apply nodeValid_prime [2, 37, 1229] ⟨90947, 2, [(2, 1), (37, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1229
  · decide +kernel

theorem prime_93983 : Nat.Prime 93983 := by
  apply nodeValid_prime [2, 7, 137] ⟨93983, 5, [(2, 1), (7, 3), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_109357 : Nat.Prime 109357 := by
  apply nodeValid_prime [2, 3, 13, 701] ⟨109357, 11, [(2, 2), (3, 1), (13, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_701
  · decide +kernel

theorem prime_110221 : Nat.Prime 110221 := by
  apply nodeValid_prime [2, 3, 5, 11, 167] ⟨110221, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_167
  · decide +kernel

theorem prime_111217 : Nat.Prime 111217 := by
  apply nodeValid_prime [2, 3, 7, 331] ⟨111217, 15, [(2, 4), (3, 1), (7, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_331
  · decide +kernel

theorem prime_111323 : Nat.Prime 111323 := by
  apply nodeValid_prime [2, 55661] ⟨111323, 2, [(2, 1), (55661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_55661
  · decide +kernel

theorem prime_114671 : Nat.Prime 114671 := by
  apply nodeValid_prime [2, 5, 11467] ⟨114671, 13, [(2, 1), (5, 1), (11467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11467
  · decide +kernel

theorem prime_123593 : Nat.Prime 123593 := by
  apply nodeValid_prime [2, 7, 2207] ⟨123593, 5, [(2, 3), (7, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2207
  · decide +kernel

theorem prime_129341 : Nat.Prime 129341 := by
  apply nodeValid_prime [2, 5, 29, 223] ⟨129341, 2, [(2, 2), (5, 1), (29, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_223
  · decide +kernel

theorem prime_136177 : Nat.Prime 136177 := by
  apply nodeValid_prime [2, 3, 2837] ⟨136177, 5, [(2, 4), (3, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2837
  · decide +kernel

theorem prime_159073 : Nat.Prime 159073 := by
  apply nodeValid_prime [2, 3, 1657] ⟨159073, 7, [(2, 5), (3, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1657
  · decide +kernel

theorem prime_177601 : Nat.Prime 177601 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨177601, 11, [(2, 6), (3, 1), (5, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_197221 : Nat.Prime 197221 := by
  apply nodeValid_prime [2, 3, 5, 19, 173] ⟨197221, 7, [(2, 2), (3, 1), (5, 1), (19, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_173
  · decide +kernel

theorem prime_256939 : Nat.Prime 256939 := by
  apply nodeValid_prime [2, 3, 11, 17, 229] ⟨256939, 2, [(2, 1), (3, 1), (11, 1), (17, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_229
  · decide +kernel

theorem prime_267661 : Nat.Prime 267661 := by
  apply nodeValid_prime [2, 3, 5, 1487] ⟨267661, 2, [(2, 2), (3, 2), (5, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1487
  · decide +kernel

theorem prime_300733 : Nat.Prime 300733 := by
  apply nodeValid_prime [2, 3, 19, 1319] ⟨300733, 5, [(2, 2), (3, 1), (19, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1319
  · decide +kernel

theorem prime_325063 : Nat.Prime 325063 := by
  apply nodeValid_prime [2, 3, 18059] ⟨325063, 3, [(2, 1), (3, 2), (18059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18059
  · decide +kernel

theorem prime_363557 : Nat.Prime 363557 := by
  apply nodeValid_prime [2, 97, 937] ⟨363557, 2, [(2, 2), (97, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_937
  · decide +kernel

theorem prime_378019 : Nat.Prime 378019 := by
  apply nodeValid_prime [2, 3, 21001] ⟨378019, 3, [(2, 1), (3, 2), (21001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21001
  · decide +kernel

theorem prime_391057 : Nat.Prime 391057 := by
  apply nodeValid_prime [2, 3, 8147] ⟨391057, 11, [(2, 4), (3, 1), (8147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8147
  · decide +kernel

theorem prime_415489 : Nat.Prime 415489 := by
  apply nodeValid_prime [2, 3, 541] ⟨415489, 11, [(2, 8), (3, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
  · decide +kernel

theorem prime_459619 : Nat.Prime 459619 := by
  apply nodeValid_prime [2, 3, 76603] ⟨459619, 2, [(2, 1), (3, 1), (76603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76603
  · decide +kernel

theorem prime_474391 : Nat.Prime 474391 := by
  apply nodeValid_prime [2, 3, 5, 7, 251] ⟨474391, 7, [(2, 1), (3, 3), (5, 1), (7, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_251
  · decide +kernel

theorem prime_495511 : Nat.Prime 495511 := by
  apply nodeValid_prime [2, 3, 5, 83, 199] ⟨495511, 3, [(2, 1), (3, 1), (5, 1), (83, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_199
  · decide +kernel

theorem prime_897433 : Nat.Prime 897433 := by
  apply nodeValid_prime [2, 3, 61, 613] ⟨897433, 5, [(2, 3), (3, 1), (61, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_613
  · decide +kernel

theorem prime_970573 : Nat.Prime 970573 := by
  apply nodeValid_prime [2, 3, 29, 2789] ⟨970573, 5, [(2, 2), (3, 1), (29, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2789
  · decide +kernel

theorem prime_1114019 : Nat.Prime 1114019 := by
  apply nodeValid_prime [2, 653, 853] ⟨1114019, 2, [(2, 1), (653, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_653
    · exact prime_853
  · decide +kernel

theorem prime_1209181 : Nat.Prime 1209181 := by
  apply nodeValid_prime [2, 3, 5, 7, 2879] ⟨1209181, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (2879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2879
  · decide +kernel

theorem prime_1252631 : Nat.Prime 1252631 := by
  apply nodeValid_prime [2, 5, 229, 547] ⟨1252631, 7, [(2, 1), (5, 1), (229, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_547
  · decide +kernel

theorem prime_1300253 : Nat.Prime 1300253 := by
  apply nodeValid_prime [2, 325063] ⟨1300253, 2, [(2, 2), (325063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_325063
  · decide +kernel

theorem prime_1310417 : Nat.Prime 1310417 := by
  apply nodeValid_prime [2, 81901] ⟨1310417, 3, [(2, 4), (81901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_81901
  · decide +kernel

theorem prime_1328473 : Nat.Prime 1328473 := by
  apply nodeValid_prime [2, 3, 18451] ⟨1328473, 5, [(2, 3), (3, 2), (18451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18451
  · decide +kernel

theorem prime_1710781 : Nat.Prime 1710781 := by
  apply nodeValid_prime [2, 3, 5, 28513] ⟨1710781, 2, [(2, 2), (3, 1), (5, 1), (28513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28513
  · decide +kernel

theorem prime_2873891 : Nat.Prime 2873891 := by
  apply nodeValid_prime [2, 5, 59, 4871] ⟨2873891, 2, [(2, 1), (5, 1), (59, 1), (4871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_4871
  · decide +kernel

theorem prime_3608797 : Nat.Prime 3608797 := by
  apply nodeValid_prime [2, 3, 300733] ⟨3608797, 5, [(2, 2), (3, 1), (300733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_300733
  · decide +kernel

theorem prime_3669473 : Nat.Prime 3669473 := by
  apply nodeValid_prime [2, 114671] ⟨3669473, 3, [(2, 5), (114671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_114671
  · decide +kernel

theorem prime_4623809 : Nat.Prime 4623809 := by
  apply nodeValid_prime [2, 7, 10321] ⟨4623809, 3, [(2, 6), (7, 1), (10321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10321
  · decide +kernel

theorem prime_4798337 : Nat.Prime 4798337 := by
  apply nodeValid_prime [2, 19, 1973] ⟨4798337, 3, [(2, 7), (19, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1973
  · decide +kernel

theorem prime_5299243 : Nat.Prime 5299243 := by
  apply nodeValid_prime [2, 3, 13, 67939] ⟨5299243, 5, [(2, 1), (3, 1), (13, 1), (67939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67939
  · decide +kernel

theorem prime_6301159 : Nat.Prime 6301159 := by
  apply nodeValid_prime [2, 3, 179, 5867] ⟨6301159, 3, [(2, 1), (3, 1), (179, 1), (5867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_5867
  · decide +kernel

theorem prime_6364819 : Nat.Prime 6364819 := by
  apply nodeValid_prime [2, 3, 101, 389] ⟨6364819, 13, [(2, 1), (3, 4), (101, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_389
  · decide +kernel

theorem prime_6612169 : Nat.Prime 6612169 := by
  apply nodeValid_prime [2, 3, 137, 2011] ⟨6612169, 13, [(2, 3), (3, 1), (137, 1), (2011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_2011
  · decide +kernel

theorem prime_9204337 : Nat.Prime 9204337 := by
  apply nodeValid_prime [2, 3, 41, 1559] ⟨9204337, 10, [(2, 4), (3, 2), (41, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1559
  · decide +kernel

theorem prime_9247619 : Nat.Prime 9247619 := by
  apply nodeValid_prime [2, 4623809] ⟨9247619, 2, [(2, 1), (4623809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4623809
  · decide +kernel

theorem prime_11030857 : Nat.Prime 11030857 := by
  apply nodeValid_prime [2, 3, 459619] ⟨11030857, 7, [(2, 3), (3, 1), (459619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_459619
  · decide +kernel

theorem prime_17812933 : Nat.Prime 17812933 := by
  apply nodeValid_prime [2, 3, 107, 13873] ⟨17812933, 2, [(2, 2), (3, 1), (107, 1), (13873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_13873
  · decide +kernel

theorem prime_18063527 : Nat.Prime 18063527 := by
  apply nodeValid_prime [2, 13, 43, 107, 151] ⟨18063527, 5, [(2, 1), (13, 1), (43, 1), (107, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_107
    · exact prime_151
  · decide +kernel

theorem prime_19652411 : Nat.Prime 19652411 := by
  apply nodeValid_prime [2, 5, 179, 10979] ⟨19652411, 2, [(2, 1), (5, 1), (179, 1), (10979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_10979
  · decide +kernel

theorem prime_25698973 : Nat.Prime 25698973 := by
  apply nodeValid_prime [2, 3, 13, 257, 641] ⟨25698973, 6, [(2, 2), (3, 1), (13, 1), (257, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_257
    · exact prime_641
  · decide +kernel

theorem prime_42430517 : Nat.Prime 42430517 := by
  apply nodeValid_prime [2, 97, 109357] ⟨42430517, 2, [(2, 2), (97, 1), (109357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_109357
  · decide +kernel

theorem prime_44617357 : Nat.Prime 44617357 := by
  apply nodeValid_prime [2, 3, 7, 101, 1753] ⟨44617357, 2, [(2, 2), (3, 2), (7, 1), (101, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
    · exact prime_1753
  · decide +kernel

theorem prime_46534769 : Nat.Prime 46534769 := by
  apply nodeValid_prime [2, 7, 415489] ⟨46534769, 3, [(2, 4), (7, 1), (415489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_415489
  · decide +kernel

theorem prime_84434099 : Nat.Prime 84434099 := by
  apply nodeValid_prime [2, 7, 1613, 3739] ⟨84434099, 6, [(2, 1), (7, 1), (1613, 1), (3739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1613
    · exact prime_3739
  · decide +kernel

theorem prime_92744161 : Nat.Prime 92744161 := by
  apply nodeValid_prime [2, 3, 5, 47, 4111] ⟨92744161, 7, [(2, 5), (3, 1), (5, 1), (47, 1), (4111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_4111
  · decide +kernel

theorem prime_95650057 : Nat.Prime 95650057 := by
  apply nodeValid_prime [2, 3, 1328473] ⟨95650057, 5, [(2, 3), (3, 2), (1328473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1328473
  · decide +kernel

theorem prime_158692057 : Nat.Prime 158692057 := by
  apply nodeValid_prime [2, 3, 6612169] ⟨158692057, 5, [(2, 3), (3, 1), (6612169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6612169
  · decide +kernel

theorem prime_178181243 : Nat.Prime 178181243 := by
  apply nodeValid_prime [2, 31, 2873891] ⟨178181243, 2, [(2, 1), (31, 1), (2873891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2873891
  · decide +kernel

theorem prime_231540193 : Nat.Prime 231540193 := by
  apply nodeValid_prime [2, 3, 13, 61843] ⟨231540193, 7, [(2, 5), (3, 2), (13, 1), (61843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61843
  · decide +kernel

theorem prime_285006929 : Nat.Prime 285006929 := by
  apply nodeValid_prime [2, 17812933] ⟨285006929, 3, [(2, 4), (17812933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17812933
  · decide +kernel

theorem prime_415314499 : Nat.Prime 415314499 := by
  apply nodeValid_prime [2, 3, 5501, 12583] ⟨415314499, 2, [(2, 1), (3, 1), (5501, 1), (12583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5501
    · exact prime_12583
  · decide +kernel

theorem prime_489381241 : Nat.Prime 489381241 := by
  apply nodeValid_prime [2, 3, 5, 37, 110221] ⟨489381241, 7, [(2, 3), (3, 1), (5, 1), (37, 1), (110221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_110221
  · decide +kernel

theorem prime_595318553 : Nat.Prime 595318553 := by
  apply nodeValid_prime [2, 419, 177601] ⟨595318553, 3, [(2, 3), (419, 1), (177601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_177601
  · decide +kernel

theorem prime_595631951 : Nat.Prime 595631951 := by
  apply nodeValid_prime [2, 5, 19, 32999] ⟨595631951, 13, [(2, 1), (5, 2), (19, 2), (32999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_32999
  · decide +kernel

theorem prime_650824241 : Nat.Prime 650824241 := by
  apply nodeValid_prime [2, 5, 11, 383, 1931] ⟨650824241, 6, [(2, 4), (5, 1), (11, 1), (383, 1), (1931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_383
    · exact prime_1931
  · decide +kernel

theorem prime_765035767 : Nat.Prime 765035767 := by
  apply nodeValid_prime [2, 3, 11, 73, 5881] ⟨765035767, 11, [(2, 1), (3, 4), (11, 1), (73, 1), (5881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_5881
  · decide +kernel

theorem prime_1389241159 : Nat.Prime 1389241159 := by
  apply nodeValid_prime [2, 3, 231540193] ⟨1389241159, 3, [(2, 1), (3, 1), (231540193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_231540193
  · decide +kernel

theorem prime_1733723687 : Nat.Prime 1733723687 := by
  apply nodeValid_prime [2, 47, 239, 77171] ⟨1733723687, 5, [(2, 1), (47, 1), (239, 1), (77171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_239
    · exact prime_77171
  · decide +kernel

theorem prime_3200191069 : Nat.Prime 3200191069 := by
  apply nodeValid_prime [2, 3, 10301, 25889] ⟨3200191069, 2, [(2, 2), (3, 1), (10301, 1), (25889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10301
    · exact prime_25889
  · decide +kernel

theorem prime_4725869251 : Nat.Prime 4725869251 := by
  apply nodeValid_prime [2, 3, 5, 6301159] ⟨4725869251, 2, [(2, 1), (3, 1), (5, 3), (6301159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6301159
  · decide +kernel

theorem prime_5150466793 : Nat.Prime 5150466793 := by
  apply nodeValid_prime [2, 3, 647, 110563] ⟨5150466793, 5, [(2, 3), (3, 2), (647, 1), (110563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_647
    · exact prime_110563
  · decide +kernel

theorem prime_5584172281 : Nat.Prime 5584172281 := by
  apply nodeValid_prime [2, 3, 5, 46534769] ⟨5584172281, 11, [(2, 3), (3, 1), (5, 1), (46534769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46534769
  · decide +kernel

theorem prime_5739003421 : Nat.Prime 5739003421 := by
  apply nodeValid_prime [2, 3, 5, 95650057] ⟨5739003421, 11, [(2, 2), (3, 1), (5, 1), (95650057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_95650057
  · decide +kernel

theorem prime_7516117313 : Nat.Prime 7516117313 := by
  apply nodeValid_prime [2, 11, 970573] ⟨7516117313, 3, [(2, 6), (11, 2), (970573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_970573
  · decide +kernel

theorem prime_7689351491 : Nat.Prime 7689351491 := by
  apply nodeValid_prime [2, 5, 19, 23, 977, 1801] ⟨7689351491, 2, [(2, 1), (5, 1), (19, 1), (23, 1), (977, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_977
    · exact prime_1801
  · decide +kernel

theorem prime_8403541189 : Nat.Prime 8403541189 := by
  apply nodeValid_prime [2, 3, 7, 23, 337, 12907] ⟨8403541189, 10, [(2, 2), (3, 1), (7, 1), (23, 1), (337, 1), (12907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_337
    · exact prime_12907
  · decide +kernel

theorem prime_11811041453 : Nat.Prime 11811041453 := by
  apply nodeValid_prime [2, 7, 3413, 123593] ⟨11811041453, 3, [(2, 2), (7, 1), (3413, 1), (123593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3413
    · exact prime_123593
  · decide +kernel

theorem prime_11849673713 : Nat.Prime 11849673713 := by
  apply nodeValid_prime [2, 41, 18063527] ⟨11849673713, 3, [(2, 4), (41, 1), (18063527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_18063527
  · decide +kernel

theorem prime_16861768639 : Nat.Prime 16861768639 := by
  apply nodeValid_prime [2, 3, 11, 13, 19652411] ⟨16861768639, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (19652411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19652411
  · decide +kernel

theorem prime_27289870801 : Nat.Prime 27289870801 := by
  apply nodeValid_prime [2, 3, 5, 167, 136177] ⟨27289870801, 11, [(2, 4), (3, 1), (5, 2), (167, 1), (136177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_136177
  · decide +kernel

theorem prime_31410969089 : Nat.Prime 31410969089 := by
  apply nodeValid_prime [2, 17, 3608797] ⟨31410969089, 3, [(2, 9), (17, 1), (3608797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3608797
  · decide +kernel

theorem prime_40733893553 : Nat.Prime 40733893553 := by
  apply nodeValid_prime [2, 11, 2081, 111217] ⟨40733893553, 3, [(2, 4), (11, 1), (2081, 1), (111217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2081
    · exact prime_111217
  · decide +kernel

theorem prime_49041313357 : Nat.Prime 49041313357 := by
  apply nodeValid_prime [2, 3, 7, 139, 227, 18503] ⟨49041313357, 6, [(2, 2), (3, 1), (7, 1), (139, 1), (227, 1), (18503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
    · exact prime_227
    · exact prime_18503
  · decide +kernel

theorem prime_49444481209 : Nat.Prime 49444481209 := by
  apply nodeValid_prime [2, 3, 43, 179, 267661] ⟨49444481209, 22, [(2, 3), (3, 1), (43, 1), (179, 1), (267661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_179
    · exact prime_267661
  · decide +kernel

theorem prime_82003854263 : Nat.Prime 82003854263 := by
  apply nodeValid_prime [2, 11, 149, 1741, 14369] ⟨82003854263, 5, [(2, 1), (11, 1), (149, 1), (1741, 1), (14369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_149
    · exact prime_1741
    · exact prime_14369
  · decide +kernel

theorem prime_82407465191 : Nat.Prime 82407465191 := by
  apply nodeValid_prime [2, 5, 19, 1193, 363557] ⟨82407465191, 7, [(2, 1), (5, 1), (19, 1), (1193, 1), (363557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1193
    · exact prime_363557
  · decide +kernel

theorem prime_122603286049 : Nat.Prime 122603286049 := by
  apply nodeValid_prime [2, 3, 241, 5299243] ⟨122603286049, 7, [(2, 5), (3, 1), (241, 1), (5299243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_5299243
  · decide +kernel

theorem prime_122804418739 : Nat.Prime 122804418739 := by
  apply nodeValid_prime [2, 3, 15619, 1310417] ⟨122804418739, 3, [(2, 1), (3, 1), (15619, 1), (1310417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15619
    · exact prime_1310417
  · decide +kernel

theorem prime_244804731641 : Nat.Prime 244804731641 := by
  apply nodeValid_prime [2, 5, 7, 19, 97, 474391] ⟨244804731641, 3, [(2, 3), (5, 1), (7, 1), (19, 1), (97, 1), (474391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_97
    · exact prime_474391
  · decide +kernel

theorem prime_247626907991 : Nat.Prime 247626907991 := by
  apply nodeValid_prime [2, 5, 7, 11, 17747, 18121] ⟨247626907991, 11, [(2, 1), (5, 1), (7, 1), (11, 1), (17747, 1), (18121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17747
    · exact prime_18121
  · decide +kernel

theorem prime_251287752713 : Nat.Prime 251287752713 := by
  apply nodeValid_prime [2, 31410969089] ⟨251287752713, 3, [(2, 3), (31410969089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31410969089
  · decide +kernel

theorem prime_488806710797 : Nat.Prime 488806710797 := by
  apply nodeValid_prime [2, 93983, 1300253] ⟨488806710797, 2, [(2, 2), (93983, 1), (1300253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_93983
    · exact prime_1300253
  · decide +kernel

theorem prime_488806722637 : Nat.Prime 488806722637 := by
  apply nodeValid_prime [2, 3, 40733893553] ⟨488806722637, 5, [(2, 2), (3, 1), (40733893553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40733893553
  · decide +kernel

theorem prime_488806722793 : Nat.Prime 488806722793 := by
  apply nodeValid_prime [2, 3, 73, 83, 139, 2687] ⟨488806722793, 5, [(2, 3), (3, 3), (73, 1), (83, 1), (139, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_83
    · exact prime_139
    · exact prime_2687
  · decide +kernel

theorem prime_489609463283 : Nat.Prime 489609463283 := by
  apply nodeValid_prime [2, 244804731641] ⟨489609463283, 2, [(2, 1), (244804731641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_244804731641
  · decide +kernel

theorem prime_489609463723 : Nat.Prime 489609463723 := by
  apply nodeValid_prime [2, 3, 137, 595631951] ⟨489609463723, 3, [(2, 1), (3, 1), (137, 1), (595631951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_595631951
  · decide +kernel

theorem prime_489609478711 : Nat.Prime 489609478711 := by
  apply nodeValid_prime [2, 3, 5, 11, 409, 1209181] ⟨489609478711, 30, [(2, 1), (3, 2), (5, 1), (11, 1), (409, 1), (1209181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_409
    · exact prime_1209181
  · decide +kernel

theorem prime_490413133571 : Nat.Prime 490413133571 := by
  apply nodeValid_prime [2, 5, 49041313357] ⟨490413133571, 2, [(2, 1), (5, 1), (49041313357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49041313357
  · decide +kernel

theorem prime_490413144197 : Nat.Prime 490413144197 := by
  apply nodeValid_prime [2, 122603286049] ⟨490413144197, 2, [(2, 2), (122603286049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_122603286049
  · decide +kernel

theorem prime_490413145129 : Nat.Prime 490413145129 := by
  apply nodeValid_prime [2, 3, 1039, 3457, 5689] ⟨490413145129, 13, [(2, 3), (3, 1), (1039, 1), (3457, 1), (5689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1039
    · exact prime_3457
    · exact prime_5689
  · decide +kernel

theorem prime_491217672619 : Nat.Prime 491217672619 := by
  apply nodeValid_prime [2, 3, 37, 67, 3669473] ⟨491217672619, 2, [(2, 1), (3, 3), (37, 1), (67, 1), (3669473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_67
    · exact prime_3669473
  · decide +kernel

theorem prime_491217674419 : Nat.Prime 491217674419 := by
  apply nodeValid_prime [2, 3, 27289870801] ⟨491217674419, 3, [(2, 1), (3, 2), (27289870801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27289870801
  · decide +kernel

theorem prime_491217674957 : Nat.Prime 491217674957 := by
  apply nodeValid_prime [2, 122804418739] ⟨491217674957, 2, [(2, 2), (122804418739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_122804418739
  · decide +kernel

theorem prime_492023102449 : Nat.Prime 492023102449 := by
  apply nodeValid_prime [2, 3, 173, 6857, 8641] ⟨492023102449, 13, [(2, 4), (3, 1), (173, 1), (6857, 1), (8641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_6857
    · exact prime_8641
  · decide +kernel

theorem prime_492023125579 : Nat.Prime 492023125579 := by
  apply nodeValid_prime [2, 3, 82003854263] ⟨492023125579, 2, [(2, 1), (3, 1), (82003854263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_82003854263
  · decide +kernel

theorem prime_492023126197 : Nat.Prime 492023126197 := by
  apply nodeValid_prime [2, 3, 7, 650824241] ⟨492023126197, 2, [(2, 2), (3, 3), (7, 1), (650824241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_650824241
  · decide +kernel

theorem prime_492829424209 : Nat.Prime 492829424209 := by
  apply nodeValid_prime [2, 3, 11, 311, 90947] ⟨492829424209, 7, [(2, 4), (3, 2), (11, 2), (311, 1), (90947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_311
    · exact prime_90947
  · decide +kernel

theorem prime_492829424627 : Nat.Prime 492829424627 := by
  apply nodeValid_prime [2, 7, 11, 3200191069] ⟨492829424627, 2, [(2, 1), (7, 1), (11, 1), (3200191069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_3200191069
  · decide +kernel

theorem prime_492829428067 : Nat.Prime 492829428067 := by
  apply nodeValid_prime [2, 3, 31, 40189, 65929] ⟨492829428067, 2, [(2, 1), (3, 1), (31, 1), (40189, 1), (65929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_40189
    · exact prime_65929
  · decide +kernel

theorem prime_493636634779 : Nat.Prime 493636634779 := by
  apply nodeValid_prime [2, 3, 7, 277, 42430517] ⟨493636634779, 2, [(2, 1), (3, 1), (7, 1), (277, 1), (42430517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_277
    · exact prime_42430517
  · decide +kernel

theorem prime_493636635067 : Nat.Prime 493636635067 := by
  apply nodeValid_prime [2, 3, 521, 3571, 44221] ⟨493636635067, 2, [(2, 1), (3, 1), (521, 1), (3571, 1), (44221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_3571
    · exact prime_44221
  · decide +kernel

theorem prime_493636659793 : Nat.Prime 493636659793 := by
  apply nodeValid_prime [2, 3, 17, 4993, 7127] ⟨493636659793, 5, [(2, 4), (3, 1), (17, 2), (4993, 1), (7127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4993
    · exact prime_7127
  · decide +kernel

theorem prime_494444791147 : Nat.Prime 494444791147 := by
  apply nodeValid_prime [2, 3, 82407465191] ⟨494444791147, 2, [(2, 1), (3, 1), (82407465191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_82407465191
  · decide +kernel

theorem prime_494444812091 : Nat.Prime 494444812091 := by
  apply nodeValid_prime [2, 5, 49444481209] ⟨494444812091, 6, [(2, 1), (5, 1), (49444481209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49444481209
  · decide +kernel

theorem prime_494444812129 : Nat.Prime 494444812129 := by
  apply nodeValid_prime [2, 3, 5150466793] ⟨494444812129, 13, [(2, 5), (3, 1), (5150466793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5150466793
  · decide +kernel

theorem prime_495253815893 : Nat.Prime 495253815893 := by
  apply nodeValid_prime [2, 11, 23, 489381241] ⟨495253815893, 2, [(2, 2), (11, 1), (23, 1), (489381241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_489381241
  · decide +kernel

theorem prime_495253815983 : Nat.Prime 495253815983 := by
  apply nodeValid_prime [2, 247626907991] ⟨495253815983, 5, [(2, 1), (247626907991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_247626907991
  · decide +kernel

theorem prime_495253819741 : Nat.Prime 495253819741 := by
  apply nodeValid_prime [2, 3, 5, 89, 92744161] ⟨495253819741, 2, [(2, 2), (3, 1), (5, 1), (89, 1), (92744161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_92744161
  · decide +kernel

theorem prime_496063741027 : Nat.Prime 496063741027 := by
  apply nodeValid_prime [2, 3, 7, 11811041453] ⟨496063741027, 2, [(2, 1), (3, 1), (7, 1), (11811041453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11811041453
  · decide +kernel

theorem prime_496063742659 : Nat.Prime 496063742659 := by
  apply nodeValid_prime [2, 3, 11, 7516117313] ⟨496063742659, 2, [(2, 1), (3, 1), (11, 1), (7516117313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_7516117313
  · decide +kernel

theorem prime_496063748549 : Nat.Prime 496063748549 := by
  apply nodeValid_prime [2, 111323, 1114019] ⟨496063748549, 2, [(2, 2), (111323, 1), (1114019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_111323
    · exact prime_1114019
  · decide +kernel

theorem prime_496874568871 : Nat.Prime 496874568871 := by
  apply nodeValid_prime [2, 3, 5, 199, 9247619] ⟨496874568871, 13, [(2, 1), (3, 3), (5, 1), (199, 1), (9247619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_9247619
  · decide +kernel

theorem prime_496874568901 : Nat.Prime 496874568901 := by
  apply nodeValid_prime [2, 3, 5, 19, 31, 281, 10007] ⟨496874568901, 10, [(2, 2), (3, 1), (5, 2), (19, 1), (31, 1), (281, 1), (10007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_31
    · exact prime_281
    · exact prime_10007
  · decide +kernel

theorem prime_496874574827 : Nat.Prime 496874574827 := by
  apply nodeValid_prime [2, 7, 331, 829, 129341] ⟨496874574827, 2, [(2, 1), (7, 1), (331, 1), (829, 1), (129341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_331
    · exact prime_829
    · exact prime_129341
  · decide +kernel

theorem prime_497686295947 : Nat.Prime 497686295947 := by
  apply nodeValid_prime [2, 3, 7, 11849673713] ⟨497686295947, 2, [(2, 1), (3, 1), (7, 1), (11849673713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11849673713
  · decide +kernel

theorem prime_497686310309 : Nat.Prime 497686310309 := by
  apply nodeValid_prime [2, 11, 19, 595318553] ⟨497686310309, 2, [(2, 2), (11, 1), (19, 1), (595318553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_595318553
  · decide +kernel

theorem prime_497686311119 : Nat.Prime 497686311119 := by
  apply nodeValid_prime [2, 23, 421, 25698973] ⟨497686311119, 7, [(2, 1), (23, 1), (421, 1), (25698973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_421
    · exact prime_25698973
  · decide +kernel

theorem prime_498498920497 : Nat.Prime 498498920497 := by
  apply nodeValid_prime [2, 3, 41, 84434099] ⟨498498920497, 5, [(2, 4), (3, 2), (41, 1), (84434099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_84434099
  · decide +kernel

theorem prime_498498931331 : Nat.Prime 498498931331 := by
  apply nodeValid_prime [2, 5, 37, 2719, 495511] ⟨498498931331, 2, [(2, 1), (5, 1), (37, 1), (2719, 1), (495511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_2719
    · exact prime_495511
  · decide +kernel

theorem prime_498498932161 : Nat.Prime 498498932161 := by
  apply nodeValid_prime [2, 3, 5, 131, 853, 1549] ⟨498498932161, 11, [(2, 6), (3, 2), (5, 1), (131, 1), (853, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_853
    · exact prime_1549
  · decide +kernel

theorem prime_499312421857 : Nat.Prime 499312421857 := by
  apply nodeValid_prime [2, 3, 1733723687] ⟨499312421857, 11, [(2, 5), (3, 2), (1733723687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1733723687
  · decide +kernel

theorem prime_499312422751 : Nat.Prime 499312422751 := by
  apply nodeValid_prime [2, 3, 5, 29, 97, 8161] ⟨499312422751, 6, [(2, 1), (3, 1), (5, 3), (29, 2), (97, 1), (8161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_97
    · exact prime_8161
  · decide +kernel

theorem prime_499312439111 : Nat.Prime 499312439111 := by
  apply nodeValid_prime [2, 5, 173, 10061, 28687] ⟨499312439111, 13, [(2, 1), (5, 1), (173, 1), (10061, 1), (28687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_10061
    · exact prime_28687
  · decide +kernel

theorem prime_500126817241 : Nat.Prime 500126817241 := by
  apply nodeValid_prime [2, 3, 5, 1389241159] ⟨500126817241, 11, [(2, 3), (3, 2), (5, 1), (1389241159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1389241159
  · decide +kernel

theorem prime_500126817271 : Nat.Prime 500126817271 := by
  apply nodeValid_prime [2, 3, 5, 137, 617, 197221] ⟨500126817271, 6, [(2, 1), (3, 1), (5, 1), (137, 1), (617, 1), (197221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_617
    · exact prime_197221
  · decide +kernel

theorem prime_500126855233 : Nat.Prime 500126855233 := by
  apply nodeValid_prime [2, 3, 283, 9204337] ⟨500126855233, 10, [(2, 6), (3, 1), (283, 1), (9204337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_9204337
  · decide +kernel

theorem prime_500942140607 : Nat.Prime 500942140607 := by
  apply nodeValid_prime [2, 53, 4725869251] ⟨500942140607, 5, [(2, 1), (53, 1), (4725869251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_4725869251
  · decide +kernel

theorem prime_500942168473 : Nat.Prime 500942168473 := by
  apply nodeValid_prime [2, 3, 19, 877, 1252631] ⟨500942168473, 5, [(2, 3), (3, 1), (19, 1), (877, 1), (1252631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_877
    · exact prime_1252631
  · decide +kernel

theorem prime_501758380033 : Nat.Prime 501758380033 := by
  apply nodeValid_prime [2, 3, 7, 13, 897433] ⟨501758380033, 35, [(2, 11), (3, 1), (7, 1), (13, 1), (897433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_897433
  · decide +kernel

theorem prime_501758380289 : Nat.Prime 501758380289 := by
  apply nodeValid_prime [2, 11, 178181243] ⟨501758380289, 3, [(2, 8), (11, 1), (178181243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_178181243
  · decide +kernel

theorem prime_501758381053 : Nat.Prime 501758381053 := by
  apply nodeValid_prime [2, 3, 8147, 1710781] ⟨501758381053, 5, [(2, 2), (3, 2), (8147, 1), (1710781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8147
    · exact prime_1710781
  · decide +kernel

theorem prime_502575504463 : Nat.Prime 502575504463 := by
  apply nodeValid_prime [2, 3, 233, 317, 378019] ⟨502575504463, 3, [(2, 1), (3, 2), (233, 1), (317, 1), (378019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_317
    · exact prime_378019
  · decide +kernel

theorem prime_502575505291 : Nat.Prime 502575505291 := by
  apply nodeValid_prime [2, 3, 5, 5584172281] ⟨502575505291, 22, [(2, 1), (3, 2), (5, 1), (5584172281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5584172281
  · decide +kernel

theorem prime_502575505427 : Nat.Prime 502575505427 := by
  apply nodeValid_prime [2, 251287752713] ⟨502575505427, 2, [(2, 1), (251287752713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_251287752713
  · decide +kernel

theorem prime_503393534671 : Nat.Prime 503393534671 := by
  apply nodeValid_prime [2, 3, 5, 13, 269, 4798337] ⟨503393534671, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (269, 1), (4798337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_269
    · exact prime_4798337
  · decide +kernel

theorem prime_503393534687 : Nat.Prime 503393534687 := by
  apply nodeValid_prime [2, 7, 47, 765035767] ⟨503393534687, 5, [(2, 1), (7, 1), (47, 1), (765035767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_765035767
  · decide +kernel

theorem prime_503393534711 : Nat.Prime 503393534711 := by
  apply nodeValid_prime [2, 5, 11, 719, 6364819] ⟨503393534711, 7, [(2, 1), (5, 1), (11, 1), (719, 1), (6364819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_719
    · exact prime_6364819
  · decide +kernel

theorem prime_504212468699 : Nat.Prime 504212468699 := by
  apply nodeValid_prime [2, 409, 2399, 256939] ⟨504212468699, 2, [(2, 1), (409, 1), (2399, 1), (256939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_2399
    · exact prime_256939
  · decide +kernel

theorem prime_504212471341 : Nat.Prime 504212471341 := by
  apply nodeValid_prime [2, 3, 5, 8403541189] ⟨504212471341, 6, [(2, 2), (3, 1), (5, 1), (8403541189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8403541189
  · decide +kernel

theorem prime_504212471407 : Nat.Prime 504212471407 := by
  apply nodeValid_prime [2, 3, 7, 379, 391057] ⟨504212471407, 5, [(2, 1), (3, 5), (7, 1), (379, 1), (391057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_379
    · exact prime_391057
  · decide +kernel

theorem prime_505032277759 : Nat.Prime 505032277759 := by
  apply nodeValid_prime [2, 3, 199, 2659, 159073] ⟨505032277759, 3, [(2, 1), (3, 1), (199, 1), (2659, 1), (159073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_2659
    · exact prime_159073
  · decide +kernel

theorem prime_505032278189 : Nat.Prime 505032278189 := by
  apply nodeValid_prime [2, 443, 285006929] ⟨505032278189, 2, [(2, 2), (443, 1), (285006929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_285006929
  · decide +kernel

theorem prime_505032301049 : Nat.Prime 505032301049 := by
  apply nodeValid_prime [2, 11, 5739003421] ⟨505032301049, 3, [(2, 3), (11, 1), (5739003421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_5739003421
  · decide +kernel

theorem prime_505853040307 : Nat.Prime 505853040307 := by
  apply nodeValid_prime [2, 3, 7643, 11030857] ⟨505853040307, 2, [(2, 1), (3, 1), (7643, 1), (11030857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7643
    · exact prime_11030857
  · decide +kernel

theorem prime_505853059171 : Nat.Prime 505853059171 := by
  apply nodeValid_prime [2, 3, 5, 16861768639] ⟨505853059171, 10, [(2, 1), (3, 1), (5, 1), (16861768639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16861768639
  · decide +kernel

theorem prime_505853059783 : Nat.Prime 505853059783 := by
  apply nodeValid_prime [2, 3, 7, 29, 415314499] ⟨505853059783, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (415314499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_415314499
  · decide +kernel

theorem prime_506674694459 : Nat.Prime 506674694459 := by
  apply nodeValid_prime [2, 19, 137, 883, 110221] ⟨506674694459, 2, [(2, 1), (19, 1), (137, 1), (883, 1), (110221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_137
    · exact prime_883
    · exact prime_110221
  · decide +kernel

theorem prime_506674705151 : Nat.Prime 506674705151 := by
  apply nodeValid_prime [2, 5, 37, 233, 683, 1721] ⟨506674705151, 23, [(2, 1), (5, 2), (37, 1), (233, 1), (683, 1), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_233
    · exact prime_683
    · exact prime_1721
  · decide +kernel

theorem prime_506674706093 : Nat.Prime 506674706093 := by
  apply nodeValid_prime [2, 17, 167, 44617357] ⟨506674706093, 2, [(2, 2), (17, 1), (167, 1), (44617357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_167
    · exact prime_44617357
  · decide +kernel

theorem prime_507497198287 : Nat.Prime 507497198287 := by
  apply nodeValid_prime [2, 3, 13, 41, 158692057] ⟨507497198287, 6, [(2, 1), (3, 1), (13, 1), (41, 1), (158692057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_158692057
  · decide +kernel

theorem prime_507497198407 : Nat.Prime 507497198407 := by
  apply nodeValid_prime [2, 3, 11, 7689351491] ⟨507497198407, 3, [(2, 1), (3, 1), (11, 1), (7689351491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_7689351491
  · decide +kernel

theorem prime_507497255261 : Nat.Prime 507497255261 := by
  apply nodeValid_prime [2, 5, 127, 4813, 41513] ⟨507497255261, 2, [(2, 2), (5, 1), (127, 1), (4813, 1), (41513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_4813
    · exact prime_41513
  · decide +kernel

theorem prime_508320715181 : Nat.Prime 508320715181 := by
  apply nodeValid_prime [2, 5, 17, 23, 4723, 13763] ⟨508320715181, 2, [(2, 2), (5, 1), (17, 1), (23, 1), (4723, 1), (13763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_4723
    · exact prime_13763
  · decide +kernel

theorem prime_508320720463 : Nat.Prime 508320720463 := by
  apply nodeValid_prime [2, 3, 1033, 2953, 27773] ⟨508320720463, 5, [(2, 1), (3, 1), (1033, 1), (2953, 1), (27773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
    · exact prime_2953
    · exact prime_27773
  · decide +kernel

theorem prime_508320721393 : Nat.Prime 508320721393 := by
  apply nodeValid_prime [2, 3, 11, 17467, 55117] ⟨508320721393, 10, [(2, 4), (3, 1), (11, 1), (17467, 1), (55117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17467
    · exact prime_55117
  · decide +kernel

end Sude.Lucas.Generated
