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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3547 : Nat.Prime 3547 := by
  apply nodeValid_prime [2, 3, 197] ⟨3547, 2, [(2, 1), (3, 2), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
  · decide +kernel

theorem prime_4049 : Nat.Prime 4049 := by
  apply nodeValid_prime [2, 11, 23] ⟨4049, 3, [(2, 4), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_5303 : Nat.Prime 5303 := by
  apply nodeValid_prime [2, 11, 241] ⟨5303, 5, [(2, 1), (11, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_241
  · decide +kernel

theorem prime_5953 : Nat.Prime 5953 := by
  apply nodeValid_prime [2, 3, 31] ⟨5953, 7, [(2, 6), (3, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_6427 : Nat.Prime 6427 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨6427, 3, [(2, 1), (3, 3), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_6691 : Nat.Prime 6691 := by
  apply nodeValid_prime [2, 3, 5, 223] ⟨6691, 2, [(2, 1), (3, 1), (5, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
  · decide +kernel

theorem prime_6761 : Nat.Prime 6761 := by
  apply nodeValid_prime [2, 5, 13] ⟨6761, 3, [(2, 3), (5, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_7333 : Nat.Prime 7333 := by
  apply nodeValid_prime [2, 3, 13, 47] ⟨7333, 6, [(2, 2), (3, 1), (13, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_8387 : Nat.Prime 8387 := by
  apply nodeValid_prime [2, 7, 599] ⟨8387, 2, [(2, 1), (7, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_599
  · decide +kernel

theorem prime_8779 : Nat.Prime 8779 := by
  apply nodeValid_prime [2, 3, 7, 11, 19] ⟨8779, 11, [(2, 1), (3, 1), (7, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_8807 : Nat.Prime 8807 := by
  apply nodeValid_prime [2, 7, 17, 37] ⟨8807, 5, [(2, 1), (7, 1), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_9461 : Nat.Prime 9461 := by
  apply nodeValid_prime [2, 5, 11, 43] ⟨9461, 3, [(2, 2), (5, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_9733 : Nat.Prime 9733 := by
  apply nodeValid_prime [2, 3, 811] ⟨9733, 2, [(2, 2), (3, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
  · decide +kernel

theorem prime_10061 : Nat.Prime 10061 := by
  apply nodeValid_prime [2, 5, 503] ⟨10061, 3, [(2, 2), (5, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_503
  · decide +kernel

theorem prime_10607 : Nat.Prime 10607 := by
  apply nodeValid_prime [2, 5303] ⟨10607, 5, [(2, 1), (5303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5303
  · decide +kernel

theorem prime_10627 : Nat.Prime 10627 := by
  apply nodeValid_prime [2, 3, 7, 11, 23] ⟨10627, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_11329 : Nat.Prime 11329 := by
  apply nodeValid_prime [2, 3, 59] ⟨11329, 7, [(2, 6), (3, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_13049 : Nat.Prime 13049 := by
  apply nodeValid_prime [2, 7, 233] ⟨13049, 3, [(2, 3), (7, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_233
  · decide +kernel

theorem prime_13649 : Nat.Prime 13649 := by
  apply nodeValid_prime [2, 853] ⟨13649, 3, [(2, 4), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_853
  · decide +kernel

theorem prime_14143 : Nat.Prime 14143 := by
  apply nodeValid_prime [2, 3, 2357] ⟨14143, 3, [(2, 1), (3, 1), (2357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2357
  · decide +kernel

theorem prime_14723 : Nat.Prime 14723 := by
  apply nodeValid_prime [2, 17, 433] ⟨14723, 2, [(2, 1), (17, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_433
  · decide +kernel

theorem prime_14737 : Nat.Prime 14737 := by
  apply nodeValid_prime [2, 3, 307] ⟨14737, 10, [(2, 4), (3, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
  · decide +kernel

theorem prime_15349 : Nat.Prime 15349 := by
  apply nodeValid_prime [2, 3, 1279] ⟨15349, 2, [(2, 2), (3, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
  · decide +kernel

theorem prime_17093 : Nat.Prime 17093 := by
  apply nodeValid_prime [2, 4273] ⟨17093, 2, [(2, 2), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4273
  · decide +kernel

theorem prime_20369 : Nat.Prime 20369 := by
  apply nodeValid_prime [2, 19, 67] ⟨20369, 3, [(2, 4), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_20563 : Nat.Prime 20563 := by
  apply nodeValid_prime [2, 3, 23, 149] ⟨20563, 3, [(2, 1), (3, 1), (23, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_149
  · decide +kernel

theorem prime_25537 : Nat.Prime 25537 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨25537, 10, [(2, 6), (3, 1), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_25763 : Nat.Prime 25763 := by
  apply nodeValid_prime [2, 11, 1171] ⟨25763, 5, [(2, 1), (11, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1171
  · decide +kernel

theorem prime_27299 : Nat.Prime 27299 := by
  apply nodeValid_prime [2, 13649] ⟨27299, 2, [(2, 1), (13649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13649
  · decide +kernel

theorem prime_27847 : Nat.Prime 27847 := by
  apply nodeValid_prime [2, 3, 7, 13, 17] ⟨27847, 6, [(2, 1), (3, 2), (7, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_32789 : Nat.Prime 32789 := by
  apply nodeValid_prime [2, 7, 1171] ⟨32789, 2, [(2, 2), (7, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1171
  · decide +kernel

theorem prime_35099 : Nat.Prime 35099 := by
  apply nodeValid_prime [2, 7, 23, 109] ⟨35099, 2, [(2, 1), (7, 1), (23, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_109
  · decide +kernel

theorem prime_35111 : Nat.Prime 35111 := by
  apply nodeValid_prime [2, 5, 3511] ⟨35111, 13, [(2, 1), (5, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3511
  · decide +kernel

theorem prime_35117 : Nat.Prime 35117 := by
  apply nodeValid_prime [2, 8779] ⟨35117, 2, [(2, 2), (8779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8779
  · decide +kernel

theorem prime_40361 : Nat.Prime 40361 := by
  apply nodeValid_prime [2, 5, 1009] ⟨40361, 3, [(2, 3), (5, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1009
  · decide +kernel

theorem prime_44633 : Nat.Prime 44633 := by
  apply nodeValid_prime [2, 7, 797] ⟨44633, 3, [(2, 3), (7, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_797
  · decide +kernel

theorem prime_44711 : Nat.Prime 44711 := by
  apply nodeValid_prime [2, 5, 17, 263] ⟨44711, 7, [(2, 1), (5, 1), (17, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_263
  · decide +kernel

theorem prime_48757 : Nat.Prime 48757 := by
  apply nodeValid_prime [2, 3, 17, 239] ⟨48757, 2, [(2, 2), (3, 1), (17, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_239
  · decide +kernel

theorem prime_50969 : Nat.Prime 50969 := by
  apply nodeValid_prime [2, 23, 277] ⟨50969, 3, [(2, 3), (23, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_277
  · decide +kernel

theorem prime_52517 : Nat.Prime 52517 := by
  apply nodeValid_prime [2, 19, 691] ⟨52517, 2, [(2, 2), (19, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_691
  · decide +kernel

theorem prime_58579 : Nat.Prime 58579 := by
  apply nodeValid_prime [2, 3, 13, 751] ⟨58579, 2, [(2, 1), (3, 1), (13, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_751
  · decide +kernel

theorem prime_65579 : Nat.Prime 65579 := by
  apply nodeValid_prime [2, 32789] ⟨65579, 2, [(2, 1), (32789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32789
  · decide +kernel

theorem prime_68819 : Nat.Prime 68819 := by
  apply nodeValid_prime [2, 19, 1811] ⟨68819, 2, [(2, 1), (19, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1811
  · decide +kernel

theorem prime_70199 : Nat.Prime 70199 := by
  apply nodeValid_prime [2, 35099] ⟨70199, 17, [(2, 1), (35099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35099
  · decide +kernel

theorem prime_70753 : Nat.Prime 70753 := by
  apply nodeValid_prime [2, 3, 11, 67] ⟨70753, 5, [(2, 5), (3, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_71287 : Nat.Prime 71287 := by
  apply nodeValid_prime [2, 3, 109] ⟨71287, 3, [(2, 1), (3, 1), (109, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_75787 : Nat.Prime 75787 := by
  apply nodeValid_prime [2, 3, 17, 743] ⟨75787, 5, [(2, 1), (3, 1), (17, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_743
  · decide +kernel

theorem prime_84649 : Nat.Prime 84649 := by
  apply nodeValid_prime [2, 3, 3527] ⟨84649, 13, [(2, 3), (3, 1), (3527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3527
  · decide +kernel

theorem prime_88339 : Nat.Prime 88339 := by
  apply nodeValid_prime [2, 3, 14723] ⟨88339, 3, [(2, 1), (3, 1), (14723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14723
  · decide +kernel

theorem prime_88423 : Nat.Prime 88423 := by
  apply nodeValid_prime [2, 3, 14737] ⟨88423, 6, [(2, 1), (3, 1), (14737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14737
  · decide +kernel

theorem prime_89519 : Nat.Prime 89519 := by
  apply nodeValid_prime [2, 11, 13, 313] ⟨89519, 11, [(2, 1), (11, 1), (13, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_313
  · decide +kernel

theorem prime_90989 : Nat.Prime 90989 := by
  apply nodeValid_prime [2, 23, 43] ⟨90989, 2, [(2, 2), (23, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
  · decide +kernel

theorem prime_91771 : Nat.Prime 91771 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 23] ⟨91771, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_96697 : Nat.Prime 96697 := by
  apply nodeValid_prime [2, 3, 17, 79] ⟨96697, 7, [(2, 3), (3, 2), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_101939 : Nat.Prime 101939 := by
  apply nodeValid_prime [2, 50969] ⟨101939, 2, [(2, 1), (50969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_50969
  · decide +kernel

theorem prime_112087 : Nat.Prime 112087 := by
  apply nodeValid_prime [2, 3, 13, 479] ⟨112087, 3, [(2, 1), (3, 2), (13, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_479
  · decide +kernel

theorem prime_144241 : Nat.Prime 144241 := by
  apply nodeValid_prime [2, 3, 5, 601] ⟨144241, 13, [(2, 4), (3, 1), (5, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_601
  · decide +kernel

theorem prime_145381 : Nat.Prime 145381 := by
  apply nodeValid_prime [2, 3, 5, 2423] ⟨145381, 2, [(2, 2), (3, 1), (5, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2423
  · decide +kernel

theorem prime_145433 : Nat.Prime 145433 := by
  apply nodeValid_prime [2, 7, 53] ⟨145433, 3, [(2, 3), (7, 3), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_170633 : Nat.Prime 170633 := by
  apply nodeValid_prime [2, 7, 11, 277] ⟨170633, 3, [(2, 3), (7, 1), (11, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_277
  · decide +kernel

theorem prime_179957 : Nat.Prime 179957 := by
  apply nodeValid_prime [2, 7, 6427] ⟨179957, 2, [(2, 2), (7, 1), (6427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6427
  · decide +kernel

theorem prime_184189 : Nat.Prime 184189 := by
  apply nodeValid_prime [2, 3, 15349] ⟨184189, 2, [(2, 2), (3, 1), (15349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15349
  · decide +kernel

theorem prime_195443 : Nat.Prime 195443 := by
  apply nodeValid_prime [2, 13, 7517] ⟨195443, 2, [(2, 1), (13, 1), (7517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_7517
  · decide +kernel

theorem prime_212141 : Nat.Prime 212141 := by
  apply nodeValid_prime [2, 5, 10607] ⟨212141, 2, [(2, 2), (5, 1), (10607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10607
  · decide +kernel

theorem prime_232007 : Nat.Prime 232007 := by
  apply nodeValid_prime [2, 311, 373] ⟨232007, 5, [(2, 1), (311, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_373
  · decide +kernel

theorem prime_251639 : Nat.Prime 251639 := by
  apply nodeValid_prime [2, 47, 2677] ⟨251639, 11, [(2, 1), (47, 1), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_2677
  · decide +kernel

theorem prime_251789 : Nat.Prime 251789 := by
  apply nodeValid_prime [2, 19, 3313] ⟨251789, 2, [(2, 2), (19, 1), (3313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3313
  · decide +kernel

theorem prime_251857 : Nat.Prime 251857 := by
  apply nodeValid_prime [2, 3, 11, 53] ⟨251857, 13, [(2, 4), (3, 3), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_255371 : Nat.Prime 255371 := by
  apply nodeValid_prime [2, 5, 25537] ⟨255371, 6, [(2, 1), (5, 1), (25537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25537
  · decide +kernel

theorem prime_255443 : Nat.Prime 255443 := by
  apply nodeValid_prime [2, 11, 17, 683] ⟨255443, 2, [(2, 1), (11, 1), (17, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_683
  · decide +kernel

theorem prime_283489 : Nat.Prime 283489 := by
  apply nodeValid_prime [2, 3, 2953] ⟨283489, 7, [(2, 5), (3, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2953
  · decide +kernel

theorem prime_284377 : Nat.Prime 284377 := by
  apply nodeValid_prime [2, 3, 17, 41] ⟨284377, 5, [(2, 3), (3, 1), (17, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_301831 : Nat.Prime 301831 := by
  apply nodeValid_prime [2, 3, 5, 10061] ⟨301831, 3, [(2, 1), (3, 1), (5, 1), (10061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10061
  · decide +kernel

theorem prime_345727 : Nat.Prime 345727 := by
  apply nodeValid_prime [2, 3, 19207] ⟨345727, 3, [(2, 1), (3, 2), (19207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19207
  · decide +kernel

theorem prime_400243 : Nat.Prime 400243 := by
  apply nodeValid_prime [2, 3, 41, 1627] ⟨400243, 2, [(2, 1), (3, 1), (41, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1627
  · decide +kernel

theorem prime_481753 : Nat.Prime 481753 := by
  apply nodeValid_prime [2, 3, 6691] ⟨481753, 5, [(2, 3), (3, 2), (6691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6691
  · decide +kernel

theorem prime_524633 : Nat.Prime 524633 := by
  apply nodeValid_prime [2, 65579] ⟨524633, 3, [(2, 3), (65579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_65579
  · decide +kernel

theorem prime_560869 : Nat.Prime 560869 := by
  apply nodeValid_prime [2, 3, 7, 11, 607] ⟨560869, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_607
  · decide +kernel

theorem prime_577601 : Nat.Prime 577601 := by
  apply nodeValid_prime [2, 5, 19] ⟨577601, 3, [(2, 6), (5, 2), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_580183 : Nat.Prime 580183 := by
  apply nodeValid_prime [2, 3, 96697] ⟨580183, 3, [(2, 1), (3, 1), (96697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_96697
  · decide +kernel

theorem prime_671537 : Nat.Prime 671537 := by
  apply nodeValid_prime [2, 19, 47] ⟨671537, 3, [(2, 4), (19, 1), (47, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_759691 : Nat.Prime 759691 := by
  apply nodeValid_prime [2, 3, 5, 23, 367] ⟨759691, 2, [(2, 1), (3, 2), (5, 1), (23, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_367
  · decide +kernel

theorem prime_1015627 : Nat.Prime 1015627 := by
  apply nodeValid_prime [2, 3, 19, 59, 151] ⟨1015627, 5, [(2, 1), (3, 1), (19, 1), (59, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
    · exact prime_151
  · decide +kernel

theorem prime_1032901 : Nat.Prime 1032901 := by
  apply nodeValid_prime [2, 3, 5, 11, 313] ⟨1032901, 6, [(2, 2), (3, 1), (5, 2), (11, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_313
  · decide +kernel

theorem prime_1053511 : Nat.Prime 1053511 := by
  apply nodeValid_prime [2, 3, 5, 35117] ⟨1053511, 3, [(2, 1), (3, 1), (5, 1), (35117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35117
  · decide +kernel

theorem prime_1092629 : Nat.Prime 1092629 := by
  apply nodeValid_prime [2, 273157] ⟨1092629, 2, [(2, 2), (273157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_273157
  · decide +kernel

theorem prime_1121737 : Nat.Prime 1121737 := by
  apply nodeValid_prime [2, 3, 7, 11, 607] ⟨1121737, 13, [(2, 3), (3, 1), (7, 1), (11, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_607
  · decide +kernel

theorem prime_1316033 : Nat.Prime 1316033 := by
  apply nodeValid_prime [2, 20563] ⟨1316033, 3, [(2, 6), (20563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20563
  · decide +kernel

theorem prime_1532659 : Nat.Prime 1532659 := by
  apply nodeValid_prime [2, 3, 255443] ⟨1532659, 3, [(2, 1), (3, 1), (255443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_255443
  · decide +kernel

theorem prime_1550033 : Nat.Prime 1550033 := by
  apply nodeValid_prime [2, 11, 8807] ⟨1550033, 3, [(2, 4), (11, 1), (8807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8807
  · decide +kernel

theorem prime_1684777 : Nat.Prime 1684777 := by
  apply nodeValid_prime [2, 3, 70199] ⟨1684777, 5, [(2, 3), (3, 1), (70199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_70199
  · decide +kernel

theorem prime_2461397 : Nat.Prime 2461397 := by
  apply nodeValid_prime [2, 7, 17, 5171] ⟨2461397, 2, [(2, 2), (7, 1), (17, 1), (5171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_5171
  · decide +kernel

theorem prime_2864441 : Nat.Prime 2864441 := by
  apply nodeValid_prime [2, 5, 19, 3769] ⟨2864441, 3, [(2, 3), (5, 1), (19, 1), (3769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3769
  · decide +kernel

theorem prime_3116761 : Nat.Prime 3116761 := by
  apply nodeValid_prime [2, 3, 5, 19, 1367] ⟨3116761, 11, [(2, 3), (3, 1), (5, 1), (19, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1367
  · decide +kernel

theorem prime_3486151 : Nat.Prime 3486151 := by
  apply nodeValid_prime [2, 3, 5, 61, 127] ⟨3486151, 7, [(2, 1), (3, 2), (5, 2), (61, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_127
  · decide +kernel

theorem prime_3849499 : Nat.Prime 3849499 := by
  apply nodeValid_prime [2, 3, 71287] ⟨3849499, 3, [(2, 1), (3, 3), (71287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71287
  · decide +kernel

theorem prime_4155401 : Nat.Prime 4155401 := by
  apply nodeValid_prime [2, 5, 79, 263] ⟨4155401, 3, [(2, 3), (5, 2), (79, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_263
  · decide +kernel

theorem prime_5554333 : Nat.Prime 5554333 := by
  apply nodeValid_prime [2, 3, 7, 31, 79] ⟨5554333, 14, [(2, 2), (3, 4), (7, 1), (31, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_79
  · decide +kernel

theorem prime_6338411 : Nat.Prime 6338411 := by
  apply nodeValid_prime [2, 5, 13, 48757] ⟨6338411, 7, [(2, 1), (5, 1), (13, 1), (48757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_48757
  · decide +kernel

theorem prime_7412791 : Nat.Prime 7412791 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 3209] ⟨7412791, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (3209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_3209
  · decide +kernel

theorem prime_13956577 : Nat.Prime 13956577 := by
  apply nodeValid_prime [2, 3, 145381] ⟨13956577, 7, [(2, 5), (3, 1), (145381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_145381
  · decide +kernel

theorem prime_15903443 : Nat.Prime 15903443 := by
  apply nodeValid_prime [2, 23, 345727] ⟨15903443, 2, [(2, 1), (23, 1), (345727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_345727
  · decide +kernel

theorem prime_20172263 : Nat.Prime 20172263 := by
  apply nodeValid_prime [2, 11, 19, 48259] ⟨20172263, 5, [(2, 1), (11, 1), (19, 1), (48259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_48259
  · decide +kernel

theorem prime_20189621 : Nat.Prime 20189621 := by
  apply nodeValid_prime [2, 5, 11, 91771] ⟨20189621, 2, [(2, 2), (5, 1), (11, 1), (91771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_91771
  · decide +kernel

theorem prime_20482223 : Nat.Prime 20482223 := by
  apply nodeValid_prime [2, 71, 144241] ⟨20482223, 5, [(2, 1), (71, 1), (144241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_144241
  · decide +kernel

theorem prime_20596123 : Nat.Prime 20596123 := by
  apply nodeValid_prime [2, 3, 101, 11329] ⟨20596123, 3, [(2, 1), (3, 2), (101, 1), (11329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_11329
  · decide +kernel

theorem prime_22082563 : Nat.Prime 22082563 := by
  apply nodeValid_prime [2, 3, 37, 71, 467] ⟨22082563, 2, [(2, 1), (3, 2), (37, 1), (71, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_467
  · decide +kernel

theorem prime_26488997 : Nat.Prime 26488997 := by
  apply nodeValid_prime [2, 1867, 3547] ⟨26488997, 2, [(2, 2), (1867, 1), (3547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1867
    · exact prime_3547
  · decide +kernel

theorem prime_26845033 : Nat.Prime 26845033 := by
  apply nodeValid_prime [2, 3, 149, 7507] ⟨26845033, 5, [(2, 3), (3, 1), (149, 1), (7507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_7507
  · decide +kernel

theorem prime_29468333 : Nat.Prime 29468333 := by
  apply nodeValid_prime [2, 431, 17093] ⟨29468333, 2, [(2, 2), (431, 1), (17093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_17093
  · decide +kernel

theorem prime_35628563 : Nat.Prime 35628563 := by
  apply nodeValid_prime [2, 199, 89519] ⟨35628563, 2, [(2, 1), (199, 1), (89519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_89519
  · decide +kernel

theorem prime_37622843 : Nat.Prime 37622843 := by
  apply nodeValid_prime [2, 47, 400243] ⟨37622843, 2, [(2, 1), (47, 1), (400243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_400243
  · decide +kernel

theorem prime_38954519 : Nat.Prime 38954519 := by
  apply nodeValid_prime [2, 257, 75787] ⟨38954519, 7, [(2, 1), (257, 1), (75787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_75787
  · decide +kernel

theorem prime_48471439 : Nat.Prime 48471439 := by
  apply nodeValid_prime [2, 3, 181, 44633] ⟨48471439, 6, [(2, 1), (3, 1), (181, 1), (44633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_44633
  · decide +kernel

theorem prime_49102583 : Nat.Prime 49102583 := by
  apply nodeValid_prime [2, 347, 70753] ⟨49102583, 5, [(2, 1), (347, 1), (70753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_70753
  · decide +kernel

theorem prime_57316057 : Nat.Prime 57316057 := by
  apply nodeValid_prime [2, 3, 7, 311, 1097] ⟨57316057, 5, [(2, 3), (3, 1), (7, 1), (311, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_311
    · exact prime_1097
  · decide +kernel

theorem prime_66231251 : Nat.Prime 66231251 := by
  apply nodeValid_prime [2, 5, 10597] ⟨66231251, 2, [(2, 1), (5, 5), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10597
  · decide +kernel

theorem prime_75626303 : Nat.Prime 75626303 := by
  apply nodeValid_prime [2, 17, 443, 5021] ⟨75626303, 5, [(2, 1), (17, 1), (443, 1), (5021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_443
    · exact prime_5021
  · decide +kernel

theorem prime_93798457 : Nat.Prime 93798457 := by
  apply nodeValid_prime [2, 3, 947, 4127] ⟨93798457, 15, [(2, 3), (3, 1), (947, 1), (4127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_947
    · exact prime_4127
  · decide +kernel

theorem prime_107785973 : Nat.Prime 107785973 := by
  apply nodeValid_prime [2, 7, 3849499] ⟨107785973, 2, [(2, 2), (7, 1), (3849499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3849499
  · decide +kernel

theorem prime_108848759 : Nat.Prime 108848759 := by
  apply nodeValid_prime [2, 19, 2864441] ⟨108848759, 13, [(2, 1), (19, 1), (2864441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2864441
  · decide +kernel

theorem prime_117782491 : Nat.Prime 117782491 := by
  apply nodeValid_prime [2, 3, 5, 7, 560869] ⟨117782491, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (560869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_560869
  · decide +kernel

theorem prime_229264229 : Nat.Prime 229264229 := by
  apply nodeValid_prime [2, 57316057] ⟨229264229, 2, [(2, 2), (57316057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57316057
  · decide +kernel

theorem prime_327624389 : Nat.Prime 327624389 := by
  apply nodeValid_prime [2, 7, 13, 71, 1811] ⟨327624389, 2, [(2, 2), (7, 2), (13, 1), (71, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_71
    · exact prime_1811
  · decide +kernel

theorem prime_491573353 : Nat.Prime 491573353 := by
  apply nodeValid_prime [2, 3, 20482223] ⟨491573353, 7, [(2, 3), (3, 1), (20482223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20482223
  · decide +kernel

theorem prime_1103514481 : Nat.Prime 1103514481 := by
  apply nodeValid_prime [2, 3, 5, 1532659] ⟨1103514481, 7, [(2, 4), (3, 2), (5, 1), (1532659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1532659
  · decide +kernel

theorem prime_1288605257 : Nat.Prime 1288605257 := by
  apply nodeValid_prime [2, 29, 5554333] ⟨1288605257, 3, [(2, 3), (29, 1), (5554333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_5554333
  · decide +kernel

theorem prime_1836202163 : Nat.Prime 1836202163 := by
  apply nodeValid_prime [2, 373, 2461397] ⟨1836202163, 2, [(2, 1), (373, 1), (2461397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_2461397
  · decide +kernel

theorem prime_1839363299 : Nat.Prime 1839363299 := by
  apply nodeValid_prime [2, 1753, 524633] ⟨1839363299, 2, [(2, 1), (1753, 1), (524633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1753
    · exact prime_524633
  · decide +kernel

theorem prime_2241513787 : Nat.Prime 2241513787 := by
  apply nodeValid_prime [2, 3, 4229, 88339] ⟨2241513787, 2, [(2, 1), (3, 1), (4229, 1), (88339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4229
    · exact prime_88339
  · decide +kernel

theorem prime_8966055149 : Nat.Prime 8966055149 := by
  apply nodeValid_prime [2, 2241513787] ⟨8966055149, 2, [(2, 2), (2241513787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2241513787
  · decide +kernel

theorem prime_10942661729 : Nat.Prime 10942661729 := by
  apply nodeValid_prime [2, 17, 31, 109, 5953] ⟨10942661729, 3, [(2, 5), (17, 1), (31, 1), (109, 1), (5953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_109
    · exact prime_5953
  · decide +kernel

theorem prime_14247785533 : Nat.Prime 14247785533 := by
  apply nodeValid_prime [2, 3, 13049, 90989] ⟨14247785533, 6, [(2, 2), (3, 1), (13049, 1), (90989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13049
    · exact prime_90989
  · decide +kernel

theorem prime_16383467897 : Nat.Prime 16383467897 := by
  apply nodeValid_prime [2, 19, 107785973] ⟨16383467897, 3, [(2, 3), (19, 1), (107785973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_107785973
  · decide +kernel

theorem prime_23583897247 : Nat.Prime 23583897247 := by
  apply nodeValid_prime [2, 3, 7, 13, 41, 1053511] ⟨23583897247, 5, [(2, 1), (3, 1), (7, 1), (13, 1), (41, 1), (1053511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_41
    · exact prime_1053511
  · decide +kernel

theorem prime_34831832351 : Nat.Prime 34831832351 := by
  apply nodeValid_prime [2, 5, 7, 131, 759691] ⟨34831832351, 14, [(2, 1), (5, 2), (7, 1), (131, 1), (759691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_131
    · exact prime_759691
  · decide +kernel

theorem prime_69303525497 : Nat.Prime 69303525497 := by
  apply nodeValid_prime [2, 8387, 1032901] ⟨69303525497, 3, [(2, 3), (8387, 1), (1032901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8387
    · exact prime_1032901
  · decide +kernel

theorem prime_71728441193 : Nat.Prime 71728441193 := by
  apply nodeValid_prime [2, 8966055149] ⟨71728441193, 3, [(2, 3), (8966055149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8966055149
  · decide +kernel

theorem prime_104856698899 : Nat.Prime 104856698899 := by
  apply nodeValid_prime [2, 3, 7, 31, 26845033] ⟨104856698899, 2, [(2, 1), (3, 2), (7, 1), (31, 1), (26845033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_26845033
  · decide +kernel

theorem prime_212255075141 : Nat.Prime 212255075141 := by
  apply nodeValid_prime [2, 5, 9461, 1121737] ⟨212255075141, 2, [(2, 2), (5, 1), (9461, 1), (1121737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9461
    · exact prime_1121737
  · decide +kernel

theorem prime_214083284039 : Nat.Prime 214083284039 := by
  apply nodeValid_prime [2, 13, 53, 4391, 35381] ⟨214083284039, 7, [(2, 1), (13, 1), (53, 1), (4391, 1), (35381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_4391
    · exact prime_35381
  · decide +kernel

theorem prime_412951754609 : Nat.Prime 412951754609 := by
  apply nodeValid_prime [2, 67, 103, 137, 27299] ⟨412951754609, 3, [(2, 4), (67, 1), (103, 1), (137, 1), (27299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_103
    · exact prime_137
    · exact prime_27299
  · decide +kernel

theorem prime_412951761029 : Nat.Prime 412951761029 := by
  apply nodeValid_prime [2, 19, 733, 7412791] ⟨412951761029, 2, [(2, 2), (19, 1), (733, 1), (7412791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_733
    · exact prime_7412791
  · decide +kernel

theorem prime_412951761487 : Nat.Prime 412951761487 := by
  apply nodeValid_prime [2, 3, 11, 8167, 255371] ⟨412951761487, 3, [(2, 1), (3, 2), (11, 1), (8167, 1), (255371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_8167
    · exact prime_255371
  · decide +kernel

theorem prime_413667812017 : Nat.Prime 413667812017 := by
  apply nodeValid_prime [2, 3, 67, 89, 481753] ⟨413667812017, 5, [(2, 4), (3, 2), (67, 1), (89, 1), (481753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_89
    · exact prime_481753
  · decide +kernel

theorem prime_413667812141 : Nat.Prime 413667812141 := by
  apply nodeValid_prime [2, 5, 11, 97, 229, 84649] ⟨413667812141, 3, [(2, 2), (5, 1), (11, 1), (97, 1), (229, 1), (84649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_97
    · exact prime_229
    · exact prime_84649
  · decide +kernel

theorem prime_413667842267 : Nat.Prime 413667842267 := by
  apply nodeValid_prime [2, 7, 29, 4049, 251639] ⟨413667842267, 5, [(2, 1), (7, 1), (29, 1), (4049, 1), (251639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_4049
    · exact prime_251639
  · decide +kernel

theorem prime_414384772561 : Nat.Prime 414384772561 := by
  apply nodeValid_prime [2, 3, 5, 11, 3889, 40361] ⟨414384772561, 13, [(2, 4), (3, 1), (5, 1), (11, 1), (3889, 1), (40361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_3889
    · exact prime_40361
  · decide +kernel

theorem prime_414384824041 : Nat.Prime 414384824041 := by
  apply nodeValid_prime [2, 3, 5, 11, 23, 67, 101, 2017] ⟨414384824041, 21, [(2, 3), (3, 1), (5, 1), (11, 1), (23, 1), (67, 1), (101, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_67
    · exact prime_101
    · exact prime_2017
  · decide +kernel

theorem prime_414384824767 : Nat.Prime 414384824767 := by
  apply nodeValid_prime [2, 3, 11, 1801, 3486151] ⟨414384824767, 3, [(2, 1), (3, 1), (11, 1), (1801, 1), (3486151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1801
    · exact prime_3486151
  · decide +kernel

theorem prime_415102536391 : Nat.Prime 415102536391 := by
  apply nodeValid_prime [2, 3, 5, 37, 59, 6338411] ⟨415102536391, 3, [(2, 1), (3, 1), (5, 1), (37, 1), (59, 1), (6338411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_59
    · exact prime_6338411
  · decide +kernel

theorem prime_415102538107 : Nat.Prime 415102538107 := by
  apply nodeValid_prime [2, 3, 11447, 671537] ⟨415102538107, 2, [(2, 1), (3, 3), (11447, 1), (671537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11447
    · exact prime_671537
  · decide +kernel

theorem prime_415102539853 : Nat.Prime 415102539853 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 113, 101939] ⟨415102539853, 14, [(2, 2), (3, 2), (7, 1), (11, 1), (13, 1), (113, 1), (101939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_113
    · exact prime_101939
  · decide +kernel

theorem prime_415821145703 : Nat.Prime 415821145703 := by
  apply nodeValid_prime [2, 19, 10942661729] ⟨415821145703, 10, [(2, 1), (19, 1), (10942661729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_10942661729
  · decide +kernel

theorem prime_415821152779 : Nat.Prime 415821152779 := by
  apply nodeValid_prime [2, 3, 44711, 1550033] ⟨415821152779, 2, [(2, 1), (3, 1), (44711, 1), (1550033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44711
    · exact prime_1550033
  · decide +kernel

theorem prime_415821152983 : Nat.Prime 415821152983 := by
  apply nodeValid_prime [2, 3, 69303525497] ⟨415821152983, 6, [(2, 1), (3, 1), (69303525497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_69303525497
  · decide +kernel

theorem prime_416540592557 : Nat.Prime 416540592557 := by
  apply nodeValid_prime [2, 11, 9733, 88423] ⟨416540592557, 2, [(2, 2), (11, 2), (9733, 1), (88423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9733
    · exact prime_88423
  · decide +kernel

theorem prime_416540623663 : Nat.Prime 416540623663 := by
  apply nodeValid_prime [2, 3, 68819, 112087] ⟨416540623663, 5, [(2, 1), (3, 3), (68819, 1), (112087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_68819
    · exact prime_112087
  · decide +kernel

theorem prime_416540624251 : Nat.Prime 416540624251 := by
  apply nodeValid_prime [2, 3, 5, 19, 499, 58579] ⟨416540624251, 3, [(2, 1), (3, 1), (5, 3), (19, 1), (499, 1), (58579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_499
    · exact prime_58579
  · decide +kernel

theorem prime_417260879551 : Nat.Prime 417260879551 := by
  apply nodeValid_prime [2, 3, 5, 8803, 35111] ⟨417260879551, 6, [(2, 1), (3, 3), (5, 2), (8803, 1), (35111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8803
    · exact prime_35111
  · decide +kernel

theorem prime_417260896781 : Nat.Prime 417260896781 := by
  apply nodeValid_prime [2, 5, 7, 13, 229264229] ⟨417260896781, 2, [(2, 2), (5, 1), (7, 1), (13, 1), (229264229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_229264229
  · decide +kernel

theorem prime_417260897191 : Nat.Prime 417260897191 := by
  apply nodeValid_prime [2, 3, 5, 25763, 179957] ⟨417260897191, 3, [(2, 1), (3, 2), (5, 1), (25763, 1), (179957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_25763
    · exact prime_179957
  · decide +kernel

theorem prime_417981988213 : Nat.Prime 417981988213 := by
  apply nodeValid_prime [2, 3, 34831832351] ⟨417981988213, 6, [(2, 2), (3, 1), (34831832351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34831832351
  · decide +kernel

theorem prime_417981988871 : Nat.Prime 417981988871 := by
  apply nodeValid_prime [2, 5, 29, 37, 38954519] ⟨417981988871, 13, [(2, 1), (5, 1), (29, 1), (37, 1), (38954519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_37
    · exact prime_38954519
  · decide +kernel

theorem prime_417982004203 : Nat.Prime 417982004203 := by
  apply nodeValid_prime [2, 3, 7, 281, 3593, 9857] ⟨417982004203, 3, [(2, 1), (3, 1), (7, 1), (281, 1), (3593, 1), (9857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_281
    · exact prime_3593
    · exact prime_9857
  · decide +kernel

theorem prime_418703960471 : Nat.Prime 418703960471 := by
  apply nodeValid_prime [2, 5, 31, 7333, 184189] ⟨418703960471, 11, [(2, 1), (5, 1), (31, 1), (7333, 1), (184189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_7333
    · exact prime_184189
  · decide +kernel

theorem prime_418703960929 : Nat.Prime 418703960929 := by
  apply nodeValid_prime [2, 3, 11, 1709, 232007] ⟨418703960929, 13, [(2, 5), (3, 1), (11, 1), (1709, 1), (232007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1709
    · exact prime_232007
  · decide +kernel

theorem prime_418703969143 : Nat.Prime 418703969143 := by
  apply nodeValid_prime [2, 3, 71, 327624389] ⟨418703969143, 3, [(2, 1), (3, 2), (71, 1), (327624389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_327624389
  · decide +kernel

theorem prime_419426778499 : Nat.Prime 419426778499 := by
  apply nodeValid_prime [2, 3, 7, 13, 29, 26488997] ⟨419426778499, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (29, 1), (26488997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_26488997
  · decide +kernel

theorem prime_419426795573 : Nat.Prime 419426795573 := by
  apply nodeValid_prime [2, 53, 839, 1327, 1777] ⟨419426795573, 2, [(2, 2), (53, 1), (839, 1), (1327, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_839
    · exact prime_1327
    · exact prime_1777
  · decide +kernel

theorem prime_419426795597 : Nat.Prime 419426795597 := by
  apply nodeValid_prime [2, 104856698899] ⟨419426795597, 2, [(2, 2), (104856698899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_104856698899
  · decide +kernel

theorem prime_420150432257 : Nat.Prime 420150432257 := by
  apply nodeValid_prime [2, 37, 2087, 10627] ⟨420150432257, 3, [(2, 9), (37, 1), (2087, 1), (10627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2087
    · exact prime_10627
  · decide +kernel

theorem prime_420150433007 : Nat.Prime 420150433007 := by
  apply nodeValid_prime [2, 443, 821, 577601] ⟨420150433007, 5, [(2, 1), (443, 1), (821, 1), (577601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_821
    · exact prime_577601
  · decide +kernel

theorem prime_420150433253 : Nat.Prime 420150433253 := by
  apply nodeValid_prime [2, 11, 197, 48471439] ⟨420150433253, 2, [(2, 2), (11, 1), (197, 1), (48471439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_197
    · exact prime_48471439
  · decide +kernel

theorem prime_420874938397 : Nat.Prime 420874938397 := by
  apply nodeValid_prime [2, 3, 11, 31, 3116761] ⟨420874938397, 2, [(2, 2), (3, 2), (11, 2), (31, 1), (3116761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_3116761
  · decide +kernel

theorem prime_420874957387 : Nat.Prime 420874957387 := by
  apply nodeValid_prime [2, 3, 13, 59, 101, 301831] ⟨420874957387, 3, [(2, 1), (3, 2), (13, 1), (59, 1), (101, 1), (301831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_101
    · exact prime_301831
  · decide +kernel

theorem prime_420874957753 : Nat.Prime 420874957753 := by
  apply nodeValid_prime [2, 3, 17, 41, 173, 145433] ⟨420874957753, 5, [(2, 3), (3, 1), (17, 1), (41, 1), (173, 1), (145433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_173
    · exact prime_145433
  · decide +kernel

theorem prime_421600273931 : Nat.Prime 421600273931 := by
  apply nodeValid_prime [2, 5, 11, 241, 15903443] ⟨421600273931, 2, [(2, 1), (5, 1), (11, 1), (241, 1), (15903443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_241
    · exact prime_15903443
  · decide +kernel

theorem prime_421600278017 : Nat.Prime 421600278017 := by
  apply nodeValid_prime [2, 59, 13956577] ⟨421600278017, 3, [(2, 9), (59, 1), (13956577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_13956577
  · decide +kernel

theorem prime_421600292797 : Nat.Prime 421600292797 := by
  apply nodeValid_prime [2, 3, 37, 43, 22082563] ⟨421600292797, 5, [(2, 2), (3, 1), (37, 1), (43, 1), (22082563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_43
    · exact prime_22082563
  · decide +kernel

theorem prime_422326492079 : Nat.Prime 422326492079 := by
  apply nodeValid_prime [2, 10459, 20189621] ⟨422326492079, 7, [(2, 1), (10459, 1), (20189621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10459
    · exact prime_20189621
  · decide +kernel

theorem prime_422326497491 : Nat.Prime 422326497491 := by
  apply nodeValid_prime [2, 5, 23, 1836202163] ⟨422326497491, 2, [(2, 1), (5, 1), (23, 1), (1836202163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1836202163
  · decide +kernel

theorem prime_422326498169 : Nat.Prime 422326498169 := by
  apply nodeValid_prime [2, 2617, 20172263] ⟨422326498169, 3, [(2, 3), (2617, 1), (20172263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2617
    · exact prime_20172263
  · decide +kernel

theorem prime_423053538983 : Nat.Prime 423053538983 := by
  apply nodeValid_prime [2, 2797, 75626303] ⟨423053538983, 5, [(2, 1), (2797, 1), (75626303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2797
    · exact prime_75626303
  · decide +kernel

theorem prime_423053557063 : Nat.Prime 423053557063 := by
  apply nodeValid_prime [2, 3, 1979, 35628563] ⟨423053557063, 3, [(2, 1), (3, 1), (1979, 1), (35628563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1979
    · exact prime_35628563
  · decide +kernel

theorem prime_423053558771 : Nat.Prime 423053558771 := by
  apply nodeValid_prime [2, 5, 23, 1839363299] ⟨423053558771, 2, [(2, 1), (5, 1), (23, 1), (1839363299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1839363299
  · decide +kernel

theorem prime_423781402217 : Nat.Prime 423781402217 := by
  apply nodeValid_prime [2, 131, 2069, 195443] ⟨423781402217, 3, [(2, 3), (131, 1), (2069, 1), (195443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_2069
    · exact prime_195443
  · decide +kernel

theorem prime_423781402619 : Nat.Prime 423781402619 := by
  apply nodeValid_prime [2, 7, 257, 117782491] ⟨423781402619, 6, [(2, 1), (7, 1), (257, 1), (117782491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_257
    · exact prime_117782491
  · decide +kernel

theorem prime_423781428727 : Nat.Prime 423781428727 := by
  apply nodeValid_prime [2, 3, 251, 93798457] ⟨423781428727, 3, [(2, 1), (3, 2), (251, 1), (93798457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_93798457
  · decide +kernel

theorem prime_424510150283 : Nat.Prime 424510150283 := by
  apply nodeValid_prime [2, 212255075141] ⟨424510150283, 2, [(2, 1), (212255075141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_212255075141
  · decide +kernel

theorem prime_424510150447 : Nat.Prime 424510150447 := by
  apply nodeValid_prime [2, 3, 23583897247] ⟨424510150447, 3, [(2, 1), (3, 2), (23583897247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23583897247
  · decide +kernel

theorem prime_424510160101 : Nat.Prime 424510160101 := by
  apply nodeValid_prime [2, 3, 5, 13, 108848759] ⟨424510160101, 2, [(2, 2), (3, 1), (5, 2), (13, 1), (108848759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_108848759
  · decide +kernel

theorem prime_425239734427 : Nat.Prime 425239734427 := by
  apply nodeValid_prime [2, 3, 13, 19, 1009, 284377] ⟨425239734427, 2, [(2, 1), (3, 1), (13, 1), (19, 1), (1009, 1), (284377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_1009
    · exact prime_284377
  · decide +kernel

theorem prime_425239734811 : Nat.Prime 425239734811 := by
  apply nodeValid_prime [2, 3, 5, 11, 1288605257] ⟨425239734811, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (1288605257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1288605257
  · decide +kernel

theorem prime_425239736759 : Nat.Prime 425239736759 := by
  apply nodeValid_prime [2, 787, 953, 283489] ⟨425239736759, 13, [(2, 1), (787, 1), (953, 1), (283489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_787
    · exact prime_953
    · exact prime_283489
  · decide +kernel

theorem prime_425970156511 : Nat.Prime 425970156511 := by
  apply nodeValid_prime [2, 3, 5, 17, 67, 4155401] ⟨425970156511, 7, [(2, 1), (3, 2), (5, 1), (17, 1), (67, 1), (4155401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_67
    · exact prime_4155401
  · decide +kernel

theorem prime_425970156683 : Nat.Prime 425970156683 := by
  apply nodeValid_prime [2, 7, 27847, 1092629] ⟨425970156683, 2, [(2, 1), (7, 1), (27847, 1), (1092629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_27847
    · exact prime_1092629
  · decide +kernel

theorem prime_425970165323 : Nat.Prime 425970165323 := by
  apply nodeValid_prime [2, 13, 16383467897] ⟨425970165323, 2, [(2, 1), (13, 1), (16383467897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_16383467897
  · decide +kernel

theorem prime_426701446271 : Nat.Prime 426701446271 := by
  apply nodeValid_prime [2, 5, 11, 79, 49102583] ⟨426701446271, 7, [(2, 1), (5, 1), (11, 1), (79, 1), (49102583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_79
    · exact prime_49102583
  · decide +kernel

theorem prime_426701461841 : Nat.Prime 426701461841 := by
  apply nodeValid_prime [2, 5, 181, 29468333] ⟨426701461841, 3, [(2, 4), (5, 1), (181, 1), (29468333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_181
    · exact prime_29468333
  · decide +kernel

theorem prime_426701465273 : Nat.Prime 426701465273 := by
  apply nodeValid_prime [2, 52517, 1015627] ⟨426701465273, 3, [(2, 3), (52517, 1), (1015627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_52517
    · exact prime_1015627
  · decide +kernel

theorem prime_427433565991 : Nat.Prime 427433565991 := by
  apply nodeValid_prime [2, 3, 5, 14247785533] ⟨427433565991, 6, [(2, 1), (3, 1), (5, 1), (14247785533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14247785533
  · decide +kernel

theorem prime_427433566697 : Nat.Prime 427433566697 := by
  apply nodeValid_prime [2, 212141, 251857] ⟨427433566697, 3, [(2, 3), (212141, 1), (251857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_212141
    · exact prime_251857
  · decide +kernel

theorem prime_427433580127 : Nat.Prime 427433580127 := by
  apply nodeValid_prime [2, 3, 7, 1949, 580183] ⟨427433580127, 5, [(2, 1), (3, 3), (7, 1), (1949, 1), (580183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1949
    · exact prime_580183
  · decide +kernel

theorem prime_428166557681 : Nat.Prime 428166557681 := by
  apply nodeValid_prime [2, 5, 617, 1283, 6761] ⟨428166557681, 3, [(2, 4), (5, 1), (617, 1), (1283, 1), (6761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_617
    · exact prime_1283
    · exact prime_6761
  · decide +kernel

theorem prime_428166557993 : Nat.Prime 428166557993 := by
  apply nodeValid_prime [2, 23, 79, 113, 463, 563] ⟨428166557993, 3, [(2, 3), (23, 1), (79, 1), (113, 1), (463, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_79
    · exact prime_113
    · exact prime_463
    · exact prime_563
  · decide +kernel

theorem prime_428166568079 : Nat.Prime 428166568079 := by
  apply nodeValid_prime [2, 214083284039] ⟨428166568079, 19, [(2, 1), (214083284039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_214083284039
  · decide +kernel

theorem prime_428900410201 : Nat.Prime 428900410201 := by
  apply nodeValid_prime [2, 3, 5, 19, 37622843] ⟨428900410201, 29, [(2, 3), (3, 1), (5, 2), (19, 1), (37622843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_37622843
  · decide +kernel

theorem prime_428900418833 : Nat.Prime 428900418833 := by
  apply nodeValid_prime [2, 20369, 1316033] ⟨428900418833, 3, [(2, 4), (20369, 1), (1316033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_20369
    · exact prime_1316033
  · decide +kernel

theorem prime_428900419999 : Nat.Prime 428900419999 := by
  apply nodeValid_prime [2, 3, 14143, 1684777] ⟨428900419999, 6, [(2, 1), (3, 2), (14143, 1), (1684777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14143
    · exact prime_1684777
  · decide +kernel

theorem prime_429635110523 : Nat.Prime 429635110523 := by
  apply nodeValid_prime [2, 19, 23, 491573353] ⟨429635110523, 2, [(2, 1), (19, 1), (23, 1), (491573353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_491573353
  · decide +kernel

theorem prime_429635124371 : Nat.Prime 429635124371 := by
  apply nodeValid_prime [2, 5, 170633, 251789] ⟨429635124371, 2, [(2, 1), (5, 1), (170633, 1), (251789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_170633
    · exact prime_251789
  · decide +kernel

theorem prime_429635125781 : Nat.Prime 429635125781 := by
  apply nodeValid_prime [2, 5, 7, 149, 20596123] ⟨429635125781, 2, [(2, 2), (5, 1), (7, 1), (149, 1), (20596123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_149
    · exact prime_20596123
  · decide +kernel

theorem prime_430370647159 : Nat.Prime 430370647159 := by
  apply nodeValid_prime [2, 3, 71728441193] ⟨430370647159, 3, [(2, 1), (3, 1), (71728441193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71728441193
  · decide +kernel

theorem prime_430370647591 : Nat.Prime 430370647591 := by
  apply nodeValid_prime [2, 3, 5, 13, 1103514481] ⟨430370647591, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (1103514481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1103514481
  · decide +kernel

theorem prime_430370668999 : Nat.Prime 430370668999 := by
  apply nodeValid_prime [2, 3, 19, 66231251] ⟨430370668999, 3, [(2, 1), (3, 2), (19, 2), (66231251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_66231251
  · decide +kernel

end Sude.Lucas.Generated
