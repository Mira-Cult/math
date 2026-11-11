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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0116

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_14081 : Nat.Prime 14081 := by
  apply nodeValid_prime [2, 5, 11] ⟨14081, 3, [(2, 8), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_19121 : Nat.Prime 19121 := by
  apply nodeValid_prime [2, 5, 239] ⟨19121, 6, [(2, 4), (5, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
  · decide +kernel

theorem prime_24799 : Nat.Prime 24799 := by
  apply nodeValid_prime [2, 3, 4133] ⟨24799, 6, [(2, 1), (3, 1), (4133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4133
  · decide +kernel

theorem prime_28163 : Nat.Prime 28163 := by
  apply nodeValid_prime [2, 14081] ⟨28163, 2, [(2, 1), (14081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14081
  · decide +kernel

theorem prime_28579 : Nat.Prime 28579 := by
  apply nodeValid_prime [2, 3, 11, 433] ⟨28579, 2, [(2, 1), (3, 1), (11, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_433
  · decide +kernel

theorem prime_29383 : Nat.Prime 29383 := by
  apply nodeValid_prime [2, 3, 59, 83] ⟨29383, 6, [(2, 1), (3, 1), (59, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_83
  · decide +kernel

theorem prime_30491 : Nat.Prime 30491 := by
  apply nodeValid_prime [2, 5, 3049] ⟨30491, 2, [(2, 1), (5, 1), (3049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3049
  · decide +kernel

theorem prime_32749 : Nat.Prime 32749 := by
  apply nodeValid_prime [2, 3, 2729] ⟨32749, 2, [(2, 2), (3, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2729
  · decide +kernel

theorem prime_41051 : Nat.Prime 41051 := by
  apply nodeValid_prime [2, 5, 821] ⟨41051, 2, [(2, 1), (5, 2), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_821
  · decide +kernel

theorem prime_44041 : Nat.Prime 44041 := by
  apply nodeValid_prime [2, 3, 5, 367] ⟨44041, 11, [(2, 3), (3, 1), (5, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_367
  · decide +kernel

theorem prime_46649 : Nat.Prime 46649 := by
  apply nodeValid_prime [2, 7, 17] ⟨46649, 15, [(2, 3), (7, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_50503 : Nat.Prime 50503 := by
  apply nodeValid_prime [2, 3, 19, 443] ⟨50503, 5, [(2, 1), (3, 1), (19, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_443
  · decide +kernel

theorem prime_50599 : Nat.Prime 50599 := by
  apply nodeValid_prime [2, 3, 937] ⟨50599, 3, [(2, 1), (3, 3), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_937
  · decide +kernel

theorem prime_54469 : Nat.Prime 54469 := by
  apply nodeValid_prime [2, 3, 17, 89] ⟨54469, 2, [(2, 2), (3, 2), (17, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_89
  · decide +kernel

theorem prime_70571 : Nat.Prime 70571 := by
  apply nodeValid_prime [2, 5, 7057] ⟨70571, 2, [(2, 1), (5, 1), (7057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7057
  · decide +kernel

theorem prime_80933 : Nat.Prime 80933 := by
  apply nodeValid_prime [2, 20233] ⟨80933, 2, [(2, 2), (20233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20233
  · decide +kernel

theorem prime_93997 : Nat.Prime 93997 := by
  apply nodeValid_prime [2, 3, 7, 373] ⟨93997, 11, [(2, 2), (3, 2), (7, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_373
  · decide +kernel

theorem prime_103841 : Nat.Prime 103841 := by
  apply nodeValid_prime [2, 5, 11, 59] ⟨103841, 3, [(2, 5), (5, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_104729 : Nat.Prime 104729 := by
  apply nodeValid_prime [2, 13, 19, 53] ⟨104729, 12, [(2, 3), (13, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_105683 : Nat.Prime 105683 := by
  apply nodeValid_prime [2, 53, 997] ⟨105683, 2, [(2, 1), (53, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_997
  · decide +kernel

theorem prime_113777 : Nat.Prime 113777 := by
  apply nodeValid_prime [2, 13, 547] ⟨113777, 3, [(2, 4), (13, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_547
  · decide +kernel

theorem prime_116537 : Nat.Prime 116537 := by
  apply nodeValid_prime [2, 7, 2081] ⟨116537, 3, [(2, 3), (7, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2081
  · decide +kernel

theorem prime_130811 : Nat.Prime 130811 := by
  apply nodeValid_prime [2, 5, 103, 127] ⟨130811, 6, [(2, 1), (5, 1), (103, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_127
  · decide +kernel

theorem prime_134047 : Nat.Prime 134047 := by
  apply nodeValid_prime [2, 3, 11, 677] ⟨134047, 6, [(2, 1), (3, 2), (11, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_677
  · decide +kernel

theorem prime_151253 : Nat.Prime 151253 := by
  apply nodeValid_prime [2, 37813] ⟨151253, 2, [(2, 2), (37813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37813
  · decide +kernel

theorem prime_174467 : Nat.Prime 174467 := by
  apply nodeValid_prime [2, 83, 1051] ⟨174467, 2, [(2, 1), (83, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_1051
  · decide +kernel

theorem prime_175129 : Nat.Prime 175129 := by
  apply nodeValid_prime [2, 3, 7297] ⟨175129, 7, [(2, 3), (3, 1), (7297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7297
  · decide +kernel

theorem prime_176977 : Nat.Prime 176977 := by
  apply nodeValid_prime [2, 3, 1229] ⟨176977, 7, [(2, 4), (3, 2), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1229
  · decide +kernel

theorem prime_202327 : Nat.Prime 202327 := by
  apply nodeValid_prime [2, 3, 33721] ⟨202327, 3, [(2, 1), (3, 1), (33721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33721
  · decide +kernel

theorem prime_203569 : Nat.Prime 203569 := by
  apply nodeValid_prime [2, 3, 4241] ⟨203569, 17, [(2, 4), (3, 1), (4241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4241
  · decide +kernel

theorem prime_231799 : Nat.Prime 231799 := by
  apply nodeValid_prime [2, 3, 7, 5519] ⟨231799, 3, [(2, 1), (3, 1), (7, 1), (5519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5519
  · decide +kernel

theorem prime_286043 : Nat.Prime 286043 := by
  apply nodeValid_prime [2, 17, 47, 179] ⟨286043, 2, [(2, 1), (17, 1), (47, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_179
  · decide +kernel

theorem prime_302801 : Nat.Prime 302801 := by
  apply nodeValid_prime [2, 5, 757] ⟨302801, 6, [(2, 4), (5, 2), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_757
  · decide +kernel

theorem prime_310489 : Nat.Prime 310489 := by
  apply nodeValid_prime [2, 3, 17, 761] ⟨310489, 19, [(2, 3), (3, 1), (17, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_761
  · decide +kernel

theorem prime_328897 : Nat.Prime 328897 := by
  apply nodeValid_prime [2, 3, 571] ⟨328897, 10, [(2, 6), (3, 2), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
  · decide +kernel

theorem prime_349667 : Nat.Prime 349667 := by
  apply nodeValid_prime [2, 359, 487] ⟨349667, 2, [(2, 1), (359, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_487
  · decide +kernel

theorem prime_423427 : Nat.Prime 423427 := by
  apply nodeValid_prime [2, 3, 70571] ⟨423427, 5, [(2, 1), (3, 1), (70571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_70571
  · decide +kernel

theorem prime_459089 : Nat.Prime 459089 := by
  apply nodeValid_prime [2, 7, 4099] ⟨459089, 3, [(2, 4), (7, 1), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4099
  · decide +kernel

theorem prime_497677 : Nat.Prime 497677 := by
  apply nodeValid_prime [2, 3, 67, 619] ⟨497677, 2, [(2, 2), (3, 1), (67, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_619
  · decide +kernel

theorem prime_572087 : Nat.Prime 572087 := by
  apply nodeValid_prime [2, 286043] ⟨572087, 5, [(2, 1), (286043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_286043
  · decide +kernel

theorem prime_599477 : Nat.Prime 599477 := by
  apply nodeValid_prime [2, 73, 2053] ⟨599477, 2, [(2, 2), (73, 1), (2053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_2053
  · decide +kernel

theorem prime_609821 : Nat.Prime 609821 := by
  apply nodeValid_prime [2, 5, 30491] ⟨609821, 2, [(2, 2), (5, 1), (30491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30491
  · decide +kernel

theorem prime_619471 : Nat.Prime 619471 := by
  apply nodeValid_prime [2, 3, 5, 6883] ⟨619471, 6, [(2, 1), (3, 2), (5, 1), (6883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6883
  · decide +kernel

theorem prime_797201 : Nat.Prime 797201 := by
  apply nodeValid_prime [2, 5, 1993] ⟨797201, 3, [(2, 4), (5, 2), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1993
  · decide +kernel

theorem prime_804283 : Nat.Prime 804283 := by
  apply nodeValid_prime [2, 3, 134047] ⟨804283, 2, [(2, 1), (3, 1), (134047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_134047
  · decide +kernel

theorem prime_858251 : Nat.Prime 858251 := by
  apply nodeValid_prime [2, 5, 3433] ⟨858251, 2, [(2, 1), (5, 3), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3433
  · decide +kernel

theorem prime_1015919 : Nat.Prime 1015919 := by
  apply nodeValid_prime [2, 43, 11813] ⟨1015919, 7, [(2, 1), (43, 1), (11813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_11813
  · decide +kernel

theorem prime_1031729 : Nat.Prime 1031729 := by
  apply nodeValid_prime [2, 64483] ⟨1031729, 3, [(2, 4), (64483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_64483
  · decide +kernel

theorem prime_1108817 : Nat.Prime 1108817 := by
  apply nodeValid_prime [2, 37, 1873] ⟨1108817, 3, [(2, 4), (37, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1873
  · decide +kernel

theorem prime_1194023 : Nat.Prime 1194023 := by
  apply nodeValid_prime [2, 23, 101, 257] ⟨1194023, 5, [(2, 1), (23, 1), (101, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_101
    · exact prime_257
  · decide +kernel

theorem prime_1328711 : Nat.Prime 1328711 := by
  apply nodeValid_prime [2, 5, 23, 53, 109] ⟨1328711, 23, [(2, 1), (5, 1), (23, 1), (53, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_53
    · exact prime_109
  · decide +kernel

theorem prime_1425863 : Nat.Prime 1425863 := by
  apply nodeValid_prime [2, 23, 139, 223] ⟨1425863, 5, [(2, 1), (23, 1), (139, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_139
    · exact prime_223
  · decide +kernel

theorem prime_1535689 : Nat.Prime 1535689 := by
  apply nodeValid_prime [2, 3, 7, 11, 277] ⟨1535689, 19, [(2, 3), (3, 2), (7, 1), (11, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_277
  · decide +kernel

theorem prime_1748491 : Nat.Prime 1748491 := by
  apply nodeValid_prime [2, 3, 5, 167, 349] ⟨1748491, 3, [(2, 1), (3, 1), (5, 1), (167, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_349
  · decide +kernel

theorem prime_1893937 : Nat.Prime 1893937 := by
  apply nodeValid_prime [2, 3, 11, 17, 211] ⟨1893937, 5, [(2, 4), (3, 1), (11, 1), (17, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_211
  · decide +kernel

theorem prime_1914197 : Nat.Prime 1914197 := by
  apply nodeValid_prime [2, 59, 8111] ⟨1914197, 2, [(2, 2), (59, 1), (8111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_8111
  · decide +kernel

theorem prime_2063459 : Nat.Prime 2063459 := by
  apply nodeValid_prime [2, 1031729] ⟨2063459, 2, [(2, 1), (1031729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1031729
  · decide +kernel

theorem prime_2200043 : Nat.Prime 2200043 := by
  apply nodeValid_prime [2, 13, 23, 283] ⟨2200043, 2, [(2, 1), (13, 2), (23, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_283
  · decide +kernel

theorem prime_2851727 : Nat.Prime 2851727 := by
  apply nodeValid_prime [2, 1425863] ⟨2851727, 5, [(2, 1), (1425863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1425863
  · decide +kernel

theorem prime_3432523 : Nat.Prime 3432523 := by
  apply nodeValid_prime [2, 3, 572087] ⟨3432523, 3, [(2, 1), (3, 1), (572087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_572087
  · decide +kernel

theorem prime_3716827 : Nat.Prime 3716827 := by
  apply nodeValid_prime [2, 3, 619471] ⟨3716827, 2, [(2, 1), (3, 1), (619471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619471
  · decide +kernel

theorem prime_3806683 : Nat.Prime 3806683 := by
  apply nodeValid_prime [2, 3, 11, 137, 421] ⟨3806683, 2, [(2, 1), (3, 1), (11, 1), (137, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
    · exact prime_421
  · decide +kernel

theorem prime_4234271 : Nat.Prime 4234271 := by
  apply nodeValid_prime [2, 5, 423427] ⟨4234271, 13, [(2, 1), (5, 1), (423427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_423427
  · decide +kernel

theorem prime_4588889 : Nat.Prime 4588889 := by
  apply nodeValid_prime [2, 37, 419] ⟨4588889, 3, [(2, 3), (37, 2), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_419
  · decide +kernel

theorem prime_7164139 : Nat.Prime 7164139 := by
  apply nodeValid_prime [2, 3, 1194023] ⟨7164139, 2, [(2, 1), (3, 1), (1194023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1194023
  · decide +kernel

theorem prime_8315789 : Nat.Prime 8315789 := by
  apply nodeValid_prime [2, 13, 17, 23, 409] ⟨8315789, 2, [(2, 2), (13, 1), (17, 1), (23, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_23
    · exact prime_409
  · decide +kernel

theorem prime_8456507 : Nat.Prime 8456507 := by
  apply nodeValid_prime [2, 103, 41051] ⟨8456507, 2, [(2, 1), (103, 1), (41051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_41051
  · decide +kernel

theorem prime_9735559 : Nat.Prime 9735559 := by
  apply nodeValid_prime [2, 3, 7, 231799] ⟨9735559, 3, [(2, 1), (3, 1), (7, 1), (231799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_231799
  · decide +kernel

theorem prime_11940583 : Nat.Prime 11940583 := by
  apply nodeValid_prime [2, 3, 53, 37549] ⟨11940583, 3, [(2, 1), (3, 1), (53, 1), (37549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_37549
  · decide +kernel

theorem prime_13200259 : Nat.Prime 13200259 := by
  apply nodeValid_prime [2, 3, 2200043] ⟨13200259, 2, [(2, 1), (3, 1), (2200043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2200043
  · decide +kernel

theorem prime_16333633 : Nat.Prime 16333633 := by
  apply nodeValid_prime [2, 3, 7, 4051] ⟨16333633, 10, [(2, 6), (3, 2), (7, 1), (4051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4051
  · decide +kernel

theorem prime_18412847 : Nat.Prime 18412847 := by
  apply nodeValid_prime [2, 79, 116537] ⟨18412847, 5, [(2, 1), (79, 1), (116537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_116537
  · decide +kernel

theorem prime_22297739 : Nat.Prime 22297739 := by
  apply nodeValid_prime [2, 1453, 7673] ⟨22297739, 2, [(2, 1), (1453, 1), (7673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1453
    · exact prime_7673
  · decide +kernel

theorem prime_29239267 : Nat.Prime 29239267 := by
  apply nodeValid_prime [2, 3, 7, 163, 4271] ⟨29239267, 3, [(2, 1), (3, 1), (7, 1), (163, 1), (4271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_163
    · exact prime_4271
  · decide +kernel

theorem prime_30814711 : Nat.Prime 30814711 := by
  apply nodeValid_prime [2, 3, 5, 17, 23, 37, 71] ⟨30814711, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (23, 1), (37, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_37
    · exact prime_71
  · decide +kernel

theorem prime_31739489 : Nat.Prime 31739489 := by
  apply nodeValid_prime [2, 11, 37, 2437] ⟨31739489, 3, [(2, 5), (11, 1), (37, 1), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_2437
  · decide +kernel

theorem prime_56014841 : Nat.Prime 56014841 := by
  apply nodeValid_prime [2, 5, 7, 28579] ⟨56014841, 3, [(2, 3), (5, 1), (7, 2), (28579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_28579
  · decide +kernel

theorem prime_56299811 : Nat.Prime 56299811 := by
  apply nodeValid_prime [2, 5, 7, 804283] ⟨56299811, 7, [(2, 1), (5, 1), (7, 1), (804283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_804283
  · decide +kernel

theorem prime_63960997 : Nat.Prime 63960997 := by
  apply nodeValid_prime [2, 3, 11, 179, 2707] ⟨63960997, 2, [(2, 2), (3, 1), (11, 1), (179, 1), (2707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_179
    · exact prime_2707
  · decide +kernel

theorem prime_67798033 : Nat.Prime 67798033 := by
  apply nodeValid_prime [2, 3, 389, 3631] ⟨67798033, 10, [(2, 4), (3, 1), (389, 1), (3631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_3631
  · decide +kernel

theorem prime_68981959 : Nat.Prime 68981959 := by
  apply nodeValid_prime [2, 3, 109, 35159] ⟨68981959, 3, [(2, 1), (3, 2), (109, 1), (35159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_35159
  · decide +kernel

theorem prime_75528073 : Nat.Prime 75528073 := by
  apply nodeValid_prime [2, 3, 349667] ⟨75528073, 5, [(2, 3), (3, 3), (349667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349667
  · decide +kernel

theorem prime_89315791 : Nat.Prime 89315791 := by
  apply nodeValid_prime [2, 3, 5, 17, 175129] ⟨89315791, 13, [(2, 1), (3, 1), (5, 1), (17, 1), (175129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_175129
  · decide +kernel

theorem prime_102679771 : Nat.Prime 102679771 := by
  apply nodeValid_prime [2, 3, 5, 179, 19121] ⟨102679771, 2, [(2, 1), (3, 1), (5, 1), (179, 1), (19121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_19121
  · decide +kernel

theorem prime_109695587 : Nat.Prime 109695587 := by
  apply nodeValid_prime [2, 7, 11, 13, 157, 349] ⟨109695587, 2, [(2, 1), (7, 1), (11, 1), (13, 1), (157, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_157
    · exact prime_349
  · decide +kernel

theorem prime_121308013 : Nat.Prime 121308013 := by
  apply nodeValid_prime [2, 3, 7, 41, 59, 199] ⟨121308013, 5, [(2, 2), (3, 2), (7, 1), (41, 1), (59, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_59
    · exact prime_199
  · decide +kernel

theorem prime_128099659 : Nat.Prime 128099659 := by
  apply nodeValid_prime [2, 3, 17, 89, 103, 137] ⟨128099659, 3, [(2, 1), (3, 1), (17, 1), (89, 1), (103, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_89
    · exact prime_103
    · exact prime_137
  · decide +kernel

theorem prime_128997877 : Nat.Prime 128997877 := by
  apply nodeValid_prime [2, 3, 7, 1535689] ⟨128997877, 2, [(2, 2), (3, 1), (7, 1), (1535689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1535689
  · decide +kernel

theorem prime_144611827 : Nat.Prime 144611827 := by
  apply nodeValid_prime [2, 3, 17, 109, 13007] ⟨144611827, 3, [(2, 1), (3, 1), (17, 1), (109, 1), (13007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_109
    · exact prime_13007
  · decide +kernel

theorem prime_151018723 : Nat.Prime 151018723 := by
  apply nodeValid_prime [2, 3, 223, 12541] ⟨151018723, 2, [(2, 1), (3, 3), (223, 1), (12541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_12541
  · decide +kernel

theorem prime_163666039 : Nat.Prime 163666039 := by
  apply nodeValid_prime [2, 3, 17, 19, 79, 1069] ⟨163666039, 11, [(2, 1), (3, 1), (17, 1), (19, 1), (79, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_79
    · exact prime_1069
  · decide +kernel

theorem prime_242575301 : Nat.Prime 242575301 := by
  apply nodeValid_prime [2, 5, 11, 103, 2141] ⟨242575301, 2, [(2, 2), (5, 2), (11, 1), (103, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_103
    · exact prime_2141
  · decide +kernel

theorem prime_347645099 : Nat.Prime 347645099 := by
  apply nodeValid_prime [2, 29, 31, 239, 809] ⟨347645099, 2, [(2, 1), (29, 1), (31, 1), (239, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_31
    · exact prime_239
    · exact prime_809
  · decide +kernel

theorem prime_359339927 : Nat.Prime 359339927 := by
  apply nodeValid_prime [2, 11, 16333633] ⟨359339927, 5, [(2, 1), (11, 1), (16333633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_16333633
  · decide +kernel

theorem prime_554633999 : Nat.Prime 554633999 := by
  apply nodeValid_prime [2, 73, 571, 6653] ⟨554633999, 17, [(2, 1), (73, 1), (571, 1), (6653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_571
    · exact prime_6653
  · decide +kernel

theorem prime_1232157253 : Nat.Prime 1232157253 := by
  apply nodeValid_prime [2, 3, 102679771] ⟨1232157253, 2, [(2, 2), (3, 1), (102679771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102679771
  · decide +kernel

theorem prime_1313894663 : Nat.Prime 1313894663 := by
  apply nodeValid_prime [2, 79, 8315789] ⟨1313894663, 5, [(2, 1), (79, 1), (8315789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_8315789
  · decide +kernel

theorem prime_1563998077 : Nat.Prime 1563998077 := by
  apply nodeValid_prime [2, 3, 79, 379, 1451] ⟨1563998077, 5, [(2, 2), (3, 2), (79, 1), (379, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_379
    · exact prime_1451
  · decide +kernel

theorem prime_1589823317 : Nat.Prime 1589823317 := by
  apply nodeValid_prime [2, 47, 8456507] ⟨1589823317, 2, [(2, 2), (47, 1), (8456507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_8456507
  · decide +kernel

theorem prime_4867031387 : Nat.Prime 4867031387 := by
  apply nodeValid_prime [2, 7, 347645099] ⟨4867031387, 2, [(2, 1), (7, 1), (347645099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_347645099
  · decide +kernel

theorem prime_7704039961 : Nat.Prime 7704039961 := by
  apply nodeValid_prime [2, 3, 5, 43, 497677] ⟨7704039961, 22, [(2, 3), (3, 2), (5, 1), (43, 1), (497677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_497677
  · decide +kernel

theorem prime_16780389569 : Nat.Prime 16780389569 := by
  apply nodeValid_prime [2, 13441, 19507] ⟨16780389569, 3, [(2, 6), (13441, 1), (19507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13441
    · exact prime_19507
  · decide +kernel

theorem prime_18497025553 : Nat.Prime 18497025553 := by
  apply nodeValid_prime [2, 3, 449, 858251] ⟨18497025553, 5, [(2, 4), (3, 1), (449, 1), (858251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
    · exact prime_858251
  · decide +kernel

theorem prime_27267178439 : Nat.Prime 27267178439 := by
  apply nodeValid_prime [2, 2971, 4588889] ⟨27267178439, 7, [(2, 1), (2971, 1), (4588889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2971
    · exact prime_4588889
  · decide +kernel

theorem prime_57712872179 : Nat.Prime 57712872179 := by
  apply nodeValid_prime [2, 13, 17, 397, 328897] ⟨57712872179, 2, [(2, 1), (13, 1), (17, 1), (397, 1), (328897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_397
    · exact prime_328897
  · decide +kernel

theorem prime_92561164061 : Nat.Prime 92561164061 := by
  apply nodeValid_prime [2, 5, 1093, 4234271] ⟨92561164061, 2, [(2, 2), (5, 1), (1093, 1), (4234271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1093
    · exact prime_4234271
  · decide +kernel

theorem prime_165550727539 : Nat.Prime 165550727539 := by
  apply nodeValid_prime [2, 3, 7, 1313894663] ⟨165550727539, 2, [(2, 1), (3, 2), (7, 1), (1313894663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1313894663
  · decide +kernel

theorem prime_256705775231 : Nat.Prime 256705775231 := by
  apply nodeValid_prime [2, 5, 199, 128997877] ⟨256705775231, 11, [(2, 1), (5, 1), (199, 1), (128997877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_128997877
  · decide +kernel

theorem prime_387514043219 : Nat.Prime 387514043219 := by
  apply nodeValid_prime [2, 1283, 151018723] ⟨387514043219, 2, [(2, 1), (1283, 1), (151018723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1283
    · exact prime_151018723
  · decide +kernel

theorem prime_1146926917483 : Nat.Prime 1146926917483 := by
  apply nodeValid_prime [2, 3, 109, 24799, 70717] ⟨1146926917483, 2, [(2, 1), (3, 1), (109, 1), (24799, 1), (70717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_24799
    · exact prime_70717
  · decide +kernel

theorem prime_1155175982533 : Nat.Prime 1155175982533 := by
  apply nodeValid_prime [2, 3, 11, 13, 31, 509, 14221] ⟨1155175982533, 6, [(2, 2), (3, 2), (11, 1), (13, 1), (31, 1), (509, 1), (14221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_509
    · exact prime_14221
  · decide +kernel

theorem prime_2306678797103 : Nat.Prime 2306678797103 := by
  apply nodeValid_prime [2, 71, 281, 547, 105683] ⟨2306678797103, 5, [(2, 1), (71, 1), (281, 1), (547, 1), (105683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_281
    · exact prime_547
    · exact prime_105683
  · decide +kernel

theorem prime_4587707668787 : Nat.Prime 4587707668787 := by
  apply nodeValid_prime [2, 11, 467, 2207, 202327] ⟨4587707668787, 2, [(2, 1), (11, 1), (467, 1), (2207, 1), (202327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_467
    · exact prime_2207
    · exact prime_202327
  · decide +kernel

theorem prime_4587707669933 : Nat.Prime 4587707669933 := by
  apply nodeValid_prime [2, 1146926917483] ⟨4587707669933, 2, [(2, 2), (1146926917483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1146926917483
  · decide +kernel

theorem prime_4587707670901 : Nat.Prime 4587707670901 := by
  apply nodeValid_prime [2, 3, 5, 50503, 302801] ⟨4587707670901, 2, [(2, 2), (3, 1), (5, 2), (50503, 1), (302801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_50503
    · exact prime_302801
  · decide +kernel

theorem prime_4591366012879 : Nat.Prime 4591366012879 := by
  apply nodeValid_prime [2, 3, 2309, 11279, 29383] ⟨4591366012879, 6, [(2, 1), (3, 1), (2309, 1), (11279, 1), (29383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2309
    · exact prime_11279
    · exact prime_29383
  · decide +kernel

theorem prime_4591366012901 : Nat.Prime 4591366012901 := by
  apply nodeValid_prime [2, 5, 17, 41, 2339, 28163] ⟨4591366012901, 2, [(2, 2), (5, 2), (17, 1), (41, 1), (2339, 1), (28163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_41
    · exact prime_2339
    · exact prime_28163
  · decide +kernel

theorem prime_4591366021811 : Nat.Prime 4591366021811 := by
  apply nodeValid_prime [2, 5, 233, 691, 2851727] ⟨4591366021811, 2, [(2, 1), (5, 1), (233, 1), (691, 1), (2851727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
    · exact prime_691
    · exact prime_2851727
  · decide +kernel

theorem prime_4595026252177 : Nat.Prime 4595026252177 := by
  apply nodeValid_prime [2, 3, 31, 43, 61, 130811] ⟨4595026252177, 5, [(2, 4), (3, 3), (31, 1), (43, 1), (61, 1), (130811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
    · exact prime_61
    · exact prime_130811
  · decide +kernel

theorem prime_4595026252909 : Nat.Prime 4595026252909 := by
  apply nodeValid_prime [2, 3, 7, 13, 61, 68981959] ⟨4595026252909, 6, [(2, 2), (3, 1), (7, 1), (13, 1), (61, 1), (68981959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_68981959
  · decide +kernel

theorem prime_4595026350227 : Nat.Prime 4595026350227 := by
  apply nodeValid_prime [2, 13, 113, 1563998077] ⟨4595026350227, 2, [(2, 1), (13, 1), (113, 1), (1563998077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
    · exact prime_1563998077
  · decide +kernel

theorem prime_4598688363823 : Nat.Prime 4598688363823 := by
  apply nodeValid_prime [2, 3, 7, 223, 163666039] ⟨4598688363823, 3, [(2, 1), (3, 2), (7, 1), (223, 1), (163666039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_223
    · exact prime_163666039
  · decide +kernel

theorem prime_4598688364021 : Nat.Prime 4598688364021 := by
  apply nodeValid_prime [2, 3, 5, 827, 3432523] ⟨4598688364021, 6, [(2, 2), (3, 4), (5, 1), (827, 1), (3432523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_827
    · exact prime_3432523
  · decide +kernel

theorem prime_4598688649241 : Nat.Prime 4598688649241 := by
  apply nodeValid_prime [2, 5, 7, 241, 9735559] ⟨4598688649241, 3, [(2, 3), (5, 1), (7, 2), (241, 1), (9735559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_241
    · exact prime_9735559
  · decide +kernel

theorem prime_4602352922389 : Nat.Prime 4602352922389 := by
  apply nodeValid_prime [2, 3, 13, 47, 613, 113777] ⟨4602352922389, 6, [(2, 2), (3, 3), (13, 1), (47, 1), (613, 1), (113777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
    · exact prime_613
    · exact prime_113777
  · decide +kernel

theorem prime_4602352923703 : Nat.Prime 4602352923703 := by
  apply nodeValid_prime [2, 3, 461, 554633999] ⟨4602352923703, 3, [(2, 1), (3, 2), (461, 1), (554633999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
    · exact prime_554633999
  · decide +kernel

theorem prime_4602352925977 : Nat.Prime 4602352925977 := by
  apply nodeValid_prime [2, 3, 13, 107, 2531, 54469] ⟨4602352925977, 5, [(2, 3), (3, 1), (13, 1), (107, 1), (2531, 1), (54469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_107
    · exact prime_2531
    · exact prime_54469
  · decide +kernel

theorem prime_4606019173907 : Nat.Prime 4606019173907 := by
  apply nodeValid_prime [2, 174467, 13200259] ⟨4606019173907, 2, [(2, 1), (174467, 1), (13200259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_174467
    · exact prime_13200259
  · decide +kernel

theorem prime_4606019183893 : Nat.Prime 4606019183893 := by
  apply nodeValid_prime [2, 3, 7, 73, 179, 599477] ⟨4606019183893, 2, [(2, 2), (3, 1), (7, 2), (73, 1), (179, 1), (599477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_179
    · exact prime_599477
  · decide +kernel

theorem prime_4606019184287 : Nat.Prime 4606019184287 := by
  apply nodeValid_prime [2, 13, 17, 29, 359339927] ⟨4606019184287, 5, [(2, 1), (13, 1), (17, 1), (29, 1), (359339927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_29
    · exact prime_359339927
  · decide +kernel

theorem prime_4609687355167 : Nat.Prime 4609687355167 := by
  apply nodeValid_prime [2, 3, 233, 1741, 1893937] ⟨4609687355167, 3, [(2, 1), (3, 1), (233, 1), (1741, 1), (1893937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_1741
    · exact prime_1893937
  · decide +kernel

theorem prime_4609687355233 : Nat.Prime 4609687355233 := by
  apply nodeValid_prime [2, 3, 37, 7333, 176977] ⟨4609687355233, 5, [(2, 5), (3, 1), (37, 1), (7333, 1), (176977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_7333
    · exact prime_176977
  · decide +kernel

theorem prime_4609687399619 : Nat.Prime 4609687399619 := by
  apply nodeValid_prime [2, 7, 11261, 29239267] ⟨4609687399619, 6, [(2, 1), (7, 1), (11261, 1), (29239267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11261
    · exact prime_29239267
  · decide +kernel

theorem prime_4613357594207 : Nat.Prime 4613357594207 := by
  apply nodeValid_prime [2, 2306678797103] ⟨4613357594207, 5, [(2, 1), (2306678797103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2306678797103
  · decide +kernel

theorem prime_4613357603623 : Nat.Prime 4613357603623 := by
  apply nodeValid_prime [2, 3, 34483, 22297739] ⟨4613357603623, 13, [(2, 1), (3, 1), (34483, 1), (22297739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34483
    · exact prime_22297739
  · decide +kernel

theorem prime_4613357606873 : Nat.Prime 4613357606873 := by
  apply nodeValid_prime [2, 7, 751, 109695587] ⟨4613357606873, 3, [(2, 3), (7, 1), (751, 1), (109695587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_751
    · exact prime_109695587
  · decide +kernel

theorem prime_4617029774321 : Nat.Prime 4617029774321 := by
  apply nodeValid_prime [2, 5, 57712872179] ⟨4617029774321, 6, [(2, 4), (5, 1), (57712872179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_57712872179
  · decide +kernel

theorem prime_4617029778553 : Nat.Prime 4617029778553 := by
  apply nodeValid_prime [2, 3, 2081, 30814711] ⟨4617029778553, 5, [(2, 3), (3, 2), (2081, 1), (30814711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2081
    · exact prime_30814711
  · decide +kernel

theorem prime_4617029779129 : Nat.Prime 4617029779129 := by
  apply nodeValid_prime [2, 3, 13, 31, 3613, 44041] ⟨4617029779129, 7, [(2, 3), (3, 2), (13, 1), (31, 1), (3613, 1), (44041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_3613
    · exact prime_44041
  · decide +kernel

theorem prime_4620703930133 : Nat.Prime 4620703930133 := by
  apply nodeValid_prime [2, 1155175982533] ⟨4620703930133, 2, [(2, 2), (1155175982533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1155175982533
  · decide +kernel

theorem prime_4620703954159 : Nat.Prime 4620703954159 := by
  apply nodeValid_prime [2, 3, 256705775231] ⟨4620703954159, 13, [(2, 1), (3, 2), (256705775231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_256705775231
  · decide +kernel

theorem prime_4620703954651 : Nat.Prime 4620703954651 := by
  apply nodeValid_prime [2, 3, 5, 7, 239, 18412847] ⟨4620703954651, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (239, 1), (18412847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_239
    · exact prime_18412847
  · decide +kernel

theorem prime_4624380068323 : Nat.Prime 4624380068323 := by
  apply nodeValid_prime [2, 3, 7, 3469, 31739489] ⟨4624380068323, 2, [(2, 1), (3, 1), (7, 1), (3469, 1), (31739489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3469
    · exact prime_31739489
  · decide +kernel

theorem prime_4624380083101 : Nat.Prime 4624380083101 := by
  apply nodeValid_prime [2, 3, 5, 241, 63960997] ⟨4624380083101, 2, [(2, 2), (3, 1), (5, 2), (241, 1), (63960997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
    · exact prime_63960997
  · decide +kernel

theorem prime_4624380083111 : Nat.Prime 4624380083111 := by
  apply nodeValid_prime [2, 5, 17, 3797, 7164139] ⟨4624380083111, 23, [(2, 1), (5, 1), (17, 1), (3797, 1), (7164139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_3797
    · exact prime_7164139
  · decide +kernel

theorem prime_4628058193103 : Nat.Prime 4628058193103 := by
  apply nodeValid_prime [2, 109, 379, 56014841] ⟨4628058193103, 5, [(2, 1), (109, 1), (379, 1), (56014841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_379
    · exact prime_56014841
  · decide +kernel

theorem prime_4628058201149 : Nat.Prime 4628058201149 := by
  apply nodeValid_prime [2, 15319, 75528073] ⟨4628058201149, 2, [(2, 2), (15319, 1), (75528073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15319
    · exact prime_75528073
  · decide +kernel

theorem prime_4628058203051 : Nat.Prime 4628058203051 := by
  apply nodeValid_prime [2, 5, 92561164061] ⟨4628058203051, 2, [(2, 1), (5, 2), (92561164061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_92561164061
  · decide +kernel

theorem prime_4631738286841 : Nat.Prime 4631738286841 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 59, 310489] ⟨4631738286841, 11, [(2, 3), (3, 1), (5, 1), (7, 2), (43, 1), (59, 1), (310489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_59
    · exact prime_310489
  · decide +kernel

theorem prime_4631738289679 : Nat.Prime 4631738289679 := by
  apply nodeValid_prime [2, 3, 43, 67, 89315791] ⟨4631738289679, 3, [(2, 1), (3, 2), (43, 1), (67, 1), (89315791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_67
    · exact prime_89315791
  · decide +kernel

theorem prime_4631738294059 : Nat.Prime 4631738294059 := by
  apply nodeValid_prime [2, 3, 227, 32749, 103841] ⟨4631738294059, 2, [(2, 1), (3, 1), (227, 1), (32749, 1), (103841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_32749
    · exact prime_103841
  · decide +kernel

theorem prime_4635420333893 : Nat.Prime 4635420333893 := by
  apply nodeValid_prime [2, 113, 50599, 202679] ⟨4635420333893, 2, [(2, 2), (113, 1), (50599, 1), (202679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_50599
    · exact prime_202679
  · decide +kernel

theorem prime_4635420334631 : Nat.Prime 4635420334631 := by
  apply nodeValid_prime [2, 5, 17, 27267178439] ⟨4635420334631, 7, [(2, 1), (5, 1), (17, 1), (27267178439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_27267178439
  · decide +kernel

theorem prime_4635420371093 : Nat.Prime 4635420371093 := by
  apply nodeValid_prime [2, 7, 165550727539] ⟨4635420371093, 2, [(2, 2), (7, 1), (165550727539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_165550727539
  · decide +kernel

theorem prime_4639104426401 : Nat.Prime 4639104426401 := by
  apply nodeValid_prime [2, 5, 103, 56299811] ⟨4639104426401, 3, [(2, 5), (5, 2), (103, 1), (56299811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_56299811
  · decide +kernel

theorem prime_4639104438751 : Nat.Prime 4639104438751 := by
  apply nodeValid_prime [2, 3, 5, 41, 107, 93997] ⟨4639104438751, 3, [(2, 1), (3, 2), (5, 4), (41, 1), (107, 1), (93997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_107
    · exact prime_93997
  · decide +kernel

theorem prime_4639104439007 : Nat.Prime 4639104439007 := by
  apply nodeValid_prime [2, 1459, 1589823317] ⟨4639104439007, 5, [(2, 1), (1459, 1), (1589823317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1459
    · exact prime_1589823317
  · decide +kernel

theorem prime_4642790465603 : Nat.Prime 4642790465603 := by
  apply nodeValid_prime [2, 17, 1277, 8609, 12421] ⟨4642790465603, 2, [(2, 1), (17, 1), (1277, 1), (8609, 1), (12421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1277
    · exact prime_8609
    · exact prime_12421
  · decide +kernel

theorem prime_4642790466761 : Nat.Prime 4642790466761 := by
  apply nodeValid_prime [2, 5, 43, 2657, 1015919] ⟨4642790466761, 3, [(2, 3), (5, 1), (43, 1), (2657, 1), (1015919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_2657
    · exact prime_1015919
  · decide +kernel

theorem prime_4642790467487 : Nat.Prime 4642790467487 := by
  apply nodeValid_prime [2, 609821, 3806683] ⟨4642790467487, 5, [(2, 1), (609821, 1), (3806683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_609821
    · exact prime_3806683
  · decide +kernel

theorem prime_4646478448637 : Nat.Prime 4646478448637 := by
  apply nodeValid_prime [2, 47, 409, 577, 104729] ⟨4646478448637, 2, [(2, 2), (47, 1), (409, 1), (577, 1), (104729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_409
    · exact prime_577
    · exact prime_104729
  · decide +kernel

theorem prime_4646478450203 : Nat.Prime 4646478450203 := by
  apply nodeValid_prime [2, 1328711, 1748491] ⟨4646478450203, 2, [(2, 1), (1328711, 1), (1748491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1328711
    · exact prime_1748491
  · decide +kernel

theorem prime_4646478489431 : Nat.Prime 4646478489431 := by
  apply nodeValid_prime [2, 5, 223, 8443, 246787] ⟨4646478489431, 7, [(2, 1), (5, 1), (223, 1), (8443, 1), (246787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_223
    · exact prime_8443
    · exact prime_246787
  · decide +kernel

theorem prime_4650168489859 : Nat.Prime 4650168489859 := by
  apply nodeValid_prime [2, 3, 181, 3109, 459089] ⟨4650168489859, 2, [(2, 1), (3, 2), (181, 1), (3109, 1), (459089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_3109
    · exact prime_459089
  · decide +kernel

theorem prime_4650168518629 : Nat.Prime 4650168518629 := by
  apply nodeValid_prime [2, 3, 387514043219] ⟨4650168518629, 6, [(2, 2), (3, 1), (387514043219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_387514043219
  · decide +kernel

theorem prime_4650168520171 : Nat.Prime 4650168520171 := by
  apply nodeValid_prime [2, 3, 5, 71, 242575301] ⟨4650168520171, 10, [(2, 1), (3, 3), (5, 1), (71, 1), (242575301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_242575301
  · decide +kernel

theorem prime_4653860464909 : Nat.Prime 4653860464909 := by
  apply nodeValid_prime [2, 3, 47, 199, 619, 827] ⟨4653860464909, 2, [(2, 2), (3, 5), (47, 1), (199, 1), (619, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_199
    · exact prime_619
    · exact prime_827
  · decide +kernel

theorem prime_4653860610733 : Nat.Prime 4653860610733 := by
  apply nodeValid_prime [2, 3, 23, 139, 121308013] ⟨4653860610733, 5, [(2, 2), (3, 1), (23, 1), (139, 1), (121308013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_139
    · exact prime_121308013
  · decide +kernel

theorem prime_4653860611471 : Nat.Prime 4653860611471 := by
  apply nodeValid_prime [2, 3, 5, 7, 173, 128099659] ⟨4653860611471, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (173, 1), (128099659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_173
    · exact prime_128099659
  · decide +kernel

theorem prime_4657554414181 : Nat.Prime 4657554414181 := by
  apply nodeValid_prime [2, 3, 5, 31, 4861, 19079] ⟨4657554414181, 10, [(2, 2), (3, 4), (5, 1), (31, 1), (4861, 1), (19079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_4861
    · exact prime_19079
  · decide +kernel

theorem prime_4657554416341 : Nat.Prime 4657554416341 := by
  apply nodeValid_prime [2, 3, 5, 7, 1232157253] ⟨4657554416341, 2, [(2, 2), (3, 3), (5, 1), (7, 1), (1232157253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1232157253
  · decide +kernel

theorem prime_4657554419027 : Nat.Prime 4657554419027 := by
  apply nodeValid_prime [2, 29, 103, 26699, 29201] ⟨4657554419027, 2, [(2, 1), (29, 1), (103, 1), (26699, 1), (29201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_103
    · exact prime_26699
    · exact prime_29201
  · decide +kernel

theorem prime_4661250364817 : Nat.Prime 4661250364817 := by
  apply nodeValid_prime [2, 4297, 67798033] ⟨4661250364817, 3, [(2, 4), (4297, 1), (67798033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4297
    · exact prime_67798033
  · decide +kernel

theorem prime_4661250439357 : Nat.Prime 4661250439357 := by
  apply nodeValid_prime [2, 3, 7, 18497025553] ⟨4661250439357, 5, [(2, 2), (3, 2), (7, 1), (18497025553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18497025553
  · decide +kernel

theorem prime_4661250439739 : Nat.Prime 4661250439739 := by
  apply nodeValid_prime [2, 619, 1013, 3716827] ⟨4661250439739, 2, [(2, 1), (619, 1), (1013, 1), (3716827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_1013
    · exact prime_3716827
  · decide +kernel

theorem prime_4664948300183 : Nat.Prime 4664948300183 := by
  apply nodeValid_prime [2, 139, 16780389569] ⟨4664948300183, 5, [(2, 1), (139, 1), (16780389569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_16780389569
  · decide +kernel

theorem prime_4664948353381 : Nat.Prime 4664948353381 := by
  apply nodeValid_prime [2, 3, 5, 7, 53, 1108817] ⟨4664948353381, 11, [(2, 2), (3, 4), (5, 1), (7, 2), (53, 1), (1108817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_1108817
  · decide +kernel

theorem prime_4664948353567 : Nat.Prime 4664948353567 := by
  apply nodeValid_prime [2, 3, 29, 157, 1129, 151253] ⟨4664948353567, 5, [(2, 1), (3, 1), (29, 1), (157, 1), (1129, 1), (151253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_157
    · exact prime_1129
    · exact prime_151253
  · decide +kernel

theorem prime_4668648216301 : Nat.Prime 4668648216301 := by
  apply nodeValid_prime [2, 3, 5, 241, 797201] ⟨4668648216301, 6, [(2, 2), (3, 5), (5, 2), (241, 1), (797201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
    · exact prime_797201
  · decide +kernel

theorem prime_4668648216367 : Nat.Prime 4668648216367 := by
  apply nodeValid_prime [2, 3, 101, 7704039961] ⟨4668648216367, 3, [(2, 1), (3, 1), (101, 1), (7704039961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_7704039961
  · decide +kernel

theorem prime_4668648222869 : Nat.Prime 4668648222869 := by
  apply nodeValid_prime [2, 7, 1153, 144611827] ⟨4668648222869, 3, [(2, 2), (7, 1), (1153, 1), (144611827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1153
    · exact prime_144611827
  · decide +kernel

theorem prime_4672350127477 : Nat.Prime 4672350127477 := by
  apply nodeValid_prime [2, 3, 19, 151, 607, 74527] ⟨4672350127477, 5, [(2, 2), (3, 2), (19, 1), (151, 1), (607, 1), (74527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_151
    · exact prime_607
    · exact prime_74527
  · decide +kernel

theorem prime_4672350127901 : Nat.Prime 4672350127901 := by
  apply nodeValid_prime [2, 5, 7, 13, 43, 11940583] ⟨4672350127901, 2, [(2, 2), (5, 2), (7, 1), (13, 1), (43, 1), (11940583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_11940583
  · decide +kernel

theorem prime_4672350131521 : Nat.Prime 4672350131521 := by
  apply nodeValid_prime [2, 3, 5, 4867031387] ⟨4672350131521, 11, [(2, 6), (3, 1), (5, 1), (4867031387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4867031387
  · decide +kernel

theorem prime_4676053962497 : Nat.Prime 4676053962497 := by
  apply nodeValid_prime [2, 7, 61, 131, 46649] ⟨4676053962497, 3, [(2, 8), (7, 2), (61, 1), (131, 1), (46649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_131
    · exact prime_46649
  · decide +kernel

theorem prime_4676053962917 : Nat.Prime 4676053962917 := by
  apply nodeValid_prime [2, 7, 80933, 2063459] ⟨4676053962917, 2, [(2, 2), (7, 1), (80933, 1), (2063459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_80933
    · exact prime_2063459
  · decide +kernel

theorem prime_4676054029117 : Nat.Prime 4676054029117 := by
  apply nodeValid_prime [2, 3, 203569, 1914197] ⟨4676054029117, 2, [(2, 2), (3, 1), (203569, 1), (1914197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_203569
    · exact prime_1914197
  · decide +kernel

end Sude.Lucas.Generated
