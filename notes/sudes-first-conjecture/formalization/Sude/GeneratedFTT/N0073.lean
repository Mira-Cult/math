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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0063

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5483 : Nat.Prime 5483 := by
  apply nodeValid_prime [2, 2741] ⟨5483, 2, [(2, 1), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2741
  · decide +kernel

theorem prime_5531 : Nat.Prime 5531 := by
  apply nodeValid_prime [2, 5, 7, 79] ⟨5531, 10, [(2, 1), (5, 1), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_9619 : Nat.Prime 9619 := by
  apply nodeValid_prime [2, 3, 7, 229] ⟨9619, 2, [(2, 1), (3, 1), (7, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_229
  · decide +kernel

theorem prime_9907 : Nat.Prime 9907 := by
  apply nodeValid_prime [2, 3, 13, 127] ⟨9907, 2, [(2, 1), (3, 1), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_12347 : Nat.Prime 12347 := by
  apply nodeValid_prime [2, 6173] ⟨12347, 2, [(2, 1), (6173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6173
  · decide +kernel

theorem prime_13249 : Nat.Prime 13249 := by
  apply nodeValid_prime [2, 3, 23] ⟨13249, 7, [(2, 6), (3, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_14033 : Nat.Prime 14033 := by
  apply nodeValid_prime [2, 877] ⟨14033, 3, [(2, 4), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_877
  · decide +kernel

theorem prime_15731 : Nat.Prime 15731 := by
  apply nodeValid_prime [2, 5, 11, 13] ⟨15731, 2, [(2, 1), (5, 1), (11, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_20297 : Nat.Prime 20297 := by
  apply nodeValid_prime [2, 43, 59] ⟨20297, 3, [(2, 3), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_20407 : Nat.Prime 20407 := by
  apply nodeValid_prime [2, 3, 19, 179] ⟨20407, 5, [(2, 1), (3, 1), (19, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_179
  · decide +kernel

theorem prime_25457 : Nat.Prime 25457 := by
  apply nodeValid_prime [2, 37, 43] ⟨25457, 3, [(2, 4), (37, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
  · decide +kernel

theorem prime_25819 : Nat.Prime 25819 := by
  apply nodeValid_prime [2, 3, 13, 331] ⟨25819, 3, [(2, 1), (3, 1), (13, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_331
  · decide +kernel

theorem prime_26893 : Nat.Prime 26893 := by
  apply nodeValid_prime [2, 3, 83] ⟨26893, 5, [(2, 2), (3, 4), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_28499 : Nat.Prime 28499 := by
  apply nodeValid_prime [2, 14249] ⟨28499, 2, [(2, 1), (14249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14249
  · decide +kernel

theorem prime_29881 : Nat.Prime 29881 := by
  apply nodeValid_prime [2, 3, 5, 83] ⟨29881, 7, [(2, 3), (3, 2), (5, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
  · decide +kernel

theorem prime_31391 : Nat.Prime 31391 := by
  apply nodeValid_prime [2, 5, 43, 73] ⟨31391, 31, [(2, 1), (5, 1), (43, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_73
  · decide +kernel

theorem prime_33073 : Nat.Prime 33073 := by
  apply nodeValid_prime [2, 3, 13, 53] ⟨33073, 5, [(2, 4), (3, 1), (13, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_34913 : Nat.Prime 34913 := by
  apply nodeValid_prime [2, 1091] ⟨34913, 3, [(2, 5), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1091
  · decide +kernel

theorem prime_35747 : Nat.Prime 35747 := by
  apply nodeValid_prime [2, 61, 293] ⟨35747, 2, [(2, 1), (61, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_293
  · decide +kernel

theorem prime_35863 : Nat.Prime 35863 := by
  apply nodeValid_prime [2, 3, 43, 139] ⟨35863, 3, [(2, 1), (3, 1), (43, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_139
  · decide +kernel

theorem prime_37087 : Nat.Prime 37087 := by
  apply nodeValid_prime [2, 3, 7, 883] ⟨37087, 3, [(2, 1), (3, 1), (7, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_883
  · decide +kernel

theorem prime_37357 : Nat.Prime 37357 := by
  apply nodeValid_prime [2, 3, 11, 283] ⟨37357, 6, [(2, 2), (3, 1), (11, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_283
  · decide +kernel

theorem prime_44249 : Nat.Prime 44249 := by
  apply nodeValid_prime [2, 5531] ⟨44249, 3, [(2, 3), (5531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5531
  · decide +kernel

theorem prime_60343 : Nat.Prime 60343 := by
  apply nodeValid_prime [2, 3, 89, 113] ⟨60343, 3, [(2, 1), (3, 1), (89, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_113
  · decide +kernel

theorem prime_71971 : Nat.Prime 71971 := by
  apply nodeValid_prime [2, 3, 5, 2399] ⟨71971, 2, [(2, 1), (3, 1), (5, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2399
  · decide +kernel

theorem prime_75083 : Nat.Prime 75083 := by
  apply nodeValid_prime [2, 7, 31, 173] ⟨75083, 2, [(2, 1), (7, 1), (31, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_173
  · decide +kernel

theorem prime_77527 : Nat.Prime 77527 := by
  apply nodeValid_prime [2, 3, 59, 73] ⟨77527, 5, [(2, 1), (3, 2), (59, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_73
  · decide +kernel

theorem prime_83071 : Nat.Prime 83071 := by
  apply nodeValid_prime [2, 3, 5, 13, 71] ⟨83071, 14, [(2, 1), (3, 2), (5, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_84503 : Nat.Prime 84503 := by
  apply nodeValid_prime [2, 11, 23, 167] ⟨84503, 15, [(2, 1), (11, 1), (23, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_167
  · decide +kernel

theorem prime_87751 : Nat.Prime 87751 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨87751, 3, [(2, 1), (3, 3), (5, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_88499 : Nat.Prime 88499 := by
  apply nodeValid_prime [2, 44249] ⟨88499, 2, [(2, 1), (44249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44249
  · decide +kernel

theorem prime_96097 : Nat.Prime 96097 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨96097, 5, [(2, 5), (3, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_109661 : Nat.Prime 109661 := by
  apply nodeValid_prime [2, 5, 5483] ⟨109661, 3, [(2, 2), (5, 1), (5483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5483
  · decide +kernel

theorem prime_118061 : Nat.Prime 118061 := by
  apply nodeValid_prime [2, 5, 5903] ⟨118061, 2, [(2, 2), (5, 1), (5903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5903
  · decide +kernel

theorem prime_120811 : Nat.Prime 120811 := by
  apply nodeValid_prime [2, 3, 5, 4027] ⟨120811, 3, [(2, 1), (3, 1), (5, 1), (4027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4027
  · decide +kernel

theorem prime_122321 : Nat.Prime 122321 := by
  apply nodeValid_prime [2, 5, 11, 139] ⟨122321, 6, [(2, 4), (5, 1), (11, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_139
  · decide +kernel

theorem prime_122443 : Nat.Prime 122443 := by
  apply nodeValid_prime [2, 3, 20407] ⟨122443, 2, [(2, 1), (3, 1), (20407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20407
  · decide +kernel

theorem prime_166597 : Nat.Prime 166597 := by
  apply nodeValid_prime [2, 3, 13883] ⟨166597, 2, [(2, 2), (3, 1), (13883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13883
  · decide +kernel

theorem prime_189743 : Nat.Prime 189743 := by
  apply nodeValid_prime [2, 7, 13553] ⟨189743, 5, [(2, 1), (7, 1), (13553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13553
  · decide +kernel

theorem prime_270217 : Nat.Prime 270217 := by
  apply nodeValid_prime [2, 3, 139] ⟨270217, 7, [(2, 3), (3, 5), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_284159 : Nat.Prime 284159 := by
  apply nodeValid_prime [2, 7, 20297] ⟨284159, 7, [(2, 1), (7, 1), (20297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_20297
  · decide +kernel

theorem prime_349697 : Nat.Prime 349697 := by
  apply nodeValid_prime [2, 683] ⟨349697, 3, [(2, 9), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_683
  · decide +kernel

theorem prime_408041 : Nat.Prime 408041 := by
  apply nodeValid_prime [2, 5, 101] ⟨408041, 3, [(2, 3), (5, 1), (101, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_445157 : Nat.Prime 445157 := by
  apply nodeValid_prime [2, 109, 1021] ⟨445157, 2, [(2, 2), (109, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_1021
  · decide +kernel

theorem prime_461101 : Nat.Prime 461101 := by
  apply nodeValid_prime [2, 3, 5, 29, 53] ⟨461101, 2, [(2, 2), (3, 1), (5, 2), (29, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_53
  · decide +kernel

theorem prime_472573 : Nat.Prime 472573 := by
  apply nodeValid_prime [2, 3, 13127] ⟨472573, 2, [(2, 2), (3, 2), (13127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13127
  · decide +kernel

theorem prime_509801 : Nat.Prime 509801 := by
  apply nodeValid_prime [2, 5, 2549] ⟨509801, 7, [(2, 3), (5, 2), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2549
  · decide +kernel

theorem prime_541991 : Nat.Prime 541991 := by
  apply nodeValid_prime [2, 5, 83, 653] ⟨541991, 7, [(2, 1), (5, 1), (83, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_653
  · decide +kernel

theorem prime_603431 : Nat.Prime 603431 := by
  apply nodeValid_prime [2, 5, 60343] ⟨603431, 11, [(2, 1), (5, 1), (60343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_60343
  · decide +kernel

theorem prime_1056269 : Nat.Prime 1056269 := by
  apply nodeValid_prime [2, 347, 761] ⟨1056269, 2, [(2, 2), (347, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_761
  · decide +kernel

theorem prime_1128577 : Nat.Prime 1128577 := by
  apply nodeValid_prime [2, 3, 2939] ⟨1128577, 11, [(2, 7), (3, 1), (2939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2939
  · decide +kernel

theorem prime_1253717 : Nat.Prime 1253717 := by
  apply nodeValid_prime [2, 17, 103, 179] ⟨1253717, 2, [(2, 2), (17, 1), (103, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
    · exact prime_179
  · decide +kernel

theorem prime_1360441 : Nat.Prime 1360441 := by
  apply nodeValid_prime [2, 3, 5, 3779] ⟨1360441, 14, [(2, 3), (3, 2), (5, 1), (3779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3779
  · decide +kernel

theorem prime_1473221 : Nat.Prime 1473221 := by
  apply nodeValid_prime [2, 5, 7, 17, 619] ⟨1473221, 2, [(2, 2), (5, 1), (7, 1), (17, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_619
  · decide +kernel

theorem prime_1479197 : Nat.Prime 1479197 := by
  apply nodeValid_prime [2, 31, 79, 151] ⟨1479197, 2, [(2, 2), (31, 1), (79, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_79
    · exact prime_151
  · decide +kernel

theorem prime_1505737 : Nat.Prime 1505737 := by
  apply nodeValid_prime [2, 3, 6971] ⟨1505737, 10, [(2, 3), (3, 3), (6971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6971
  · decide +kernel

theorem prime_1580417 : Nat.Prime 1580417 := by
  apply nodeValid_prime [2, 12347] ⟨1580417, 3, [(2, 7), (12347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12347
  · decide +kernel

theorem prime_2015833 : Nat.Prime 2015833 := by
  apply nodeValid_prime [2, 3, 7, 13, 71] ⟨2015833, 5, [(2, 3), (3, 1), (7, 1), (13, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_2125099 : Nat.Prime 2125099 := by
  apply nodeValid_prime [2, 3, 118061] ⟨2125099, 2, [(2, 1), (3, 2), (118061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_118061
  · decide +kernel

theorem prime_2822159 : Nat.Prime 2822159 := by
  apply nodeValid_prime [2, 617, 2287] ⟨2822159, 7, [(2, 1), (617, 1), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_617
    · exact prime_2287
  · decide +kernel

theorem prime_2946443 : Nat.Prime 2946443 := by
  apply nodeValid_prime [2, 1473221] ⟨2946443, 2, [(2, 1), (1473221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1473221
  · decide +kernel

theorem prime_2990557 : Nat.Prime 2990557 := by
  apply nodeValid_prime [2, 3, 83071] ⟨2990557, 2, [(2, 2), (3, 2), (83071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83071
  · decide +kernel

theorem prime_3541651 : Nat.Prime 3541651 := by
  apply nodeValid_prime [2, 3, 5, 7, 3373] ⟨3541651, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (3373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3373
  · decide +kernel

theorem prime_3903413 : Nat.Prime 3903413 := by
  apply nodeValid_prime [2, 367, 2659] ⟨3903413, 2, [(2, 2), (367, 1), (2659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_2659
  · decide +kernel

theorem prime_3944881 : Nat.Prime 3944881 := by
  apply nodeValid_prime [2, 3, 5, 5479] ⟨3944881, 7, [(2, 4), (3, 2), (5, 1), (5479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5479
  · decide +kernel

theorem prime_5644319 : Nat.Prime 5644319 := by
  apply nodeValid_prime [2, 2822159] ⟨5644319, 7, [(2, 1), (2822159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2822159
  · decide +kernel

theorem prime_6130021 : Nat.Prime 6130021 := by
  apply nodeValid_prime [2, 3, 5, 13, 29, 271] ⟨6130021, 10, [(2, 2), (3, 1), (5, 1), (13, 1), (29, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_29
    · exact prime_271
  · decide +kernel

theorem prime_9482503 : Nat.Prime 9482503 := by
  apply nodeValid_prime [2, 3, 1580417] ⟨9482503, 6, [(2, 1), (3, 1), (1580417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1580417
  · decide +kernel

theorem prime_9711733 : Nat.Prime 9711733 := by
  apply nodeValid_prime [2, 3, 467, 1733] ⟨9711733, 2, [(2, 2), (3, 1), (467, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_1733
  · decide +kernel

theorem prime_10068137 : Nat.Prime 10068137 := by
  apply nodeValid_prime [2, 13, 131, 739] ⟨10068137, 3, [(2, 3), (13, 1), (131, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_131
    · exact prime_739
  · decide +kernel

theorem prime_11139269 : Nat.Prime 11139269 := by
  apply nodeValid_prime [2, 7, 23, 353] ⟨11139269, 3, [(2, 2), (7, 3), (23, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_353
  · decide +kernel

theorem prime_11482301 : Nat.Prime 11482301 := by
  apply nodeValid_prime [2, 5, 199, 577] ⟨11482301, 2, [(2, 2), (5, 2), (199, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_577
  · decide +kernel

theorem prime_12761009 : Nat.Prime 12761009 := by
  apply nodeValid_prime [2, 13, 19, 3229] ⟨12761009, 3, [(2, 4), (13, 1), (19, 1), (3229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_3229
  · decide +kernel

theorem prime_13392871 : Nat.Prime 13392871 := by
  apply nodeValid_prime [2, 3, 5, 79, 5651] ⟨13392871, 35, [(2, 1), (3, 1), (5, 1), (79, 1), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_5651
  · decide +kernel

theorem prime_15584497 : Nat.Prime 15584497 := by
  apply nodeValid_prime [2, 3, 59, 5503] ⟨15584497, 10, [(2, 4), (3, 1), (59, 1), (5503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_5503
  · decide +kernel

theorem prime_16021321 : Nat.Prime 16021321 := by
  apply nodeValid_prime [2, 3, 5, 7, 19073] ⟨16021321, 22, [(2, 3), (3, 1), (5, 1), (7, 1), (19073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19073
  · decide +kernel

theorem prime_18947521 : Nat.Prime 18947521 := by
  apply nodeValid_prime [2, 3, 5, 17, 43] ⟨18947521, 7, [(2, 6), (3, 4), (5, 1), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_21362113 : Nat.Prime 21362113 := by
  apply nodeValid_prime [2, 3, 37087] ⟨21362113, 5, [(2, 6), (3, 2), (37087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37087
  · decide +kernel

theorem prime_32426041 : Nat.Prime 32426041 := by
  apply nodeValid_prime [2, 3, 5, 270217] ⟨32426041, 22, [(2, 3), (3, 1), (5, 1), (270217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_270217
  · decide +kernel

theorem prime_34691609 : Nat.Prime 34691609 := by
  apply nodeValid_prime [2, 7, 88499] ⟨34691609, 3, [(2, 3), (7, 2), (88499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_88499
  · decide +kernel

theorem prime_41780831 : Nat.Prime 41780831 := by
  apply nodeValid_prime [2, 5, 7, 13, 937] ⟨41780831, 22, [(2, 1), (5, 1), (7, 3), (13, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_937
  · decide +kernel

theorem prime_59015081 : Nat.Prime 59015081 := by
  apply nodeValid_prime [2, 5, 47, 31391] ⟨59015081, 3, [(2, 3), (5, 1), (47, 1), (31391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_31391
  · decide +kernel

theorem prime_112886381 : Nat.Prime 112886381 := by
  apply nodeValid_prime [2, 5, 5644319] ⟨112886381, 2, [(2, 2), (5, 1), (5644319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5644319
  · decide +kernel

theorem prime_113137333 : Nat.Prime 113137333 := by
  apply nodeValid_prime [2, 3, 7, 11, 122443] ⟨113137333, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (122443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_122443
  · decide +kernel

theorem prime_120384623 : Nat.Prime 120384623 := by
  apply nodeValid_prime [2, 23, 167, 15671] ⟨120384623, 5, [(2, 1), (23, 1), (167, 1), (15671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_167
    · exact prime_15671
  · decide +kernel

theorem prime_211628717 : Nat.Prime 211628717 := by
  apply nodeValid_prime [2, 13, 17, 41, 5839] ⟨211628717, 2, [(2, 2), (13, 1), (17, 1), (41, 1), (5839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_41
    · exact prime_5839
  · decide +kernel

theorem prime_240769247 : Nat.Prime 240769247 := by
  apply nodeValid_prime [2, 120384623] ⟨240769247, 5, [(2, 1), (120384623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120384623
  · decide +kernel

theorem prime_303365771 : Nat.Prime 303365771 := by
  apply nodeValid_prime [2, 5, 359, 84503] ⟨303365771, 2, [(2, 1), (5, 1), (359, 1), (84503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_359
    · exact prime_84503
  · decide +kernel

theorem prime_303872929 : Nat.Prime 303872929 := by
  apply nodeValid_prime [2, 3, 19, 166597] ⟨303872929, 14, [(2, 5), (3, 1), (19, 1), (166597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_166597
  · decide +kernel

theorem prime_354090487 : Nat.Prime 354090487 := by
  apply nodeValid_prime [2, 3, 59015081] ⟨354090487, 5, [(2, 1), (3, 1), (59015081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59015081
  · decide +kernel

theorem prime_397321843 : Nat.Prime 397321843 := by
  apply nodeValid_prime [2, 3, 349, 189743] ⟨397321843, 2, [(2, 1), (3, 1), (349, 1), (189743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_189743
  · decide +kernel

theorem prime_529872899 : Nat.Prime 529872899 := by
  apply nodeValid_prime [2, 17, 15584497] ⟨529872899, 2, [(2, 1), (17, 1), (15584497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_15584497
  · decide +kernel

theorem prime_713372903 : Nat.Prime 713372903 := by
  apply nodeValid_prime [2, 11, 32426041] ⟨713372903, 5, [(2, 1), (11, 1), (32426041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_32426041
  · decide +kernel

theorem prime_782949499 : Nat.Prime 782949499 := by
  apply nodeValid_prime [2, 3, 283, 461101] ⟨782949499, 2, [(2, 1), (3, 1), (283, 1), (461101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_461101
  · decide +kernel

theorem prime_1017978251 : Nat.Prime 1017978251 := by
  apply nodeValid_prime [2, 5, 109, 37357] ⟨1017978251, 6, [(2, 1), (5, 3), (109, 1), (37357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_37357
  · decide +kernel

theorem prime_1107233173 : Nat.Prime 1107233173 := by
  apply nodeValid_prime [2, 3, 1019, 10061] ⟨1107233173, 2, [(2, 2), (3, 3), (1019, 1), (10061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1019
    · exact prime_10061
  · decide +kernel

theorem prime_1148404949 : Nat.Prime 1148404949 := by
  apply nodeValid_prime [2, 821, 349697] ⟨1148404949, 2, [(2, 2), (821, 1), (349697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_821
    · exact prime_349697
  · decide +kernel

theorem prime_1333697083 : Nat.Prime 1333697083 := by
  apply nodeValid_prime [2, 3, 2027, 109661] ⟨1333697083, 2, [(2, 1), (3, 1), (2027, 1), (109661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2027
    · exact prime_109661
  · decide +kernel

theorem prime_1354636573 : Nat.Prime 1354636573 := by
  apply nodeValid_prime [2, 3, 112886381] ⟨1354636573, 2, [(2, 2), (3, 1), (112886381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_112886381
  · decide +kernel

theorem prime_1357692751 : Nat.Prime 1357692751 := by
  apply nodeValid_prime [2, 3, 5, 43, 14033] ⟨1357692751, 3, [(2, 1), (3, 2), (5, 3), (43, 1), (14033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_14033
  · decide +kernel

theorem prime_1656078653 : Nat.Prime 1656078653 := by
  apply nodeValid_prime [2, 31, 47, 284159] ⟨1656078653, 2, [(2, 2), (31, 1), (47, 1), (284159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_47
    · exact prime_284159
  · decide +kernel

theorem prime_1989490673 : Nat.Prime 1989490673 := by
  apply nodeValid_prime [2, 13, 109, 87751] ⟨1989490673, 3, [(2, 4), (13, 1), (109, 1), (87751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_109
    · exact prime_87751
  · decide +kernel

theorem prime_2033986481 : Nat.Prime 2033986481 := by
  apply nodeValid_prime [2, 5, 19, 101, 13249] ⟨2033986481, 3, [(2, 4), (5, 1), (19, 1), (101, 1), (13249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_101
    · exact prime_13249
  · decide +kernel

theorem prime_3640389253 : Nat.Prime 3640389253 := by
  apply nodeValid_prime [2, 3, 303365771] ⟨3640389253, 2, [(2, 2), (3, 1), (303365771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_303365771
  · decide +kernel

theorem prime_3652578203 : Nat.Prime 3652578203 := by
  apply nodeValid_prime [2, 7, 13, 19, 1056269] ⟨3652578203, 2, [(2, 1), (7, 1), (13, 1), (19, 1), (1056269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_1056269
  · decide +kernel

theorem prime_5665447793 : Nat.Prime 5665447793 := by
  apply nodeValid_prime [2, 354090487] ⟨5665447793, 3, [(2, 4), (354090487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_354090487
  · decide +kernel

theorem prime_8227346969 : Nat.Prime 8227346969 := by
  apply nodeValid_prime [2, 683, 1505737] ⟨8227346969, 3, [(2, 3), (683, 1), (1505737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_683
    · exact prime_1505737
  · decide +kernel

theorem prime_9294546791 : Nat.Prime 9294546791 := by
  apply nodeValid_prime [2, 5, 23, 31, 89, 97, 151] ⟨9294546791, 19, [(2, 1), (5, 1), (23, 1), (31, 1), (89, 1), (97, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_31
    · exact prime_89
    · exact prime_97
    · exact prime_151
  · decide +kernel

theorem prime_14390752757 : Nat.Prime 14390752757 := by
  apply nodeValid_prime [2, 17, 211628717] ⟨14390752757, 2, [(2, 2), (17, 1), (211628717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_211628717
  · decide +kernel

theorem prime_18323608519 : Nat.Prime 18323608519 := by
  apply nodeValid_prime [2, 3, 1017978251] ⟨18323608519, 3, [(2, 1), (3, 2), (1017978251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1017978251
  · decide +kernel

theorem prime_22980804593 : Nat.Prime 22980804593 := by
  apply nodeValid_prime [2, 971, 1479197] ⟨22980804593, 3, [(2, 4), (971, 1), (1479197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_971
    · exact prime_1479197
  · decide +kernel

theorem prime_27546422833 : Nat.Prime 27546422833 := by
  apply nodeValid_prime [2, 3, 19, 10068137] ⟨27546422833, 5, [(2, 4), (3, 2), (19, 1), (10068137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_10068137
  · decide +kernel

theorem prime_32137926241 : Nat.Prime 32137926241 := by
  apply nodeValid_prime [2, 3, 5, 7, 109, 87751] ⟨32137926241, 13, [(2, 5), (3, 1), (5, 1), (7, 1), (109, 1), (87751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_109
    · exact prime_87751
  · decide +kernel

theorem prime_58506256037 : Nat.Prime 58506256037 := by
  apply nodeValid_prime [2, 24239, 603431] ⟨58506256037, 2, [(2, 2), (24239, 1), (603431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_24239
    · exact prime_603431
  · decide +kernel

theorem prime_59618831509 : Nat.Prime 59618831509 := by
  apply nodeValid_prime [2, 3, 1656078653] ⟨59618831509, 2, [(2, 2), (3, 2), (1656078653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1656078653
  · decide +kernel

theorem prime_93150838307 : Nat.Prime 93150838307 := by
  apply nodeValid_prime [2, 41, 9403, 120811] ⟨93150838307, 2, [(2, 1), (41, 1), (9403, 1), (120811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_9403
    · exact prime_120811
  · decide +kernel

theorem prime_104794695163 : Nat.Prime 104794695163 := by
  apply nodeValid_prime [2, 3, 23, 29, 43, 71, 953] ⟨104794695163, 2, [(2, 1), (3, 3), (23, 1), (29, 1), (43, 1), (71, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_29
    · exact prime_43
    · exact prime_71
    · exact prime_953
  · decide +kernel

theorem prime_165278546821 : Nat.Prime 165278546821 := by
  apply nodeValid_prime [2, 3, 5, 17, 787, 22877] ⟨165278546821, 2, [(2, 2), (3, 3), (5, 1), (17, 1), (787, 1), (22877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_787
    · exact prime_22877
  · decide +kernel

theorem prime_273636587747 : Nat.Prime 273636587747 := by
  apply nodeValid_prime [2, 101, 1354636573] ⟨273636587747, 2, [(2, 1), (101, 1), (1354636573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_1354636573
  · decide +kernel

theorem prime_818177517473 : Nat.Prime 818177517473 := by
  apply nodeValid_prime [2, 7, 3652578203] ⟨818177517473, 3, [(2, 5), (7, 1), (3652578203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3652578203
  · decide +kernel

theorem prime_819087584351 : Nat.Prime 819087584351 := by
  apply nodeValid_prime [2, 5, 7, 71, 96097] ⟨819087584351, 19, [(2, 1), (5, 2), (7, 4), (71, 1), (96097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_96097
  · decide +kernel

theorem prime_819087584519 : Nat.Prime 819087584519 := by
  apply nodeValid_prime [2, 7, 58506256037] ⟨819087584519, 7, [(2, 1), (7, 1), (58506256037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_58506256037
  · decide +kernel

theorem prime_837433062311 : Nat.Prime 837433062311 := by
  apply nodeValid_prime [2, 5, 13, 47, 67, 139, 14717] ⟨837433062311, 29, [(2, 1), (5, 1), (13, 1), (47, 1), (67, 1), (139, 1), (14717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_47
    · exact prime_67
    · exact prime_139
    · exact prime_14717
  · decide +kernel

theorem prime_1636355034889 : Nat.Prime 1636355034889 := by
  apply nodeValid_prime [2, 3, 7, 79, 2069, 8513] ⟨1636355034889, 31, [(2, 3), (3, 1), (7, 2), (79, 1), (2069, 1), (8513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_2069
    · exact prime_8513
  · decide +kernel

theorem prime_1636355034947 : Nat.Prime 1636355034947 := by
  apply nodeValid_prime [2, 818177517473] ⟨1636355034947, 2, [(2, 1), (818177517473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_818177517473
  · decide +kernel

theorem prime_1636355035919 : Nat.Prime 1636355035919 := by
  apply nodeValid_prime [2, 47, 5821, 2990557] ⟨1636355035919, 7, [(2, 1), (47, 1), (5821, 1), (2990557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_5821
    · exact prime_2990557
  · decide +kernel

theorem prime_1638175163851 : Nat.Prime 1638175163851 := by
  apply nodeValid_prime [2, 3, 5, 3640389253] ⟨1638175163851, 3, [(2, 1), (3, 2), (5, 2), (3640389253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3640389253
  · decide +kernel

theorem prime_1638175168703 : Nat.Prime 1638175168703 := by
  apply nodeValid_prime [2, 819087584351] ⟨1638175168703, 5, [(2, 1), (819087584351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_819087584351
  · decide +kernel

theorem prime_1638175169039 : Nat.Prime 1638175169039 := by
  apply nodeValid_prime [2, 819087584519] ⟨1638175169039, 13, [(2, 1), (819087584519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_819087584519
  · decide +kernel

theorem prime_1639996658197 : Nat.Prime 1639996658197 := by
  apply nodeValid_prime [2, 3, 13, 503, 821, 25457] ⟨1639996658197, 2, [(2, 2), (3, 1), (13, 1), (503, 1), (821, 1), (25457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_503
    · exact prime_821
    · exact prime_25457
  · decide +kernel

theorem prime_1639996671503 : Nat.Prime 1639996671503 := by
  apply nodeValid_prime [2, 7, 79, 3331, 445157] ⟨1639996671503, 5, [(2, 1), (7, 1), (79, 1), (3331, 1), (445157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_3331
    · exact prime_445157
  · decide +kernel

theorem prime_1639996673351 : Nat.Prime 1639996673351 := by
  apply nodeValid_prime [2, 5, 7, 17, 3671, 75083] ⟨1639996673351, 7, [(2, 1), (5, 2), (7, 1), (17, 1), (3671, 1), (75083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_3671
    · exact prime_75083
  · decide +kernel

theorem prime_1641819526483 : Nat.Prime 1641819526483 := by
  apply nodeValid_prime [2, 3, 273636587747] ⟨1641819526483, 2, [(2, 1), (3, 1), (273636587747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_273636587747
  · decide +kernel

theorem prime_1641819534427 : Nat.Prime 1641819534427 := by
  apply nodeValid_prime [2, 3, 9619, 9482503] ⟨1641819534427, 2, [(2, 1), (3, 2), (9619, 1), (9482503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9619
    · exact prime_9482503
  · decide +kernel

theorem prime_1641819534977 : Nat.Prime 1641819534977 := by
  apply nodeValid_prime [2, 307, 41780831] ⟨1641819534977, 3, [(2, 7), (307, 1), (41780831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_41780831
  · decide +kernel

theorem prime_1643643698027 : Nat.Prime 1643643698027 := by
  apply nodeValid_prime [2, 11, 19, 353, 11139269] ⟨1643643698027, 2, [(2, 1), (11, 1), (19, 1), (353, 1), (11139269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_353
    · exact prime_11139269
  · decide +kernel

theorem prime_1643643698447 : Nat.Prime 1643643698447 := by
  apply nodeValid_prime [2, 17, 31, 73, 21362113] ⟨1643643698447, 5, [(2, 1), (17, 1), (31, 1), (73, 1), (21362113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_73
    · exact prime_21362113
  · decide +kernel

theorem prime_1643643763121 : Nat.Prime 1643643763121 := by
  apply nodeValid_prime [2, 5, 19, 367, 2946443] ⟨1643643763121, 3, [(2, 4), (5, 1), (19, 1), (367, 1), (2946443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_367
    · exact prime_2946443
  · decide +kernel

theorem prime_1645469371153 : Nat.Prime 1645469371153 := by
  apply nodeValid_prime [2, 3, 101, 113137333] ⟨1645469371153, 5, [(2, 4), (3, 2), (101, 1), (113137333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_113137333
  · decide +kernel

theorem prime_1645469393671 : Nat.Prime 1645469393671 := by
  apply nodeValid_prime [2, 3, 5, 35863, 509801] ⟨1645469393671, 3, [(2, 1), (3, 2), (5, 1), (35863, 1), (509801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35863
    · exact prime_509801
  · decide +kernel

theorem prime_1645469393801 : Nat.Prime 1645469393801 := by
  apply nodeValid_prime [2, 5, 8227346969] ⟨1645469393801, 3, [(2, 3), (5, 2), (8227346969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8227346969
  · decide +kernel

theorem prime_1647296347259 : Nat.Prime 1647296347259 := by
  apply nodeValid_prime [2, 89, 691, 13392871] ⟨1647296347259, 2, [(2, 1), (89, 1), (691, 1), (13392871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_691
    · exact prime_13392871
  · decide +kernel

theorem prime_1647296361079 : Nat.Prime 1647296361079 := by
  apply nodeValid_prime [2, 3, 691, 397321843] ⟨1647296361079, 3, [(2, 1), (3, 1), (691, 1), (397321843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_397321843
  · decide +kernel

theorem prime_1647296361757 : Nat.Prime 1647296361757 := by
  apply nodeValid_prime [2, 3, 1319, 34691609] ⟨1647296361757, 2, [(2, 2), (3, 2), (1319, 1), (34691609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1319
    · exact prime_34691609
  · decide +kernel

theorem prime_1649124687557 : Nat.Prime 1649124687557 := by
  apply nodeValid_prime [2, 23, 33073, 541991] ⟨1649124687557, 2, [(2, 2), (23, 1), (33073, 1), (541991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_33073
    · exact prime_541991
  · decide +kernel

theorem prime_1649124766057 : Nat.Prime 1649124766057 := by
  apply nodeValid_prime [2, 3, 97, 1499, 472573] ⟨1649124766057, 5, [(2, 3), (3, 1), (97, 1), (1499, 1), (472573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1499
    · exact prime_472573
  · decide +kernel

theorem prime_1649124766711 : Nat.Prime 1649124766711 := by
  apply nodeValid_prime [2, 3, 5, 18323608519] ⟨1649124766711, 3, [(2, 1), (3, 2), (5, 1), (18323608519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18323608519
  · decide +kernel

theorem prime_1650954385217 : Nat.Prime 1650954385217 := by
  apply nodeValid_prime [2, 19, 1357692751] ⟨1650954385217, 5, [(2, 6), (19, 1), (1357692751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1357692751
  · decide +kernel

theorem prime_1650954385393 : Nat.Prime 1650954385393 := by
  apply nodeValid_prime [2, 3, 13, 131, 751, 26893] ⟨1650954385393, 5, [(2, 4), (3, 1), (13, 1), (131, 1), (751, 1), (26893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_131
    · exact prime_751
    · exact prime_26893
  · decide +kernel

theorem prime_1650954390247 : Nat.Prime 1650954390247 := by
  apply nodeValid_prime [2, 3, 7, 139, 293, 35747] ⟨1650954390247, 3, [(2, 1), (3, 4), (7, 1), (139, 1), (293, 1), (35747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
    · exact prime_293
    · exact prime_35747
  · decide +kernel

theorem prime_1652785369981 : Nat.Prime 1652785369981 := by
  apply nodeValid_prime [2, 3, 5, 27546422833] ⟨1652785369981, 2, [(2, 2), (3, 1), (5, 1), (27546422833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27546422833
  · decide +kernel

theorem prime_1652785370543 : Nat.Prime 1652785370543 := by
  apply nodeValid_prime [2, 71971, 11482301] ⟨1652785370543, 5, [(2, 1), (71971, 1), (11482301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71971
    · exact prime_11482301
  · decide +kernel

theorem prime_1652785468211 : Nat.Prime 1652785468211 := by
  apply nodeValid_prime [2, 5, 165278546821] ⟨1652785468211, 6, [(2, 1), (5, 1), (165278546821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_165278546821
  · decide +kernel

theorem prime_1654617930697 : Nat.Prime 1654617930697 := by
  apply nodeValid_prime [2, 3, 22980804593] ⟨1654617930697, 5, [(2, 3), (3, 2), (22980804593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22980804593
  · decide +kernel

theorem prime_1654617947597 : Nat.Prime 1654617947597 := by
  apply nodeValid_prime [2, 25819, 16021321] ⟨1654617947597, 2, [(2, 2), (25819, 1), (16021321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_25819
    · exact prime_16021321
  · decide +kernel

theorem prime_1654617948959 : Nat.Prime 1654617948959 := by
  apply nodeValid_prime [2, 13, 4987, 12761009] ⟨1654617948959, 17, [(2, 1), (13, 1), (4987, 1), (12761009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4987
    · exact prime_12761009
  · decide +kernel

theorem prime_1656451777087 : Nat.Prime 1656451777087 := by
  apply nodeValid_prime [2, 3, 23, 1333697083] ⟨1656451777087, 3, [(2, 1), (3, 3), (23, 1), (1333697083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1333697083
  · decide +kernel

theorem prime_1656451879843 : Nat.Prime 1656451879843 := by
  apply nodeValid_prime [2, 3, 41, 349, 677, 28499] ⟨1656451879843, 2, [(2, 1), (3, 1), (41, 1), (349, 1), (677, 1), (28499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_349
    · exact prime_677
    · exact prime_28499
  · decide +kernel

theorem prime_1656451880767 : Nat.Prime 1656451880767 := by
  apply nodeValid_prime [2, 3, 43, 713372903] ⟨1656451880767, 6, [(2, 1), (3, 3), (43, 1), (713372903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_713372903
  · decide +kernel

theorem prime_1658287003067 : Nat.Prime 1658287003067 := by
  apply nodeValid_prime [2, 17, 59, 389, 2125099] ⟨1658287003067, 2, [(2, 1), (17, 1), (59, 1), (389, 1), (2125099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
    · exact prime_389
    · exact prime_2125099
  · decide +kernel

theorem prime_1658287037921 : Nat.Prime 1658287037921 := by
  apply nodeValid_prime [2, 5, 547, 18947521] ⟨1658287037921, 3, [(2, 5), (5, 1), (547, 1), (18947521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_547
    · exact prime_18947521
  · decide +kernel

theorem prime_1658287038883 : Nat.Prime 1658287038883 := by
  apply nodeValid_prime [2, 3, 353, 782949499] ⟨1658287038883, 2, [(2, 1), (3, 1), (353, 1), (782949499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353
    · exact prime_782949499
  · decide +kernel

theorem prime_1660123605113 : Nat.Prime 1660123605113 := by
  apply nodeValid_prime [2, 7, 103, 5273, 54583] ⟨1660123605113, 3, [(2, 3), (7, 1), (103, 1), (5273, 1), (54583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_103
    · exact prime_5273
    · exact prime_54583
  · decide +kernel

theorem prime_1660123639021 : Nat.Prime 1660123639021 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 37, 9711733] ⟨1660123639021, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (37, 1), (9711733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_37
    · exact prime_9711733
  · decide +kernel

theorem prime_1660123639231 : Nat.Prime 1660123639231 := by
  apply nodeValid_prime [2, 3, 5, 7, 2081, 77527] ⟨1660123639231, 3, [(2, 1), (3, 1), (5, 1), (7, 3), (2081, 1), (77527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2081
    · exact prime_77527
  · decide +kernel

theorem prime_1661961579697 : Nat.Prime 1661961579697 := by
  apply nodeValid_prime [2, 3, 11, 131, 787, 10177] ⟨1661961579697, 5, [(2, 4), (3, 2), (11, 1), (131, 1), (787, 1), (10177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
    · exact prime_787
    · exact prime_10177
  · decide +kernel

theorem prime_1661961580183 : Nat.Prime 1661961580183 := by
  apply nodeValid_prime [2, 3, 163, 281, 2015833] ⟨1661961580183, 3, [(2, 1), (3, 2), (163, 1), (281, 1), (2015833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_281
    · exact prime_2015833
  · decide +kernel

theorem prime_1661961583873 : Nat.Prime 1661961583873 := by
  apply nodeValid_prime [2, 3, 71, 97, 34913] ⟨1661961583873, 7, [(2, 8), (3, 3), (71, 1), (97, 1), (34913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_97
    · exact prime_34913
  · decide +kernel

theorem prime_1663800900323 : Nat.Prime 1663800900323 := by
  apply nodeValid_prime [2, 11, 19, 1009, 3944881] ⟨1663800900323, 2, [(2, 1), (11, 1), (19, 1), (1009, 1), (3944881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1009
    · exact prime_3944881
  · decide +kernel

theorem prime_1663800902861 : Nat.Prime 1663800902861 := by
  apply nodeValid_prime [2, 5, 157, 529872899] ⟨1663800902861, 2, [(2, 2), (5, 1), (157, 1), (529872899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_529872899
  · decide +kernel

theorem prime_1663800941459 : Nat.Prime 1663800941459 := by
  apply nodeValid_prime [2, 409, 2033986481] ⟨1663800941459, 2, [(2, 1), (409, 1), (2033986481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_2033986481
  · decide +kernel

theorem prime_1665641650747 : Nat.Prime 1665641650747 := by
  apply nodeValid_prime [2, 3, 1153, 240769247] ⟨1665641650747, 3, [(2, 1), (3, 1), (1153, 1), (240769247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1153
    · exact prime_240769247
  · decide +kernel

theorem prime_1665641651143 : Nat.Prime 1665641651143 := by
  apply nodeValid_prime [2, 3, 7, 5665447793] ⟨1665641651143, 5, [(2, 1), (3, 1), (7, 2), (5665447793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5665447793
  · decide +kernel

theorem prime_1665641676497 : Nat.Prime 1665641676497 := by
  apply nodeValid_prime [2, 7, 37, 163, 521, 4733] ⟨1665641676497, 3, [(2, 4), (7, 1), (37, 1), (163, 1), (521, 1), (4733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_163
    · exact prime_521
    · exact prime_4733
  · decide +kernel

theorem prime_1667483786273 : Nat.Prime 1667483786273 := by
  apply nodeValid_prime [2, 43, 9907, 122321] ⟨1667483786273, 3, [(2, 5), (43, 1), (9907, 1), (122321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_9907
    · exact prime_122321
  · decide +kernel

theorem prime_1667483985949 : Nat.Prime 1667483985949 := by
  apply nodeValid_prime [2, 3, 11, 1148404949] ⟨1667483985949, 6, [(2, 2), (3, 1), (11, 2), (1148404949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1148404949
  · decide +kernel

theorem prime_1667483986433 : Nat.Prime 1667483986433 := by
  apply nodeValid_prime [2, 11, 29, 59, 15731] ⟨1667483986433, 3, [(2, 9), (11, 2), (29, 1), (59, 1), (15731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_59
    · exact prime_15731
  · decide +kernel

theorem prime_1669327282253 : Nat.Prime 1669327282253 := by
  apply nodeValid_prime [2, 7, 59618831509] ⟨1669327282253, 2, [(2, 2), (7, 1), (59618831509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59618831509
  · decide +kernel

theorem prime_1669327318721 : Nat.Prime 1669327318721 := by
  apply nodeValid_prime [2, 5, 23, 37, 6130021] ⟨1669327318721, 3, [(2, 6), (5, 1), (23, 1), (37, 1), (6130021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_6130021
  · decide +kernel

theorem prime_1669327319813 : Nat.Prime 1669327319813 := by
  apply nodeValid_prime [2, 29, 14390752757] ⟨1669327319813, 2, [(2, 2), (29, 1), (14390752757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_14390752757
  · decide +kernel

theorem prime_1671172164359 : Nat.Prime 1671172164359 := by
  apply nodeValid_prime [2, 97, 6871, 1253717] ⟨1671172164359, 11, [(2, 1), (97, 1), (6871, 1), (1253717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_6871
    · exact prime_1253717
  · decide +kernel

theorem prime_1671172164533 : Nat.Prime 1671172164533 := by
  apply nodeValid_prime [2, 13, 32137926241] ⟨1671172164533, 2, [(2, 2), (13, 1), (32137926241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_32137926241
  · decide +kernel

theorem prime_1671172165321 : Nat.Prime 1671172165321 := by
  apply nodeValid_prime [2, 3, 5, 7, 1989490673] ⟨1671172165321, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (1989490673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1989490673
  · decide +kernel

theorem prime_1673018422381 : Nat.Prime 1673018422381 := by
  apply nodeValid_prime [2, 3, 5, 9294546791] ⟨1673018422381, 7, [(2, 2), (3, 2), (5, 1), (9294546791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9294546791
  · decide +kernel

theorem prime_1673018425453 : Nat.Prime 1673018425453 := by
  apply nodeValid_prime [2, 3, 11, 17, 191, 3903413] ⟨1673018425453, 5, [(2, 2), (3, 1), (11, 1), (17, 1), (191, 1), (3903413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_191
    · exact prime_3903413
  · decide +kernel

theorem prime_1673018427851 : Nat.Prime 1673018427851 := by
  apply nodeValid_prime [2, 5, 7, 11, 13109, 33149] ⟨1673018427851, 7, [(2, 1), (5, 2), (7, 1), (11, 1), (13109, 1), (33149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13109
    · exact prime_33149
  · decide +kernel

theorem prime_1674866069297 : Nat.Prime 1674866069297 := by
  apply nodeValid_prime [2, 7, 17, 16421, 53569] ⟨1674866069297, 3, [(2, 4), (7, 1), (17, 1), (16421, 1), (53569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_16421
    · exact prime_53569
  · decide +kernel

theorem prime_1674866123921 : Nat.Prime 1674866123921 := by
  apply nodeValid_prime [2, 5, 11, 1399, 1360441] ⟨1674866123921, 3, [(2, 4), (5, 1), (11, 1), (1399, 1), (1360441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1399
    · exact prime_1360441
  · decide +kernel

theorem prime_1674866124623 : Nat.Prime 1674866124623 := by
  apply nodeValid_prime [2, 837433062311] ⟨1674866124623, 5, [(2, 1), (837433062311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_837433062311
  · decide +kernel

theorem prime_1676715089527 : Nat.Prime 1676715089527 := by
  apply nodeValid_prime [2, 3, 93150838307] ⟨1676715089527, 5, [(2, 1), (3, 2), (93150838307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_93150838307
  · decide +kernel

theorem prime_1676715122609 : Nat.Prime 1676715122609 := by
  apply nodeValid_prime [2, 104794695163] ⟨1676715122609, 3, [(2, 4), (104794695163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_104794695163
  · decide +kernel

theorem prime_1676715122767 : Nat.Prime 1676715122767 := by
  apply nodeValid_prime [2, 3, 29, 197, 1637, 29881] ⟨1676715122767, 3, [(2, 1), (3, 1), (29, 1), (197, 1), (1637, 1), (29881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_197
    · exact prime_1637
    · exact prime_29881
  · decide +kernel

theorem prime_1678565490269 : Nat.Prime 1678565490269 := by
  apply nodeValid_prime [2, 379, 1107233173] ⟨1678565490269, 2, [(2, 2), (379, 1), (1107233173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_1107233173
  · decide +kernel

theorem prime_1678565491451 : Nat.Prime 1678565491451 := by
  apply nodeValid_prime [2, 5, 9479, 3541651] ⟨1678565491451, 2, [(2, 1), (5, 2), (9479, 1), (3541651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9479
    · exact prime_3541651
  · decide +kernel

theorem prime_1678565499899 : Nat.Prime 1678565499899 := by
  apply nodeValid_prime [2, 7, 29, 113, 1621, 22571] ⟨1678565499899, 2, [(2, 1), (7, 1), (29, 1), (113, 1), (1621, 1), (22571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_113
    · exact prime_1621
    · exact prime_22571
  · decide +kernel

theorem prime_1680417295691 : Nat.Prime 1680417295691 := by
  apply nodeValid_prime [2, 5, 7, 89, 239, 1128577] ⟨1680417295691, 2, [(2, 1), (5, 1), (7, 1), (89, 1), (239, 1), (1128577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_89
    · exact prime_239
    · exact prime_1128577
  · decide +kernel

theorem prime_1680417296497 : Nat.Prime 1680417296497 := by
  apply nodeValid_prime [2, 3, 9533, 408041] ⟨1680417296497, 5, [(2, 4), (3, 3), (9533, 1), (408041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9533
    · exact prime_408041
  · decide +kernel

theorem prime_1680417297371 : Nat.Prime 1680417297371 := by
  apply nodeValid_prime [2, 5, 7, 79, 303872929] ⟨1680417297371, 2, [(2, 1), (5, 1), (7, 1), (79, 1), (303872929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
    · exact prime_303872929
  · decide +kernel

end Sude.Lucas.Generated
