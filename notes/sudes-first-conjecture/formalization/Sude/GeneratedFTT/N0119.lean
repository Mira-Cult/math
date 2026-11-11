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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0103

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7547 : Nat.Prime 7547 := by
  apply nodeValid_prime [2, 7, 11] ⟨7547, 2, [(2, 1), (7, 3), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_13903 : Nat.Prime 13903 := by
  apply nodeValid_prime [2, 3, 7, 331] ⟨13903, 3, [(2, 1), (3, 1), (7, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_331
  · decide +kernel

theorem prime_14633 : Nat.Prime 14633 := by
  apply nodeValid_prime [2, 31, 59] ⟨14633, 3, [(2, 3), (31, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_59
  · decide +kernel

theorem prime_15959 : Nat.Prime 15959 := by
  apply nodeValid_prime [2, 79, 101] ⟨15959, 11, [(2, 1), (79, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_101
  · decide +kernel

theorem prime_19433 : Nat.Prime 19433 := by
  apply nodeValid_prime [2, 7, 347] ⟨19433, 3, [(2, 3), (7, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_347
  · decide +kernel

theorem prime_19457 : Nat.Prime 19457 := by
  apply nodeValid_prime [2, 19] ⟨19457, 3, [(2, 10), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19
  · decide +kernel

theorem prime_21377 : Nat.Prime 21377 := by
  apply nodeValid_prime [2, 167] ⟨21377, 3, [(2, 7), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_167
  · decide +kernel

theorem prime_31891 : Nat.Prime 31891 := by
  apply nodeValid_prime [2, 3, 5, 1063] ⟨31891, 2, [(2, 1), (3, 1), (5, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1063
  · decide +kernel

theorem prime_36293 : Nat.Prime 36293 := by
  apply nodeValid_prime [2, 43, 211] ⟨36293, 2, [(2, 2), (43, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_211
  · decide +kernel

theorem prime_37957 : Nat.Prime 37957 := by
  apply nodeValid_prime [2, 3, 3163] ⟨37957, 2, [(2, 2), (3, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3163
  · decide +kernel

theorem prime_40343 : Nat.Prime 40343 := by
  apply nodeValid_prime [2, 23, 877] ⟨40343, 5, [(2, 1), (23, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_877
  · decide +kernel

theorem prime_41011 : Nat.Prime 41011 := by
  apply nodeValid_prime [2, 3, 5, 1367] ⟨41011, 2, [(2, 1), (3, 1), (5, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1367
  · decide +kernel

theorem prime_42089 : Nat.Prime 42089 := by
  apply nodeValid_prime [2, 5261] ⟨42089, 3, [(2, 3), (5261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5261
  · decide +kernel

theorem prime_47819 : Nat.Prime 47819 := by
  apply nodeValid_prime [2, 23909] ⟨47819, 2, [(2, 1), (23909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23909
  · decide +kernel

theorem prime_51137 : Nat.Prime 51137 := by
  apply nodeValid_prime [2, 17, 47] ⟨51137, 3, [(2, 6), (17, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_52289 : Nat.Prime 52289 := by
  apply nodeValid_prime [2, 19, 43] ⟨52289, 3, [(2, 6), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_56599 : Nat.Prime 56599 := by
  apply nodeValid_prime [2, 3, 9433] ⟨56599, 3, [(2, 1), (3, 1), (9433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9433
  · decide +kernel

theorem prime_57047 : Nat.Prime 57047 := by
  apply nodeValid_prime [2, 11, 2593] ⟨57047, 7, [(2, 1), (11, 1), (2593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2593
  · decide +kernel

theorem prime_66109 : Nat.Prime 66109 := by
  apply nodeValid_prime [2, 3, 7, 787] ⟨66109, 2, [(2, 2), (3, 1), (7, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_787
  · decide +kernel

theorem prime_66373 : Nat.Prime 66373 := by
  apply nodeValid_prime [2, 3, 5531] ⟨66373, 2, [(2, 2), (3, 1), (5531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5531
  · decide +kernel

theorem prime_79349 : Nat.Prime 79349 := by
  apply nodeValid_prime [2, 83, 239] ⟨79349, 2, [(2, 2), (83, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_239
  · decide +kernel

theorem prime_93463 : Nat.Prime 93463 := by
  apply nodeValid_prime [2, 3, 37, 421] ⟨93463, 3, [(2, 1), (3, 1), (37, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_421
  · decide +kernel

theorem prime_95891 : Nat.Prime 95891 := by
  apply nodeValid_prime [2, 5, 43, 223] ⟨95891, 2, [(2, 1), (5, 1), (43, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_223
  · decide +kernel

theorem prime_100019 : Nat.Prime 100019 := by
  apply nodeValid_prime [2, 43, 1163] ⟨100019, 2, [(2, 1), (43, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1163
  · decide +kernel

theorem prime_104579 : Nat.Prime 104579 := by
  apply nodeValid_prime [2, 52289] ⟨104579, 2, [(2, 1), (52289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_52289
  · decide +kernel

theorem prime_138937 : Nat.Prime 138937 := by
  apply nodeValid_prime [2, 3, 7, 827] ⟨138937, 5, [(2, 3), (3, 1), (7, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_827
  · decide +kernel

theorem prime_140449 : Nat.Prime 140449 := by
  apply nodeValid_prime [2, 3, 7, 11, 19] ⟨140449, 17, [(2, 5), (3, 1), (7, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_146299 : Nat.Prime 146299 := by
  apply nodeValid_prime [2, 3, 37, 659] ⟨146299, 2, [(2, 1), (3, 1), (37, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_659
  · decide +kernel

theorem prime_159473 : Nat.Prime 159473 := by
  apply nodeValid_prime [2, 9967] ⟨159473, 3, [(2, 4), (9967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9967
  · decide +kernel

theorem prime_171529 : Nat.Prime 171529 := by
  apply nodeValid_prime [2, 3, 7, 1021] ⟨171529, 11, [(2, 3), (3, 1), (7, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1021
  · decide +kernel

theorem prime_177539 : Nat.Prime 177539 := by
  apply nodeValid_prime [2, 29, 3061] ⟨177539, 2, [(2, 1), (29, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3061
  · decide +kernel

theorem prime_186947 : Nat.Prime 186947 := by
  apply nodeValid_prime [2, 211, 443] ⟨186947, 2, [(2, 1), (211, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_443
  · decide +kernel

theorem prime_188729 : Nat.Prime 188729 := by
  apply nodeValid_prime [2, 31, 761] ⟨188729, 3, [(2, 3), (31, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_761
  · decide +kernel

theorem prime_196117 : Nat.Prime 196117 := by
  apply nodeValid_prime [2, 3, 59, 277] ⟨196117, 2, [(2, 2), (3, 1), (59, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_277
  · decide +kernel

theorem prime_220357 : Nat.Prime 220357 := by
  apply nodeValid_prime [2, 3, 6121] ⟨220357, 5, [(2, 2), (3, 2), (6121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6121
  · decide +kernel

theorem prime_237929 : Nat.Prime 237929 := by
  apply nodeValid_prime [2, 29741] ⟨237929, 3, [(2, 3), (29741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29741
  · decide +kernel

theorem prime_264437 : Nat.Prime 264437 := by
  apply nodeValid_prime [2, 66109] ⟨264437, 2, [(2, 2), (66109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_66109
  · decide +kernel

theorem prime_265493 : Nat.Prime 265493 := by
  apply nodeValid_prime [2, 66373] ⟨265493, 2, [(2, 2), (66373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_66373
  · decide +kernel

theorem prime_268993 : Nat.Prime 268993 := by
  apply nodeValid_prime [2, 3, 467] ⟨268993, 5, [(2, 6), (3, 2), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
  · decide +kernel

theorem prime_283601 : Nat.Prime 283601 := by
  apply nodeValid_prime [2, 5, 709] ⟨283601, 3, [(2, 4), (5, 2), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_709
  · decide +kernel

theorem prime_284659 : Nat.Prime 284659 := by
  apply nodeValid_prime [2, 3, 11, 19, 227] ⟨284659, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_340849 : Nat.Prime 340849 := by
  apply nodeValid_prime [2, 3, 263] ⟨340849, 13, [(2, 4), (3, 4), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
  · decide +kernel

theorem prime_377459 : Nat.Prime 377459 := by
  apply nodeValid_prime [2, 188729] ⟨377459, 2, [(2, 1), (188729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_188729
  · decide +kernel

theorem prime_379501 : Nat.Prime 379501 := by
  apply nodeValid_prime [2, 3, 5, 11, 23] ⟨379501, 13, [(2, 2), (3, 1), (5, 3), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_379571 : Nat.Prime 379571 := by
  apply nodeValid_prime [2, 5, 37957] ⟨379571, 2, [(2, 1), (5, 1), (37957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37957
  · decide +kernel

theorem prime_447133 : Nat.Prime 447133 := by
  apply nodeValid_prime [2, 3, 7, 5323] ⟨447133, 2, [(2, 2), (3, 1), (7, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5323
  · decide +kernel

theorem prime_452807 : Nat.Prime 452807 := by
  apply nodeValid_prime [2, 29, 37, 211] ⟨452807, 5, [(2, 1), (29, 1), (37, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_211
  · decide +kernel

theorem prime_475859 : Nat.Prime 475859 := by
  apply nodeValid_prime [2, 237929] ⟨475859, 2, [(2, 1), (237929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_237929
  · decide +kernel

theorem prime_476513 : Nat.Prime 476513 := by
  apply nodeValid_prime [2, 14891] ⟨476513, 3, [(2, 5), (14891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14891
  · decide +kernel

theorem prime_508103 : Nat.Prime 508103 := by
  apply nodeValid_prime [2, 7, 36293] ⟨508103, 5, [(2, 1), (7, 1), (36293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_36293
  · decide +kernel

theorem prime_510287 : Nat.Prime 510287 := by
  apply nodeValid_prime [2, 7, 41, 127] ⟨510287, 7, [(2, 1), (7, 2), (41, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_127
  · decide +kernel

theorem prime_539663 : Nat.Prime 539663 := by
  apply nodeValid_prime [2, 239, 1129] ⟨539663, 5, [(2, 1), (239, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_1129
  · decide +kernel

theorem prime_561797 : Nat.Prime 561797 := by
  apply nodeValid_prime [2, 140449] ⟨561797, 2, [(2, 2), (140449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_140449
  · decide +kernel

theorem prime_581149 : Nat.Prime 581149 := by
  apply nodeValid_prime [2, 3, 5381] ⟨581149, 2, [(2, 2), (3, 3), (5381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5381
  · decide +kernel

theorem prime_657793 : Nat.Prime 657793 := by
  apply nodeValid_prime [2, 3, 571] ⟨657793, 5, [(2, 7), (3, 2), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
  · decide +kernel

theorem prime_678199 : Nat.Prime 678199 := by
  apply nodeValid_prime [2, 3, 17, 61, 109] ⟨678199, 6, [(2, 1), (3, 1), (17, 1), (61, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_109
  · decide +kernel

theorem prime_682489 : Nat.Prime 682489 := by
  apply nodeValid_prime [2, 3, 9479] ⟨682489, 14, [(2, 3), (3, 2), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9479
  · decide +kernel

theorem prime_762973 : Nat.Prime 762973 := by
  apply nodeValid_prime [2, 3, 7, 31, 293] ⟨762973, 2, [(2, 2), (3, 1), (7, 1), (31, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_293
  · decide +kernel

theorem prime_1090939 : Nat.Prime 1090939 := by
  apply nodeValid_prime [2, 3, 173, 1051] ⟨1090939, 2, [(2, 1), (3, 1), (173, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_1051
  · decide +kernel

theorem prime_1214933 : Nat.Prime 1214933 := by
  apply nodeValid_prime [2, 37, 8209] ⟨1214933, 2, [(2, 2), (37, 1), (8209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_8209
  · decide +kernel

theorem prime_1561727 : Nat.Prime 1561727 := by
  apply nodeValid_prime [2, 277, 2819] ⟨1561727, 5, [(2, 1), (277, 1), (2819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_2819
  · decide +kernel

theorem prime_1586623 : Nat.Prime 1586623 := by
  apply nodeValid_prime [2, 3, 264437] ⟨1586623, 3, [(2, 1), (3, 1), (264437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_264437
  · decide +kernel

theorem prime_2058841 : Nat.Prime 2058841 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 43] ⟨2058841, 23, [(2, 3), (3, 2), (5, 1), (7, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_2102857 : Nat.Prime 2102857 := by
  apply nodeValid_prime [2, 3, 7, 12517] ⟨2102857, 5, [(2, 3), (3, 1), (7, 1), (12517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12517
  · decide +kernel

theorem prime_2103007 : Nat.Prime 2103007 := by
  apply nodeValid_prime [2, 3, 37, 9473] ⟨2103007, 3, [(2, 1), (3, 1), (37, 1), (9473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_9473
  · decide +kernel

theorem prime_2293111 : Nat.Prime 2293111 := by
  apply nodeValid_prime [2, 3, 5, 19, 149] ⟨2293111, 15, [(2, 1), (3, 4), (5, 1), (19, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_149
  · decide +kernel

theorem prime_2534867 : Nat.Prime 2534867 := by
  apply nodeValid_prime [2, 19, 41, 1627] ⟨2534867, 2, [(2, 1), (19, 1), (41, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_1627
  · decide +kernel

theorem prime_2729539 : Nat.Prime 2729539 := by
  apply nodeValid_prime [2, 3, 7, 29, 83] ⟨2729539, 3, [(2, 1), (3, 4), (7, 1), (29, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_83
  · decide +kernel

theorem prime_3016747 : Nat.Prime 3016747 := by
  apply nodeValid_prime [2, 3, 167597] ⟨3016747, 3, [(2, 1), (3, 2), (167597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167597
  · decide +kernel

theorem prime_3238181 : Nat.Prime 3238181 := by
  apply nodeValid_prime [2, 5, 11, 41, 359] ⟨3238181, 2, [(2, 2), (5, 1), (11, 1), (41, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_359
  · decide +kernel

theorem prime_3624319 : Nat.Prime 3624319 := by
  apply nodeValid_prime [2, 3, 41, 1637] ⟨3624319, 3, [(2, 1), (3, 3), (41, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1637
  · decide +kernel

theorem prime_3695773 : Nat.Prime 3695773 := by
  apply nodeValid_prime [2, 3, 131, 2351] ⟨3695773, 5, [(2, 2), (3, 1), (131, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_2351
  · decide +kernel

theorem prime_5326171 : Nat.Prime 5326171 := by
  apply nodeValid_prime [2, 3, 5, 177539] ⟨5326171, 2, [(2, 1), (3, 1), (5, 1), (177539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_177539
  · decide +kernel

theorem prime_5424457 : Nat.Prime 5424457 := by
  apply nodeValid_prime [2, 3, 79, 2861] ⟨5424457, 19, [(2, 3), (3, 1), (79, 1), (2861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_2861
  · decide +kernel

theorem prime_6346493 : Nat.Prime 6346493 := by
  apply nodeValid_prime [2, 1586623] ⟨6346493, 2, [(2, 2), (1586623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1586623
  · decide +kernel

theorem prime_10792211 : Nat.Prime 10792211 := by
  apply nodeValid_prime [2, 5, 11, 13, 7547] ⟨10792211, 2, [(2, 1), (5, 1), (11, 1), (13, 1), (7547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_7547
  · decide +kernel

theorem prime_12226457 : Nat.Prime 12226457 := by
  apply nodeValid_prime [2, 11, 138937] ⟨12226457, 3, [(2, 3), (11, 1), (138937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_138937
  · decide +kernel

theorem prime_12299153 : Nat.Prime 12299153 := by
  apply nodeValid_prime [2, 337, 2281] ⟨12299153, 3, [(2, 4), (337, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_2281
  · decide +kernel

theorem prime_22852513 : Nat.Prime 22852513 := by
  apply nodeValid_prime [2, 3, 79349] ⟨22852513, 5, [(2, 5), (3, 2), (79349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79349
  · decide +kernel

theorem prime_24788303 : Nat.Prime 24788303 := by
  apply nodeValid_prime [2, 7, 11, 14633] ⟨24788303, 10, [(2, 1), (7, 1), (11, 2), (14633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_14633
  · decide +kernel

theorem prime_29141803 : Nat.Prime 29141803 := by
  apply nodeValid_prime [2, 3, 539663] ⟨29141803, 2, [(2, 1), (3, 3), (539663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_539663
  · decide +kernel

theorem prime_34970323 : Nat.Prime 34970323 := by
  apply nodeValid_prime [2, 3, 389, 14983] ⟨34970323, 2, [(2, 1), (3, 1), (389, 1), (14983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_14983
  · decide +kernel

theorem prime_42799069 : Nat.Prime 42799069 := by
  apply nodeValid_prime [2, 3, 13, 109, 839] ⟨42799069, 6, [(2, 2), (3, 2), (13, 1), (109, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_109
    · exact prime_839
  · decide +kernel

theorem prime_52945037 : Nat.Prime 52945037 := by
  apply nodeValid_prime [2, 83, 159473] ⟨52945037, 2, [(2, 2), (83, 1), (159473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_159473
  · decide +kernel

theorem prime_60049859 : Nat.Prime 60049859 := by
  apply nodeValid_prime [2, 11, 2729539] ⟨60049859, 7, [(2, 1), (11, 1), (2729539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2729539
  · decide +kernel

theorem prime_64489471 : Nat.Prime 64489471 := by
  apply nodeValid_prime [2, 3, 5, 23, 93463] ⟨64489471, 7, [(2, 1), (3, 1), (5, 1), (23, 1), (93463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_93463
  · decide +kernel

theorem prime_74381051 : Nat.Prime 74381051 := by
  apply nodeValid_prime [2, 5, 107, 13903] ⟨74381051, 2, [(2, 1), (5, 2), (107, 1), (13903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_13903
  · decide +kernel

theorem prime_113751719 : Nat.Prime 113751719 := by
  apply nodeValid_prime [2, 997, 57047] ⟨113751719, 7, [(2, 1), (997, 1), (57047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_997
    · exact prime_57047
  · decide +kernel

theorem prime_120099719 : Nat.Prime 120099719 := by
  apply nodeValid_prime [2, 60049859] ⟨120099719, 11, [(2, 1), (60049859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60049859
  · decide +kernel

theorem prime_123530461 : Nat.Prime 123530461 := by
  apply nodeValid_prime [2, 3, 5, 2058841] ⟨123530461, 2, [(2, 2), (3, 1), (5, 1), (2058841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2058841
  · decide +kernel

theorem prime_129588517 : Nat.Prime 129588517 := by
  apply nodeValid_prime [2, 3, 263, 13687] ⟨129588517, 2, [(2, 2), (3, 2), (263, 1), (13687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_13687
  · decide +kernel

theorem prime_159233029 : Nat.Prime 159233029 := by
  apply nodeValid_prime [2, 3, 751, 17669] ⟨159233029, 2, [(2, 2), (3, 1), (751, 1), (17669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_751
    · exact prime_17669
  · decide +kernel

theorem prime_237084553 : Nat.Prime 237084553 := by
  apply nodeValid_prime [2, 3, 23, 61, 2347] ⟨237084553, 5, [(2, 3), (3, 2), (23, 1), (61, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_61
    · exact prime_2347
  · decide +kernel

theorem prime_293879941 : Nat.Prime 293879941 := by
  apply nodeValid_prime [2, 3, 5, 1597, 3067] ⟨293879941, 2, [(2, 2), (3, 1), (5, 1), (1597, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1597
    · exact prime_3067
  · decide +kernel

theorem prime_352246231 : Nat.Prime 352246231 := by
  apply nodeValid_prime [2, 3, 5, 7, 193, 2897] ⟨352246231, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (193, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_193
    · exact prime_2897
  · decide +kernel

theorem prime_363832697 : Nat.Prime 363832697 := by
  apply nodeValid_prime [2, 2963, 15349] ⟨363832697, 3, [(2, 3), (2963, 1), (15349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2963
    · exact prime_15349
  · decide +kernel

theorem prime_432787697 : Nat.Prime 432787697 := by
  apply nodeValid_prime [2, 11, 223, 11027] ⟨432787697, 3, [(2, 4), (11, 1), (223, 1), (11027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_223
    · exact prime_11027
  · decide +kernel

theorem prime_472199059 : Nat.Prime 472199059 := by
  apply nodeValid_prime [2, 3, 19, 51137] ⟨472199059, 14, [(2, 1), (3, 5), (19, 1), (51137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_51137
  · decide +kernel

theorem prime_492880559 : Nat.Prime 492880559 := by
  apply nodeValid_prime [2, 17, 19, 762973] ⟨492880559, 13, [(2, 1), (17, 1), (19, 1), (762973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_762973
  · decide +kernel

theorem prime_638472389 : Nat.Prime 638472389 := by
  apply nodeValid_prime [2, 9839, 16223] ⟨638472389, 2, [(2, 2), (9839, 1), (16223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9839
    · exact prime_16223
  · decide +kernel

theorem prime_641159839 : Nat.Prime 641159839 := by
  apply nodeValid_prime [2, 3, 11, 3238181] ⟨641159839, 3, [(2, 1), (3, 2), (11, 1), (3238181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3238181
  · decide +kernel

theorem prime_774090439 : Nat.Prime 774090439 := by
  apply nodeValid_prime [2, 3, 11, 19, 23, 26839] ⟨774090439, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (23, 1), (26839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_23
    · exact prime_26839
  · decide +kernel

theorem prime_1165672121 : Nat.Prime 1165672121 := by
  apply nodeValid_prime [2, 5, 29141803] ⟨1165672121, 3, [(2, 3), (5, 1), (29141803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29141803
  · decide +kernel

theorem prime_1210072349 : Nat.Prime 1210072349 := by
  apply nodeValid_prime [2, 797, 379571] ⟨1210072349, 2, [(2, 2), (797, 1), (379571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_797
    · exact prime_379571
  · decide +kernel

theorem prime_2158078163 : Nat.Prime 2158078163 := by
  apply nodeValid_prime [2, 2383, 452807] ⟨2158078163, 2, [(2, 1), (2383, 1), (452807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2383
    · exact prime_452807
  · decide +kernel

theorem prime_2617250959 : Nat.Prime 2617250959 := by
  apply nodeValid_prime [2, 3, 7, 367, 56599] ⟨2617250959, 3, [(2, 1), (3, 2), (7, 1), (367, 1), (56599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_367
    · exact prime_56599
  · decide +kernel

theorem prime_3844930399 : Nat.Prime 3844930399 := by
  apply nodeValid_prime [2, 3, 43, 149, 100019] ⟨3844930399, 3, [(2, 1), (3, 1), (43, 1), (149, 1), (100019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_149
    · exact prime_100019
  · decide +kernel

theorem prime_8315393939 : Nat.Prime 8315393939 := by
  apply nodeValid_prime [2, 29, 73, 233, 8429] ⟨8315393939, 2, [(2, 1), (29, 1), (73, 1), (233, 1), (8429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_73
    · exact prime_233
    · exact prime_8429
  · decide +kernel

theorem prime_8803933553 : Nat.Prime 8803933553 := by
  apply nodeValid_prime [2, 1933, 284659] ⟨8803933553, 3, [(2, 4), (1933, 1), (284659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1933
    · exact prime_284659
  · decide +kernel

theorem prime_10579677877 : Nat.Prime 10579677877 := by
  apply nodeValid_prime [2, 3, 293879941] ⟨10579677877, 2, [(2, 2), (3, 2), (293879941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293879941
  · decide +kernel

theorem prime_34281442883 : Nat.Prime 34281442883 := by
  apply nodeValid_prime [2, 99929, 171529] ⟨34281442883, 2, [(2, 1), (99929, 1), (171529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_99929
    · exact prime_171529
  · decide +kernel

theorem prime_44194956781 : Nat.Prime 44194956781 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 23, 71, 157] ⟨44194956781, 2, [(2, 2), (3, 1), (5, 1), (13, 2), (17, 1), (23, 1), (71, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_23
    · exact prime_71
    · exact prime_157
  · decide +kernel

theorem prime_44894372251 : Nat.Prime 44894372251 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 657793] ⟨44894372251, 3, [(2, 1), (3, 1), (5, 3), (7, 1), (13, 1), (657793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_657793
  · decide +kernel

theorem prime_49915253767 : Nat.Prime 49915253767 := by
  apply nodeValid_prime [2, 3, 7, 17, 137, 510287] ⟨49915253767, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (137, 1), (510287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_137
    · exact prime_510287
  · decide +kernel

theorem prime_57450559043 : Nat.Prime 57450559043 := by
  apply nodeValid_prime [2, 42089, 682489] ⟨57450559043, 2, [(2, 1), (42089, 1), (682489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_42089
    · exact prime_682489
  · decide +kernel

theorem prime_59036616439 : Nat.Prime 59036616439 := by
  apply nodeValid_prime [2, 3, 37061, 265493] ⟨59036616439, 11, [(2, 1), (3, 1), (37061, 1), (265493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37061
    · exact prime_265493
  · decide +kernel

theorem prime_66815605589 : Nat.Prime 66815605589 := by
  apply nodeValid_prime [2, 199, 449, 186947] ⟨66815605589, 2, [(2, 2), (199, 1), (449, 1), (186947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_449
    · exact prime_186947
  · decide +kernel

theorem prime_97047803129 : Nat.Prime 97047803129 := by
  apply nodeValid_prime [2, 19, 638472389] ⟨97047803129, 6, [(2, 3), (19, 1), (638472389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_638472389
  · decide +kernel

theorem prime_119514323197 : Nat.Prime 119514323197 := by
  apply nodeValid_prime [2, 3, 89, 389, 95891] ⟨119514323197, 2, [(2, 2), (3, 2), (89, 1), (389, 1), (95891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_389
    · exact prime_95891
  · decide +kernel

theorem prime_120551576449 : Nat.Prime 120551576449 := by
  apply nodeValid_prime [2, 3, 29, 659, 16427] ⟨120551576449, 7, [(2, 7), (3, 1), (29, 1), (659, 1), (16427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_659
    · exact prime_16427
  · decide +kernel

theorem prime_133421493241 : Nat.Prime 133421493241 := by
  apply nodeValid_prime [2, 3, 5, 7, 52945037] ⟨133421493241, 17, [(2, 3), (3, 2), (5, 1), (7, 1), (52945037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_52945037
  · decide +kernel

theorem prime_160231590593 : Nat.Prime 160231590593 := by
  apply nodeValid_prime [2, 101, 24788303] ⟨160231590593, 3, [(2, 6), (101, 1), (24788303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_24788303
  · decide +kernel

theorem prime_265169738681 : Nat.Prime 265169738681 := by
  apply nodeValid_prime [2, 5, 7, 11, 12299153] ⟨265169738681, 3, [(2, 3), (5, 1), (7, 2), (11, 1), (12299153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_12299153
  · decide +kernel

theorem prime_300434230777 : Nat.Prime 300434230777 := by
  apply nodeValid_prime [2, 3, 53, 103, 2293111] ⟨300434230777, 5, [(2, 3), (3, 1), (53, 1), (103, 1), (2293111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_103
    · exact prime_2293111
  · decide +kernel

theorem prime_479186436019 : Nat.Prime 479186436019 := by
  apply nodeValid_prime [2, 3, 163, 233, 2102857] ⟨479186436019, 2, [(2, 1), (3, 1), (163, 1), (233, 1), (2102857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_233
    · exact prime_2102857
  · decide +kernel

theorem prime_484100240509 : Nat.Prime 484100240509 := by
  apply nodeValid_prime [2, 3, 37, 67, 5424457] ⟨484100240509, 2, [(2, 2), (3, 2), (37, 1), (67, 1), (5424457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_67
    · exact prime_5424457
  · decide +kernel

theorem prime_806201752127 : Nat.Prime 806201752127 := by
  apply nodeValid_prime [2, 17, 61, 83, 241, 19433] ⟨806201752127, 5, [(2, 1), (17, 1), (61, 1), (83, 1), (241, 1), (19433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_83
    · exact prime_241
    · exact prime_19433
  · decide +kernel

theorem prime_1205515765777 : Nat.Prime 1205515765777 := by
  apply nodeValid_prime [2, 3, 7, 157, 22852513] ⟨1205515765777, 5, [(2, 4), (3, 1), (7, 1), (157, 1), (22852513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
    · exact prime_22852513
  · decide +kernel

theorem prime_4773055296259 : Nat.Prime 4773055296259 := by
  apply nodeValid_prime [2, 3, 265169738681] ⟨4773055296259, 2, [(2, 1), (3, 2), (265169738681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_265169738681
  · decide +kernel

theorem prime_4773055332349 : Nat.Prime 4773055332349 := by
  apply nodeValid_prime [2, 3, 44194956781] ⟨4773055332349, 2, [(2, 2), (3, 3), (44194956781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44194956781
  · decide +kernel

theorem prime_4773055333357 : Nat.Prime 4773055333357 := by
  apply nodeValid_prime [2, 3, 269, 492880559] ⟨4773055333357, 5, [(2, 2), (3, 2), (269, 1), (492880559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_492880559
  · decide +kernel

theorem prime_4776813097457 : Nat.Prime 4776813097457 := by
  apply nodeValid_prime [2, 37, 21377, 377459] ⟨4776813097457, 3, [(2, 4), (37, 1), (21377, 1), (377459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_21377
    · exact prime_377459
  · decide +kernel

theorem prime_4776813244561 : Nat.Prime 4776813244561 := by
  apply nodeValid_prime [2, 3, 5, 7, 601, 619, 7643] ⟨4776813244561, 19, [(2, 4), (3, 1), (5, 1), (7, 1), (601, 1), (619, 1), (7643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_601
    · exact prime_619
    · exact prime_7643
  · decide +kernel

theorem prime_4776813246169 : Nat.Prime 4776813246169 := by
  apply nodeValid_prime [2, 3, 353, 4649, 40427] ⟨4776813246169, 7, [(2, 3), (3, 2), (353, 1), (4649, 1), (40427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353
    · exact prime_4649
    · exact prime_40427
  · decide +kernel

theorem prime_4780572901063 : Nat.Prime 4780572901063 := by
  apply nodeValid_prime [2, 3, 7, 263, 432787697] ⟨4780572901063, 3, [(2, 1), (3, 1), (7, 1), (263, 1), (432787697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_263
    · exact prime_432787697
  · decide +kernel

theorem prime_4780572926693 : Nat.Prime 4780572926693 := by
  apply nodeValid_prime [2, 71, 237084553] ⟨4780572926693, 2, [(2, 2), (71, 2), (237084553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_237084553
  · decide +kernel

theorem prime_4780572927881 : Nat.Prime 4780572927881 := by
  apply nodeValid_prime [2, 5, 119514323197] ⟨4780572927881, 3, [(2, 3), (5, 1), (119514323197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_119514323197
  · decide +kernel

theorem prime_4784334718619 : Nat.Prime 4784334718619 := by
  apply nodeValid_prime [2, 7, 13, 41, 641159839] ⟨4784334718619, 2, [(2, 1), (7, 1), (13, 1), (41, 1), (641159839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_41
    · exact prime_641159839
  · decide +kernel

theorem prime_4784334753053 : Nat.Prime 4784334753053 := by
  apply nodeValid_prime [2, 457, 2617250959] ⟨4784334753053, 2, [(2, 2), (457, 1), (2617250959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_2617250959
  · decide +kernel

theorem prime_4784334754531 : Nat.Prime 4784334754531 := by
  apply nodeValid_prime [2, 3, 5, 1291, 123530461] ⟨4784334754531, 3, [(2, 1), (3, 1), (5, 1), (1291, 1), (123530461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1291
    · exact prime_123530461
  · decide +kernel

theorem prime_4788098458261 : Nat.Prime 4788098458261 := by
  apply nodeValid_prime [2, 3, 5, 13, 472199059] ⟨4788098458261, 6, [(2, 2), (3, 1), (5, 1), (13, 2), (472199059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_472199059
  · decide +kernel

theorem prime_4788098458441 : Nat.Prime 4788098458441 := by
  apply nodeValid_prime [2, 3, 5, 11, 59, 508103] ⟨4788098458441, 31, [(2, 3), (3, 1), (5, 1), (11, 3), (59, 1), (508103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_59
    · exact prime_508103
  · decide +kernel

theorem prime_4788098542831 : Nat.Prime 4788098542831 := by
  apply nodeValid_prime [2, 3, 5, 146299, 1090939] ⟨4788098542831, 3, [(2, 1), (3, 1), (5, 1), (146299, 1), (1090939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_146299
    · exact prime_1090939
  · decide +kernel

theorem prime_4791864360191 : Nat.Prime 4791864360191 := by
  apply nodeValid_prime [2, 5, 479186436019] ⟨4791864360191, 31, [(2, 1), (5, 1), (479186436019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479186436019
  · decide +kernel

theorem prime_4791864361633 : Nat.Prime 4791864361633 := by
  apply nodeValid_prime [2, 3, 49915253767] ⟨4791864361633, 5, [(2, 5), (3, 1), (49915253767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49915253767
  · decide +kernel

theorem prime_4791864371299 : Nat.Prime 4791864371299 := by
  apply nodeValid_prime [2, 3, 220357, 3624319] ⟨4791864371299, 3, [(2, 1), (3, 1), (220357, 1), (3624319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_220357
    · exact prime_3624319
  · decide +kernel

theorem prime_4795632134921 : Nat.Prime 4795632134921 := by
  apply nodeValid_prime [2, 5, 11, 8971, 1214933] ⟨4795632134921, 3, [(2, 3), (5, 1), (11, 1), (8971, 1), (1214933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_8971
    · exact prime_1214933
  · decide +kernel

theorem prime_4795632134939 : Nat.Prime 4795632134939 := by
  apply nodeValid_prime [2, 196117, 12226457] ⟨4795632134939, 2, [(2, 1), (196117, 1), (12226457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_196117
    · exact prime_12226457
  · decide +kernel

theorem prime_4795632203491 : Nat.Prime 4795632203491 := by
  apply nodeValid_prime [2, 3, 5, 17, 1039, 3016747] ⟨4795632203491, 2, [(2, 1), (3, 2), (5, 1), (17, 1), (1039, 1), (3016747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1039
    · exact prime_3016747
  · decide +kernel

theorem prime_4799401999523 : Nat.Prime 4799401999523 := by
  apply nodeValid_prime [2, 13, 19, 227, 42799069] ⟨4799401999523, 5, [(2, 1), (13, 1), (19, 1), (227, 1), (42799069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_227
    · exact prime_42799069
  · decide +kernel

theorem prime_4799402003621 : Nat.Prime 4799402003621 := by
  apply nodeValid_prime [2, 5, 7, 34281442883] ⟨4799402003621, 2, [(2, 2), (5, 1), (7, 1), (34281442883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_34281442883
  · decide +kernel

theorem prime_4799402035759 : Nat.Prime 4799402035759 := by
  apply nodeValid_prime [2, 3, 11, 37, 41, 5326171] ⟨4799402035759, 3, [(2, 1), (3, 3), (11, 1), (37, 1), (41, 1), (5326171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_41
    · exact prime_5326171
  · decide +kernel

theorem prime_4803173756159 : Nat.Prime 4803173756159 := by
  apply nodeValid_prime [2, 227, 10579677877] ⟨4803173756159, 7, [(2, 1), (227, 1), (10579677877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_10579677877
  · decide +kernel

theorem prime_4803173756677 : Nat.Prime 4803173756677 := by
  apply nodeValid_prime [2, 3, 133421493241] ⟨4803173756677, 2, [(2, 2), (3, 2), (133421493241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_133421493241
  · decide +kernel

theorem prime_4803173864051 : Nat.Prime 4803173864051 := by
  apply nodeValid_prime [2, 5, 41, 67, 34970323] ⟨4803173864051, 10, [(2, 1), (5, 2), (41, 1), (67, 1), (34970323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_67
    · exact prime_34970323
  · decide +kernel

theorem prime_4806947692433 : Nat.Prime 4806947692433 := by
  apply nodeValid_prime [2, 300434230777] ⟨4806947692433, 3, [(2, 4), (300434230777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_300434230777
  · decide +kernel

theorem prime_4806947717791 : Nat.Prime 4806947717791 := by
  apply nodeValid_prime [2, 3, 5, 160231590593] ⟨4806947717791, 3, [(2, 1), (3, 1), (5, 1), (160231590593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_160231590593
  · decide +kernel

theorem prime_4806947719939 : Nat.Prime 4806947719939 := by
  apply nodeValid_prime [2, 3, 7, 13, 8803933553] ⟨4806947719939, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (8803933553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_8803933553
  · decide +kernel

theorem prime_4810723526849 : Nat.Prime 4810723526849 := by
  apply nodeValid_prime [2, 211, 613, 581149] ⟨4810723526849, 3, [(2, 6), (211, 1), (613, 1), (581149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_613
    · exact prime_581149
  · decide +kernel

theorem prime_4810723602409 : Nat.Prime 4810723602409 := by
  apply nodeValid_prime [2, 3, 66815605589] ⟨4810723602409, 19, [(2, 3), (3, 2), (66815605589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66815605589
  · decide +kernel

theorem prime_4810723602449 : Nat.Prime 4810723602449 := by
  apply nodeValid_prime [2, 1493, 12619, 15959] ⟨4810723602449, 3, [(2, 4), (1493, 1), (12619, 1), (15959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1493
    · exact prime_12619
    · exact prime_15959
  · decide +kernel

theorem prime_4814501365963 : Nat.Prime 4814501365963 := by
  apply nodeValid_prime [2, 3, 57089, 1561727] ⟨4814501365963, 3, [(2, 1), (3, 3), (57089, 1), (1561727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_57089
    · exact prime_1561727
  · decide +kernel

theorem prime_4814501485309 : Nat.Prime 4814501485309 := by
  apply nodeValid_prime [2, 3, 17, 67, 352246231] ⟨4814501485309, 2, [(2, 2), (3, 1), (17, 1), (67, 1), (352246231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
    · exact prime_352246231
  · decide +kernel

theorem prime_4814501486401 : Nat.Prime 4814501486401 := by
  apply nodeValid_prime [2, 3, 5, 881, 379501] ⟨4814501486401, 17, [(2, 6), (3, 2), (5, 2), (881, 1), (379501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_881
    · exact prime_379501
  · decide +kernel

theorem prime_4818281161957 : Nat.Prime 4818281161957 := by
  apply nodeValid_prime [2, 3, 37, 40343, 268993] ⟨4818281161957, 5, [(2, 2), (3, 1), (37, 1), (40343, 1), (268993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_40343
    · exact prime_268993
  · decide +kernel

theorem prime_4818281162449 : Nat.Prime 4818281162449 := by
  apply nodeValid_prime [2, 3, 13, 19, 1433, 283601] ⟨4818281162449, 11, [(2, 4), (3, 1), (13, 1), (19, 1), (1433, 1), (283601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_1433
    · exact prime_283601
  · decide +kernel

theorem prime_4818281213047 : Nat.Prime 4818281213047 := by
  apply nodeValid_prime [2, 3, 7, 163, 211, 476513] ⟨4818281213047, 3, [(2, 1), (3, 1), (7, 2), (163, 1), (211, 1), (476513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_163
    · exact prime_211
    · exact prime_476513
  · decide +kernel

theorem prime_4822063057961 : Nat.Prime 4822063057961 := by
  apply nodeValid_prime [2, 5, 120551576449] ⟨4822063057961, 6, [(2, 3), (5, 1), (120551576449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_120551576449
  · decide +kernel

theorem prime_4822063062989 : Nat.Prime 4822063062989 := by
  apply nodeValid_prime [2, 293, 12071, 340849] ⟨4822063062989, 2, [(2, 2), (293, 1), (12071, 1), (340849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_12071
    · exact prime_340849
  · decide +kernel

theorem prime_4822063063109 : Nat.Prime 4822063063109 := by
  apply nodeValid_prime [2, 1205515765777] ⟨4822063063109, 2, [(2, 2), (1205515765777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1205515765777
  · decide +kernel

theorem prime_4825846908859 : Nat.Prime 4825846908859 := by
  apply nodeValid_prime [2, 3, 37, 181, 120099719] ⟨4825846908859, 3, [(2, 1), (3, 1), (37, 1), (181, 1), (120099719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_181
    · exact prime_120099719
  · decide +kernel

theorem prime_4825846959343 : Nat.Prime 4825846959343 := by
  apply nodeValid_prime [2, 3, 53, 31891, 475859] ⟨4825846959343, 11, [(2, 1), (3, 1), (53, 1), (31891, 1), (475859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_31891
    · exact prime_475859
  · decide +kernel

theorem prime_4825846959613 : Nat.Prime 4825846959613 := by
  apply nodeValid_prime [2, 3, 7, 57450559043] ⟨4825846959613, 5, [(2, 2), (3, 1), (7, 1), (57450559043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_57450559043
  · decide +kernel

theorem prime_4829632767139 : Nat.Prime 4829632767139 := by
  apply nodeValid_prime [2, 3, 61, 19457, 678199] ⟨4829632767139, 3, [(2, 1), (3, 1), (61, 1), (19457, 1), (678199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_19457
    · exact prime_678199
  · decide +kernel

theorem prime_4829632854127 : Nat.Prime 4829632854127 := by
  apply nodeValid_prime [2, 3, 1193, 1201, 561797] ⟨4829632854127, 3, [(2, 1), (3, 1), (1193, 1), (1201, 1), (561797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1193
    · exact prime_1201
    · exact prime_561797
  · decide +kernel

theorem prime_4829632855609 : Nat.Prime 4829632855609 := by
  apply nodeValid_prime [2, 3, 11, 47, 9491, 41011] ⟨4829632855609, 19, [(2, 3), (3, 1), (11, 1), (47, 1), (9491, 1), (41011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_9491
    · exact prime_41011
  · decide +kernel

theorem prime_4833420627953 : Nat.Prime 4833420627953 := by
  apply nodeValid_prime [2, 7, 11677, 3695773] ⟨4833420627953, 3, [(2, 4), (7, 1), (11677, 1), (3695773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11677
    · exact prime_3695773
  · decide +kernel

theorem prime_4833420701111 : Nat.Prime 4833420701111 := by
  apply nodeValid_prime [2, 5, 31, 647, 1301, 18523] ⟨4833420701111, 7, [(2, 1), (5, 1), (31, 1), (647, 1), (1301, 1), (18523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_647
    · exact prime_1301
    · exact prime_18523
  · decide +kernel

theorem prime_4833420701117 : Nat.Prime 4833420701117 := by
  apply nodeValid_prime [2, 7, 223, 774090439] ⟨4833420701117, 2, [(2, 2), (7, 1), (223, 1), (774090439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_223
    · exact prime_774090439
  · decide +kernel

theorem prime_4837210512763 : Nat.Prime 4837210512763 := by
  apply nodeValid_prime [2, 3, 806201752127] ⟨4837210512763, 2, [(2, 1), (3, 1), (806201752127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_806201752127
  · decide +kernel

theorem prime_4837210520981 : Nat.Prime 4837210520981 := by
  apply nodeValid_prime [2, 5, 19, 6053, 2103007] ⟨4837210520981, 2, [(2, 2), (5, 1), (19, 1), (6053, 1), (2103007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_6053
    · exact prime_2103007
  · decide +kernel

theorem prime_4837210521053 : Nat.Prime 4837210521053 := by
  apply nodeValid_prime [2, 7, 13, 17, 61, 67, 11251] ⟨4837210521053, 2, [(2, 2), (7, 1), (13, 1), (17, 2), (61, 1), (67, 1), (11251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_61
    · exact prime_67
    · exact prime_11251
  · decide +kernel

theorem prime_4841002405091 : Nat.Prime 4841002405091 := by
  apply nodeValid_prime [2, 5, 484100240509] ⟨4841002405091, 2, [(2, 1), (5, 1), (484100240509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_484100240509
  · decide +kernel

theorem prime_4841002547659 : Nat.Prime 4841002547659 := by
  apply nodeValid_prime [2, 3, 563, 159233029] ⟨4841002547659, 3, [(2, 1), (3, 3), (563, 1), (159233029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_563
    · exact prime_159233029
  · decide +kernel

theorem prime_4841002547999 : Nat.Prime 4841002547999 := by
  apply nodeValid_prime [2, 41, 59036616439] ⟨4841002547999, 7, [(2, 1), (41, 1), (59036616439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_59036616439
  · decide +kernel

theorem prime_4844796193253 : Nat.Prime 4844796193253 := by
  apply nodeValid_prime [2, 3329, 363832697] ⟨4844796193253, 2, [(2, 2), (3329, 1), (363832697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3329
    · exact prime_363832697
  · decide +kernel

theorem prime_4844796193277 : Nat.Prime 4844796193277 := by
  apply nodeValid_prime [2, 13, 89, 97, 10792211] ⟨4844796193277, 2, [(2, 2), (13, 1), (89, 1), (97, 1), (10792211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_89
    · exact prime_97
    · exact prime_10792211
  · decide +kernel

theorem prime_4844796296563 : Nat.Prime 4844796296563 := by
  apply nodeValid_prime [2, 3, 31, 67, 129588517] ⟨4844796296563, 2, [(2, 1), (3, 2), (31, 1), (67, 1), (129588517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_67
    · exact prime_129588517
  · decide +kernel

theorem prime_4848592202921 : Nat.Prime 4848592202921 := by
  apply nodeValid_prime [2, 5, 47819, 2534867] ⟨4848592202921, 3, [(2, 3), (5, 1), (47819, 1), (2534867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47819
    · exact prime_2534867
  · decide +kernel

theorem prime_4848592202999 : Nat.Prime 4848592202999 := by
  apply nodeValid_prime [2, 47, 173, 2851, 104579] ⟨4848592202999, 23, [(2, 1), (47, 1), (173, 1), (2851, 1), (104579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_173
    · exact prime_2851
    · exact prime_104579
  · decide +kernel

theorem prime_4848592203109 : Nat.Prime 4848592203109 := by
  apply nodeValid_prime [2, 3, 44894372251] ⟨4848592203109, 2, [(2, 2), (3, 3), (44894372251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44894372251
  · decide +kernel

theorem prime_4852390119491 : Nat.Prime 4852390119491 := by
  apply nodeValid_prime [2, 5, 401, 1210072349] ⟨4852390119491, 2, [(2, 1), (5, 1), (401, 1), (1210072349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_401
    · exact prime_1210072349
  · decide +kernel

theorem prime_4852390156451 : Nat.Prime 4852390156451 := by
  apply nodeValid_prime [2, 5, 97047803129] ⟨4852390156451, 2, [(2, 1), (5, 2), (97047803129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97047803129
  · decide +kernel

theorem prime_4852390156591 : Nat.Prime 4852390156591 := by
  apply nodeValid_prime [2, 3, 5, 19, 79, 241, 447133] ⟨4852390156591, 6, [(2, 1), (3, 1), (5, 1), (19, 1), (79, 1), (241, 1), (447133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_79
    · exact prime_241
    · exact prime_447133
  · decide +kernel

theorem prime_4856190056087 : Nat.Prime 4856190056087 := by
  apply nodeValid_prime [2, 2083, 1165672121] ⟨4856190056087, 5, [(2, 1), (2083, 1), (1165672121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2083
    · exact prime_1165672121
  · decide +kernel

theorem prime_4856190057689 : Nat.Prime 4856190057689 := by
  apply nodeValid_prime [2, 8161, 74381051] ⟨4856190057689, 3, [(2, 3), (8161, 1), (74381051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8161
    · exact prime_74381051
  · decide +kernel

theorem prime_4856190060377 : Nat.Prime 4856190060377 := by
  apply nodeValid_prime [2, 73, 8315393939] ⟨4856190060377, 3, [(2, 3), (73, 1), (8315393939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_8315393939
  · decide +kernel

theorem prime_4859992023077 : Nat.Prime 4859992023077 := by
  apply nodeValid_prime [2, 563, 2158078163] ⟨4859992023077, 2, [(2, 2), (563, 1), (2158078163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_2158078163
  · decide +kernel

theorem prime_4859992023569 : Nat.Prime 4859992023569 := by
  apply nodeValid_prime [2, 11, 19, 229, 6346493] ⟨4859992023569, 3, [(2, 4), (11, 1), (19, 1), (229, 1), (6346493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_229
    · exact prime_6346493
  · decide +kernel

theorem prime_4859992024337 : Nat.Prime 4859992024337 := by
  apply nodeValid_prime [2, 79, 3844930399] ⟨4859992024337, 3, [(2, 4), (79, 1), (3844930399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_3844930399
  · decide +kernel

theorem prime_4863795902821 : Nat.Prime 4863795902821 := by
  apply nodeValid_prime [2, 3, 5, 419, 64489471] ⟨4863795902821, 10, [(2, 2), (3, 2), (5, 1), (419, 1), (64489471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_419
    · exact prime_64489471
  · decide +kernel

theorem prime_4863795905431 : Nat.Prime 4863795905431 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 37, 251, 311] ⟨4863795905431, 3, [(2, 1), (3, 7), (5, 1), (7, 1), (11, 1), (37, 1), (251, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_37
    · exact prime_251
    · exact prime_311
  · decide +kernel

theorem prime_4863796001003 : Nat.Prime 4863796001003 := by
  apply nodeValid_prime [2, 21379, 113751719] ⟨4863796001003, 2, [(2, 1), (21379, 1), (113751719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21379
    · exact prime_113751719
  · decide +kernel

end Sude.Lucas.Generated
