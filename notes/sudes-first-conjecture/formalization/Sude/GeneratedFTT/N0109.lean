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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0088

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11933 : Nat.Prime 11933 := by
  apply nodeValid_prime [2, 19, 157] ⟨11933, 2, [(2, 2), (19, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_157
  · decide +kernel

theorem prime_13963 : Nat.Prime 13963 := by
  apply nodeValid_prime [2, 3, 13, 179] ⟨13963, 3, [(2, 1), (3, 1), (13, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_179
  · decide +kernel

theorem prime_14879 : Nat.Prime 14879 := by
  apply nodeValid_prime [2, 43, 173] ⟨14879, 7, [(2, 1), (43, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_173
  · decide +kernel

theorem prime_16369 : Nat.Prime 16369 := by
  apply nodeValid_prime [2, 3, 11, 31] ⟨16369, 7, [(2, 4), (3, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_19181 : Nat.Prime 19181 := by
  apply nodeValid_prime [2, 5, 7, 137] ⟨19181, 2, [(2, 2), (5, 1), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_33599 : Nat.Prime 33599 := by
  apply nodeValid_prime [2, 107, 157] ⟨33599, 11, [(2, 1), (107, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_157
  · decide +kernel

theorem prime_39239 : Nat.Prime 39239 := by
  apply nodeValid_prime [2, 23, 853] ⟨39239, 7, [(2, 1), (23, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_853
  · decide +kernel

theorem prime_41203 : Nat.Prime 41203 := by
  apply nodeValid_prime [2, 3, 7, 109] ⟨41203, 3, [(2, 1), (3, 3), (7, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
  · decide +kernel

theorem prime_42467 : Nat.Prime 42467 := by
  apply nodeValid_prime [2, 17, 1249] ⟨42467, 5, [(2, 1), (17, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1249
  · decide +kernel

theorem prime_51839 : Nat.Prime 51839 := by
  apply nodeValid_prime [2, 25919] ⟨51839, 7, [(2, 1), (25919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25919
  · decide +kernel

theorem prime_52361 : Nat.Prime 52361 := by
  apply nodeValid_prime [2, 5, 7, 11, 17] ⟨52361, 6, [(2, 3), (5, 1), (7, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_56989 : Nat.Prime 56989 := by
  apply nodeValid_prime [2, 3, 1583] ⟨56989, 6, [(2, 2), (3, 2), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1583
  · decide +kernel

theorem prime_68581 : Nat.Prime 68581 := by
  apply nodeValid_prime [2, 3, 5, 127] ⟨68581, 6, [(2, 2), (3, 3), (5, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_81373 : Nat.Prime 81373 := by
  apply nodeValid_prime [2, 3, 6781] ⟨81373, 2, [(2, 2), (3, 1), (6781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6781
  · decide +kernel

theorem prime_84437 : Nat.Prime 84437 := by
  apply nodeValid_prime [2, 11, 19, 101] ⟨84437, 2, [(2, 2), (11, 1), (19, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_101
  · decide +kernel

theorem prime_93871 : Nat.Prime 93871 := by
  apply nodeValid_prime [2, 3, 5, 7, 149] ⟨93871, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_121181 : Nat.Prime 121181 := by
  apply nodeValid_prime [2, 5, 73, 83] ⟨121181, 2, [(2, 2), (5, 1), (73, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_83
  · decide +kernel

theorem prime_150889 : Nat.Prime 150889 := by
  apply nodeValid_prime [2, 3, 6287] ⟨150889, 11, [(2, 3), (3, 1), (6287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6287
  · decide +kernel

theorem prime_152777 : Nat.Prime 152777 := by
  apply nodeValid_prime [2, 13, 113] ⟨152777, 3, [(2, 3), (13, 2), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
  · decide +kernel

theorem prime_167213 : Nat.Prime 167213 := by
  apply nodeValid_prime [2, 17, 2459] ⟨167213, 2, [(2, 2), (17, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2459
  · decide +kernel

theorem prime_168761 : Nat.Prime 168761 := by
  apply nodeValid_prime [2, 5, 4219] ⟨168761, 3, [(2, 3), (5, 1), (4219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4219
  · decide +kernel

theorem prime_230369 : Nat.Prime 230369 := by
  apply nodeValid_prime [2, 23, 313] ⟨230369, 3, [(2, 5), (23, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_313
  · decide +kernel

theorem prime_233917 : Nat.Prime 233917 := by
  apply nodeValid_prime [2, 3, 101, 193] ⟨233917, 6, [(2, 2), (3, 1), (101, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_193
  · decide +kernel

theorem prime_255253 : Nat.Prime 255253 := by
  apply nodeValid_prime [2, 3, 89, 239] ⟨255253, 5, [(2, 2), (3, 1), (89, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_239
  · decide +kernel

theorem prime_277097 : Nat.Prime 277097 := by
  apply nodeValid_prime [2, 19, 1823] ⟨277097, 3, [(2, 3), (19, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1823
  · decide +kernel

theorem prime_280591 : Nat.Prime 280591 := by
  apply nodeValid_prime [2, 3, 5, 47, 199] ⟨280591, 3, [(2, 1), (3, 1), (5, 1), (47, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_199
  · decide +kernel

theorem prime_283771 : Nat.Prime 283771 := by
  apply nodeValid_prime [2, 3, 5, 1051] ⟨283771, 2, [(2, 1), (3, 3), (5, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1051
  · decide +kernel

theorem prime_331249 : Nat.Prime 331249 := by
  apply nodeValid_prime [2, 3, 67, 103] ⟨331249, 11, [(2, 4), (3, 1), (67, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_103
  · decide +kernel

theorem prime_334427 : Nat.Prime 334427 := by
  apply nodeValid_prime [2, 167213] ⟨334427, 2, [(2, 1), (167213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_167213
  · decide +kernel

theorem prime_412031 : Nat.Prime 412031 := by
  apply nodeValid_prime [2, 5, 41203] ⟨412031, 11, [(2, 1), (5, 1), (41203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41203
  · decide +kernel

theorem prime_451181 : Nat.Prime 451181 := by
  apply nodeValid_prime [2, 5, 17, 1327] ⟨451181, 2, [(2, 2), (5, 1), (17, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1327
  · decide +kernel

theorem prime_478523 : Nat.Prime 478523 := by
  apply nodeValid_prime [2, 11, 21751] ⟨478523, 2, [(2, 1), (11, 1), (21751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_21751
  · decide +kernel

theorem prime_564533 : Nat.Prime 564533 := by
  apply nodeValid_prime [2, 107, 1319] ⟨564533, 2, [(2, 2), (107, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_1319
  · decide +kernel

theorem prime_602081 : Nat.Prime 602081 := by
  apply nodeValid_prime [2, 5, 53, 71] ⟨602081, 11, [(2, 5), (5, 1), (53, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_71
  · decide +kernel

theorem prime_611213 : Nat.Prime 611213 := by
  apply nodeValid_prime [2, 7, 83, 263] ⟨611213, 2, [(2, 2), (7, 1), (83, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
    · exact prime_263
  · decide +kernel

theorem prime_824063 : Nat.Prime 824063 := by
  apply nodeValid_prime [2, 412031] ⟨824063, 5, [(2, 1), (412031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_412031
  · decide +kernel

theorem prime_991621 : Nat.Prime 991621 := by
  apply nodeValid_prime [2, 3, 5, 7, 787] ⟨991621, 14, [(2, 2), (3, 2), (5, 1), (7, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_787
  · decide +kernel

theorem prime_1007971 : Nat.Prime 1007971 := by
  apply nodeValid_prime [2, 3, 5, 33599] ⟨1007971, 2, [(2, 1), (3, 1), (5, 1), (33599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_33599
  · decide +kernel

theorem prime_1102313 : Nat.Prime 1102313 := by
  apply nodeValid_prime [2, 227, 607] ⟨1102313, 3, [(2, 3), (227, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_607
  · decide +kernel

theorem prime_1255847 : Nat.Prime 1255847 := by
  apply nodeValid_prime [2, 23, 1187] ⟨1255847, 5, [(2, 1), (23, 2), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1187
  · decide +kernel

theorem prime_1438447 : Nat.Prime 1438447 := by
  apply nodeValid_prime [2, 3, 149, 1609] ⟨1438447, 5, [(2, 1), (3, 1), (149, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_1609
  · decide +kernel

theorem prime_1571657 : Nat.Prime 1571657 := by
  apply nodeValid_prime [2, 71, 2767] ⟨1571657, 3, [(2, 3), (71, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2767
  · decide +kernel

theorem prime_1709671 : Nat.Prime 1709671 := by
  apply nodeValid_prime [2, 3, 5, 56989] ⟨1709671, 3, [(2, 1), (3, 1), (5, 1), (56989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_56989
  · decide +kernel

theorem prime_1734547 : Nat.Prime 1734547 := by
  apply nodeValid_prime [2, 3, 11, 41, 641] ⟨1734547, 2, [(2, 1), (3, 1), (11, 1), (41, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_641
  · decide +kernel

theorem prime_2065967 : Nat.Prime 2065967 := by
  apply nodeValid_prime [2, 7, 173, 853] ⟨2065967, 5, [(2, 1), (7, 1), (173, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_173
    · exact prime_853
  · decide +kernel

theorem prime_2177239 : Nat.Prime 2177239 := by
  apply nodeValid_prime [2, 3, 7, 51839] ⟨2177239, 3, [(2, 1), (3, 1), (7, 1), (51839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_51839
  · decide +kernel

theorem prime_2216777 : Nat.Prime 2216777 := by
  apply nodeValid_prime [2, 277097] ⟨2216777, 3, [(2, 3), (277097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_277097
  · decide +kernel

theorem prime_2281973 : Nat.Prime 2281973 := by
  apply nodeValid_prime [2, 7, 11, 31, 239] ⟨2281973, 2, [(2, 2), (7, 1), (11, 1), (31, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_239
  · decide +kernel

theorem prime_3080939 : Nat.Prime 3080939 := by
  apply nodeValid_prime [2, 7, 359, 613] ⟨3080939, 2, [(2, 1), (7, 1), (359, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_359
    · exact prime_613
  · decide +kernel

theorem prime_3113833 : Nat.Prime 3113833 := by
  apply nodeValid_prime [2, 3, 23, 5641] ⟨3113833, 11, [(2, 3), (3, 1), (23, 1), (5641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_5641
  · decide +kernel

theorem prime_3266551 : Nat.Prime 3266551 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 61] ⟨3266551, 7, [(2, 1), (3, 2), (5, 2), (7, 1), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_3726809 : Nat.Prime 3726809 := by
  apply nodeValid_prime [2, 17, 67, 409] ⟨3726809, 6, [(2, 3), (17, 1), (67, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_67
    · exact prime_409
  · decide +kernel

theorem prime_3858287 : Nat.Prime 3858287 := by
  apply nodeValid_prime [2, 17, 37, 3067] ⟨3858287, 5, [(2, 1), (17, 1), (37, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_3067
  · decide +kernel

theorem prime_3864347 : Nat.Prime 3864347 := by
  apply nodeValid_prime [2, 431, 4483] ⟨3864347, 2, [(2, 1), (431, 1), (4483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_4483
  · decide +kernel

theorem prime_4084049 : Nat.Prime 4084049 := by
  apply nodeValid_prime [2, 255253] ⟨4084049, 3, [(2, 4), (255253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_255253
  · decide +kernel

theorem prime_4154461 : Nat.Prime 4154461 := by
  apply nodeValid_prime [2, 3, 5, 17, 4073] ⟨4154461, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (4073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_4073
  · decide +kernel

theorem prime_5598473 : Nat.Prime 5598473 := by
  apply nodeValid_prime [2, 11, 113, 563] ⟨5598473, 3, [(2, 3), (11, 1), (113, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
    · exact prime_563
  · decide +kernel

theorem prime_6073877 : Nat.Prime 6073877 := by
  apply nodeValid_prime [2, 29, 52361] ⟨6073877, 2, [(2, 2), (29, 1), (52361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_52361
  · decide +kernel

theorem prime_6402751 : Nat.Prime 6402751 := by
  apply nodeValid_prime [2, 3, 5, 8537] ⟨6402751, 3, [(2, 1), (3, 1), (5, 3), (8537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8537
  · decide +kernel

theorem prime_6938189 : Nat.Prime 6938189 := by
  apply nodeValid_prime [2, 1734547] ⟨6938189, 2, [(2, 2), (1734547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1734547
  · decide +kernel

theorem prime_8514797 : Nat.Prime 8514797 := by
  apply nodeValid_prime [2, 673, 3163] ⟨8514797, 2, [(2, 2), (673, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_673
    · exact prime_3163
  · decide +kernel

theorem prime_10798727 : Nat.Prime 10798727 := by
  apply nodeValid_prime [2, 19, 31, 89, 103] ⟨10798727, 5, [(2, 1), (19, 1), (31, 1), (89, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_89
    · exact prime_103
  · decide +kernel

theorem prime_12001097 : Nat.Prime 12001097 := by
  apply nodeValid_prime [2, 937, 1601] ⟨12001097, 3, [(2, 3), (937, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_937
    · exact prime_1601
  · decide +kernel

theorem prime_14042137 : Nat.Prime 14042137 := by
  apply nodeValid_prime [2, 3, 17, 127, 271] ⟨14042137, 5, [(2, 3), (3, 1), (17, 1), (127, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_127
    · exact prime_271
  · decide +kernel

theorem prime_15824513 : Nat.Prime 15824513 := by
  apply nodeValid_prime [2, 11, 11239] ⟨15824513, 3, [(2, 7), (11, 1), (11239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11239
  · decide +kernel

theorem prime_19804871 : Nat.Prime 19804871 := by
  apply nodeValid_prime [2, 5, 61, 32467] ⟨19804871, 11, [(2, 1), (5, 1), (61, 1), (32467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_32467
  · decide +kernel

theorem prime_20763923 : Nat.Prime 20763923 := by
  apply nodeValid_prime [2, 19, 577, 947] ⟨20763923, 2, [(2, 1), (19, 1), (577, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_577
    · exact prime_947
  · decide +kernel

theorem prime_23149723 : Nat.Prime 23149723 := by
  apply nodeValid_prime [2, 3, 3858287] ⟨23149723, 5, [(2, 1), (3, 1), (3858287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3858287
  · decide +kernel

theorem prime_24735121 : Nat.Prime 24735121 := by
  apply nodeValid_prime [2, 3, 5, 23, 4481] ⟨24735121, 7, [(2, 4), (3, 1), (5, 1), (23, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_4481
  · decide +kernel

theorem prime_28711381 : Nat.Prime 28711381 := by
  apply nodeValid_prime [2, 3, 5, 478523] ⟨28711381, 6, [(2, 2), (3, 1), (5, 1), (478523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_478523
  · decide +kernel

theorem prime_44272903 : Nat.Prime 44272903 := by
  apply nodeValid_prime [2, 3, 71, 103, 1009] ⟨44272903, 3, [(2, 1), (3, 1), (71, 1), (103, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_103
    · exact prime_1009
  · decide +kernel

theorem prime_47899259 : Nat.Prime 47899259 := by
  apply nodeValid_prime [2, 11, 2177239] ⟨47899259, 2, [(2, 1), (11, 1), (2177239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2177239
  · decide +kernel

theorem prime_51088883 : Nat.Prime 51088883 := by
  apply nodeValid_prime [2, 13, 113, 17389] ⟨51088883, 2, [(2, 1), (13, 1), (113, 1), (17389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
    · exact prime_17389
  · decide +kernel

theorem prime_52175327 : Nat.Prime 52175327 := by
  apply nodeValid_prime [2, 7, 3726809] ⟨52175327, 5, [(2, 1), (7, 1), (3726809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3726809
  · decide +kernel

theorem prime_66330023 : Nat.Prime 66330023 := by
  apply nodeValid_prime [2, 11, 17, 23, 701] ⟨66330023, 10, [(2, 1), (11, 2), (17, 1), (23, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_23
    · exact prime_701
  · decide +kernel

theorem prime_79077671 : Nat.Prime 79077671 := by
  apply nodeValid_prime [2, 5, 7, 71, 2273] ⟨79077671, 7, [(2, 1), (5, 1), (7, 2), (71, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_2273
  · decide +kernel

theorem prime_83140117 : Nat.Prime 83140117 := by
  apply nodeValid_prime [2, 3, 1279, 5417] ⟨83140117, 2, [(2, 2), (3, 1), (1279, 1), (5417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
    · exact prime_5417
  · decide +kernel

theorem prime_84210121 : Nat.Prime 84210121 := by
  apply nodeValid_prime [2, 3, 5, 233917] ⟨84210121, 11, [(2, 3), (3, 2), (5, 1), (233917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233917
  · decide +kernel

theorem prime_89988193 : Nat.Prime 89988193 := by
  apply nodeValid_prime [2, 3, 7, 14879] ⟨89988193, 5, [(2, 5), (3, 3), (7, 1), (14879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14879
  · decide +kernel

theorem prime_163162297 : Nat.Prime 163162297 := by
  apply nodeValid_prime [2, 3, 11, 43, 1597] ⟨163162297, 5, [(2, 3), (3, 3), (11, 1), (43, 1), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_1597
  · decide +kernel

theorem prime_164812601 : Nat.Prime 164812601 := by
  apply nodeValid_prime [2, 5, 824063] ⟨164812601, 3, [(2, 3), (5, 2), (824063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_824063
  · decide +kernel

theorem prime_172748971 : Nat.Prime 172748971 := by
  apply nodeValid_prime [2, 3, 5, 47, 13613] ⟨172748971, 3, [(2, 1), (3, 3), (5, 1), (47, 1), (13613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_13613
  · decide +kernel

theorem prime_230499037 : Nat.Prime 230499037 := by
  apply nodeValid_prime [2, 3, 6402751] ⟨230499037, 2, [(2, 2), (3, 2), (6402751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6402751
  · decide +kernel

theorem prime_305850637 : Nat.Prime 305850637 := by
  apply nodeValid_prime [2, 3, 7, 13, 89, 1049] ⟨305850637, 5, [(2, 2), (3, 2), (7, 1), (13, 1), (89, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_89
    · exact prime_1049
  · decide +kernel

theorem prime_329625203 : Nat.Prime 329625203 := by
  apply nodeValid_prime [2, 164812601] ⟨329625203, 2, [(2, 1), (164812601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_164812601
  · decide +kernel

theorem prime_652649189 : Nat.Prime 652649189 := by
  apply nodeValid_prime [2, 163162297] ⟨652649189, 2, [(2, 2), (163162297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163162297
  · decide +kernel

theorem prime_694671409 : Nat.Prime 694671409 := by
  apply nodeValid_prime [2, 3, 17, 283771] ⟨694671409, 14, [(2, 4), (3, 2), (17, 1), (283771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_283771
  · decide +kernel

theorem prime_748670009 : Nat.Prime 748670009 := by
  apply nodeValid_prime [2, 71, 233, 5657] ⟨748670009, 3, [(2, 3), (71, 1), (233, 1), (5657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_233
    · exact prime_5657
  · decide +kernel

theorem prime_766510187 : Nat.Prime 766510187 := by
  apply nodeValid_prime [2, 13, 89, 331249] ⟨766510187, 2, [(2, 1), (13, 1), (89, 1), (331249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_89
    · exact prime_331249
  · decide +kernel

theorem prime_881800547 : Nat.Prime 881800547 := by
  apply nodeValid_prime [2, 11, 71, 564533] ⟨881800547, 2, [(2, 1), (11, 1), (71, 1), (564533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_564533
  · decide +kernel

theorem prime_892458901 : Nat.Prime 892458901 := by
  apply nodeValid_prime [2, 3, 5, 991621] ⟨892458901, 2, [(2, 2), (3, 2), (5, 2), (991621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_991621
  · decide +kernel

theorem prime_921996149 : Nat.Prime 921996149 := by
  apply nodeValid_prime [2, 230499037] ⟨921996149, 2, [(2, 2), (230499037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_230499037
  · decide +kernel

theorem prime_1067202413 : Nat.Prime 1067202413 := by
  apply nodeValid_prime [2, 19, 14042137] ⟨1067202413, 2, [(2, 2), (19, 1), (14042137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_14042137
  · decide +kernel

theorem prime_1360908119 : Nat.Prime 1360908119 := by
  apply nodeValid_prime [2, 43, 15824513] ⟨1360908119, 7, [(2, 1), (43, 1), (15824513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_15824513
  · decide +kernel

theorem prime_1588198187 : Nat.Prime 1588198187 := by
  apply nodeValid_prime [2, 6553, 121181] ⟨1588198187, 2, [(2, 1), (6553, 1), (121181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6553
    · exact prime_121181
  · decide +kernel

theorem prime_1711494251 : Nat.Prime 1711494251 := by
  apply nodeValid_prime [2, 5, 661, 10357] ⟨1711494251, 6, [(2, 1), (5, 3), (661, 1), (10357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_661
    · exact prime_10357
  · decide +kernel

theorem prime_1914198887 : Nat.Prime 1914198887 := by
  apply nodeValid_prime [2, 293, 3266551] ⟨1914198887, 10, [(2, 1), (293, 1), (3266551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_3266551
  · decide +kernel

theorem prime_1979740247 : Nat.Prime 1979740247 := by
  apply nodeValid_prime [2, 11, 89988193] ⟨1979740247, 10, [(2, 1), (11, 1), (89988193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89988193
  · decide +kernel

theorem prime_2056019447 : Nat.Prime 2056019447 := by
  apply nodeValid_prime [2, 13, 79077671] ⟨2056019447, 5, [(2, 1), (13, 1), (79077671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79077671
  · decide +kernel

theorem prime_2193206209 : Nat.Prime 2193206209 := by
  apply nodeValid_prime [2, 3, 2069, 5521] ⟨2193206209, 11, [(2, 6), (3, 1), (2069, 1), (5521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2069
    · exact prime_5521
  · decide +kernel

theorem prime_2721816239 : Nat.Prime 2721816239 := by
  apply nodeValid_prime [2, 1360908119] ⟨2721816239, 7, [(2, 1), (1360908119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1360908119
  · decide +kernel

theorem prime_2791797793 : Nat.Prime 2791797793 := by
  apply nodeValid_prime [2, 3, 7, 4154461] ⟨2791797793, 10, [(2, 5), (3, 1), (7, 1), (4154461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4154461
  · decide +kernel

theorem prime_3038348801 : Nat.Prime 3038348801 := by
  apply nodeValid_prime [2, 5, 17, 13963] ⟨3038348801, 3, [(2, 9), (5, 2), (17, 1), (13963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_13963
  · decide +kernel

theorem prime_4614752843 : Nat.Prime 4614752843 := by
  apply nodeValid_prime [2, 7, 329625203] ⟨4614752843, 2, [(2, 1), (7, 1), (329625203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_329625203
  · decide +kernel

theorem prime_5366979461 : Nat.Prime 5366979461 := by
  apply nodeValid_prime [2, 5, 71, 89, 42467] ⟨5366979461, 2, [(2, 2), (5, 1), (71, 1), (89, 1), (42467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_89
    · exact prime_42467
  · decide +kernel

theorem prime_6833308679 : Nat.Prime 6833308679 := by
  apply nodeValid_prime [2, 7, 17, 28711381] ⟨6833308679, 7, [(2, 1), (7, 1), (17, 1), (28711381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_28711381
  · decide +kernel

theorem prime_7073940479 : Nat.Prime 7073940479 := by
  apply nodeValid_prime [2, 11, 29, 1007971] ⟨7073940479, 7, [(2, 1), (11, 2), (29, 1), (1007971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_1007971
  · decide +kernel

theorem prime_8757775363 : Nat.Prime 8757775363 := by
  apply nodeValid_prime [2, 3, 7, 47, 607, 7309] ⟨8757775363, 2, [(2, 1), (3, 1), (7, 1), (47, 1), (607, 1), (7309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_607
    · exact prime_7309
  · decide +kernel

theorem prime_9505318931 : Nat.Prime 9505318931 := by
  apply nodeValid_prime [2, 5, 137, 6938189] ⟨9505318931, 2, [(2, 1), (5, 1), (137, 1), (6938189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_6938189
  · decide +kernel

theorem prime_28784272259 : Nat.Prime 28784272259 := by
  apply nodeValid_prime [2, 7, 2056019447] ⟨28784272259, 2, [(2, 1), (7, 1), (2056019447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2056019447
  · decide +kernel

theorem prime_38799224069 : Nat.Prime 38799224069 := by
  apply nodeValid_prime [2, 11, 881800547] ⟨38799224069, 2, [(2, 2), (11, 1), (881800547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_881800547
  · decide +kernel

theorem prime_41017708819 : Nat.Prime 41017708819 := by
  apply nodeValid_prime [2, 3, 1103, 2065967] ⟨41017708819, 2, [(2, 1), (3, 2), (1103, 1), (2065967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1103
    · exact prime_2065967
  · decide +kernel

theorem prime_57568544519 : Nat.Prime 57568544519 := by
  apply nodeValid_prime [2, 28784272259] ⟨57568544519, 13, [(2, 1), (28784272259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28784272259
  · decide +kernel

theorem prime_99269299699 : Nat.Prime 99269299699 := by
  apply nodeValid_prime [2, 3, 199, 83140117] ⟨99269299699, 3, [(2, 1), (3, 1), (199, 1), (83140117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_83140117
  · decide +kernel

theorem prime_130379239937 : Nat.Prime 130379239937 := by
  apply nodeValid_prime [2, 11, 23149723] ⟨130379239937, 3, [(2, 9), (11, 1), (23149723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23149723
  · decide +kernel

theorem prime_150563886287 : Nat.Prime 150563886287 := by
  apply nodeValid_prime [2, 11, 4003, 1709671] ⟨150563886287, 5, [(2, 1), (11, 1), (4003, 1), (1709671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4003
    · exact prime_1709671
  · decide +kernel

theorem prime_164070835277 : Nat.Prime 164070835277 := by
  apply nodeValid_prime [2, 41017708819] ⟨164070835277, 2, [(2, 2), (41017708819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41017708819
  · decide +kernel

theorem prime_329517727139 : Nat.Prime 329517727139 := by
  apply nodeValid_prime [2, 17, 16097, 602081] ⟨329517727139, 2, [(2, 1), (17, 1), (16097, 1), (602081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_16097
    · exact prime_602081
  · decide +kernel

theorem prime_330621376133 : Nat.Prime 330621376133 := by
  apply nodeValid_prime [2, 29, 1249, 2281973] ⟨330621376133, 2, [(2, 2), (29, 1), (1249, 1), (2281973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1249
    · exact prime_2281973
  · decide +kernel

theorem prime_495932057051 : Nat.Prime 495932057051 := by
  apply nodeValid_prime [2, 5, 23, 71, 6073877] ⟨495932057051, 7, [(2, 1), (5, 2), (23, 1), (71, 1), (6073877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_71
    · exact prime_6073877
  · decide +kernel

theorem prime_3894985946737 : Nat.Prime 3894985946737 := by
  apply nodeValid_prime [2, 3, 67, 2729, 5479] ⟨3894985946737, 5, [(2, 4), (3, 5), (67, 1), (2729, 1), (5479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_2729
    · exact prime_5479
  · decide +kernel

theorem prime_3894985947031 : Nat.Prime 3894985947031 := by
  apply nodeValid_prime [2, 3, 5, 19, 6833308679] ⟨3894985947031, 14, [(2, 1), (3, 1), (5, 1), (19, 1), (6833308679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_6833308679
  · decide +kernel

theorem prime_3894985950673 : Nat.Prime 3894985950673 := by
  apply nodeValid_prime [2, 3, 29, 593, 1361, 3467] ⟨3894985950673, 7, [(2, 4), (3, 1), (29, 1), (593, 1), (1361, 1), (3467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_593
    · exact prime_1361
    · exact prime_3467
  · decide +kernel

theorem prime_3898260431867 : Nat.Prime 3898260431867 := by
  apply nodeValid_prime [2, 93871, 20763923] ⟨3898260431867, 2, [(2, 1), (93871, 1), (20763923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_93871
    · exact prime_20763923
  · decide +kernel

theorem prime_3898260432397 : Nat.Prime 3898260432397 := by
  apply nodeValid_prime [2, 3, 11, 199, 2579, 19181] ⟨3898260432397, 5, [(2, 2), (3, 2), (11, 1), (199, 1), (2579, 1), (19181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_199
    · exact prime_2579
    · exact prime_19181
  · decide +kernel

theorem prime_3898260479569 : Nat.Prime 3898260479569 := by
  apply nodeValid_prime [2, 3, 7, 13, 892458901] ⟨3898260479569, 17, [(2, 4), (3, 1), (7, 1), (13, 1), (892458901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_892458901
  · decide +kernel

theorem prime_3901536851831 : Nat.Prime 3901536851831 := by
  apply nodeValid_prime [2, 5, 509, 766510187] ⟨3901536851831, 11, [(2, 1), (5, 1), (509, 1), (766510187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_509
    · exact prime_766510187
  · decide +kernel

theorem prime_3901536851843 : Nat.Prime 3901536851843 := by
  apply nodeValid_prime [2, 7, 61, 652649189] ⟨3901536851843, 2, [(2, 1), (7, 2), (61, 1), (652649189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_652649189
  · decide +kernel

theorem prime_3901536870193 : Nat.Prime 3901536870193 := by
  apply nodeValid_prime [2, 3, 13, 193, 10798727] ⟨3901536870193, 5, [(2, 4), (3, 2), (13, 1), (193, 1), (10798727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_193
    · exact prime_10798727
  · decide +kernel

theorem prime_3904815123877 : Nat.Prime 3904815123877 := by
  apply nodeValid_prime [2, 3, 113, 2293, 1255847] ⟨3904815123877, 6, [(2, 2), (3, 1), (113, 1), (2293, 1), (1255847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_2293
    · exact prime_1255847
  · decide +kernel

theorem prime_3904815144409 : Nat.Prime 3904815144409 := by
  apply nodeValid_prime [2, 3, 23, 7073940479] ⟨3904815144409, 17, [(2, 3), (3, 1), (23, 1), (7073940479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_7073940479
  · decide +kernel

theorem prime_3904815145481 : Nat.Prime 3904815145481 := by
  apply nodeValid_prime [2, 5, 29, 439, 997, 7691] ⟨3904815145481, 3, [(2, 3), (5, 1), (29, 1), (439, 1), (997, 1), (7691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_439
    · exact prime_997
    · exact prime_7691
  · decide +kernel

theorem prime_3908095193969 : Nat.Prime 3908095193969 := by
  apply nodeValid_prime [2, 7, 683, 51088883] ⟨3908095193969, 3, [(2, 4), (7, 1), (683, 1), (51088883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_683
    · exact prime_51088883
  · decide +kernel

theorem prime_3908095194431 : Nat.Prime 3908095194431 := by
  apply nodeValid_prime [2, 5, 7, 2819, 19804871] ⟨3908095194431, 7, [(2, 1), (5, 1), (7, 1), (2819, 1), (19804871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2819
    · exact prime_19804871
  · decide +kernel

theorem prime_3908095236407 : Nat.Prime 3908095236407 := by
  apply nodeValid_prime [2, 1831, 1067202413] ⟨3908095236407, 5, [(2, 1), (1831, 1), (1067202413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1831
    · exact prime_1067202413
  · decide +kernel

theorem prime_3911377198013 : Nat.Prime 3911377198013 := by
  apply nodeValid_prime [2, 211, 20117, 230369] ⟨3911377198013, 2, [(2, 2), (211, 1), (20117, 1), (230369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_20117
    · exact prime_230369
  · decide +kernel

theorem prime_3911377198111 : Nat.Prime 3911377198111 := by
  apply nodeValid_prime [2, 3, 5, 130379239937] ⟨3911377198111, 6, [(2, 1), (3, 1), (5, 1), (130379239937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_130379239937
  · decide +kernel

theorem prime_3911377209161 : Nat.Prime 3911377209161 := by
  apply nodeValid_prime [2, 5, 31, 3547, 28687] ⟨3911377209161, 6, [(2, 3), (5, 1), (31, 2), (3547, 1), (28687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_3547
    · exact prime_28687
  · decide +kernel

theorem prime_3914661026273 : Nat.Prime 3914661026273 := by
  apply nodeValid_prime [2, 17, 2311, 3113833] ⟨3914661026273, 3, [(2, 5), (17, 1), (2311, 1), (3113833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2311
    · exact prime_3113833
  · decide +kernel

theorem prime_3914661027293 : Nat.Prime 3914661027293 := by
  apply nodeValid_prime [2, 17, 57568544519] ⟨3914661027293, 2, [(2, 2), (17, 1), (57568544519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_57568544519
  · decide +kernel

theorem prime_3914661043463 : Nat.Prime 3914661043463 := by
  apply nodeValid_prime [2, 13, 150563886287] ⟨3914661043463, 5, [(2, 1), (13, 1), (150563886287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_150563886287
  · decide +kernel

theorem prime_3917946659971 : Nat.Prime 3917946659971 := by
  apply nodeValid_prime [2, 3, 5, 7, 61, 305850637] ⟨3917946659971, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (305850637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_305850637
  · decide +kernel

theorem prime_3917946662281 : Nat.Prime 3917946662281 := by
  apply nodeValid_prime [2, 3, 5, 7, 172748971] ⟨3917946662281, 13, [(2, 3), (3, 4), (5, 1), (7, 1), (172748971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_172748971
  · decide +kernel

theorem prime_3917946746761 : Nat.Prime 3917946746761 := by
  apply nodeValid_prime [2, 3, 5, 47, 694671409] ⟨3917946746761, 14, [(2, 3), (3, 1), (5, 1), (47, 1), (694671409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_694671409
  · decide +kernel

theorem prime_3921234302567 : Nat.Prime 3921234302567 := by
  apply nodeValid_prime [2, 7, 68581, 4084049] ⟨3921234302567, 7, [(2, 1), (7, 1), (68581, 1), (4084049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_68581
    · exact prime_4084049
  · decide +kernel

theorem prime_3921234302861 : Nat.Prime 3921234302861 := by
  apply nodeValid_prime [2, 5, 7, 9091, 3080939] ⟨3921234302861, 2, [(2, 2), (5, 1), (7, 1), (9091, 1), (3080939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_9091
    · exact prime_3080939
  · decide +kernel

theorem prime_3921234314441 : Nat.Prime 3921234314441 := by
  apply nodeValid_prime [2, 5, 29, 397, 8514797] ⟨3921234314441, 3, [(2, 3), (5, 1), (29, 1), (397, 1), (8514797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_397
    · exact prime_8514797
  · decide +kernel

theorem prime_3924523746287 : Nat.Prime 3924523746287 := by
  apply nodeValid_prime [2, 11, 13, 263, 52175327] ⟨3924523746287, 5, [(2, 1), (11, 1), (13, 1), (263, 1), (52175327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_263
    · exact prime_52175327
  · decide +kernel

theorem prime_3924523768103 : Nat.Prime 3924523768103 := by
  apply nodeValid_prime [2, 7, 1619, 24735121] ⟨3924523768103, 5, [(2, 1), (7, 2), (1619, 1), (24735121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1619
    · exact prime_24735121
  · decide +kernel

theorem prime_3927815034901 : Nat.Prime 3927815034901 := by
  apply nodeValid_prime [2, 3, 5, 19, 8161, 84437] ⟨3927815034901, 2, [(2, 2), (3, 1), (5, 2), (19, 1), (8161, 1), (84437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_8161
    · exact prime_84437
  · decide +kernel

theorem prime_3927815034937 : Nat.Prime 3927815034937 := by
  apply nodeValid_prime [2, 3, 13, 1049, 12001097] ⟨3927815034937, 5, [(2, 3), (3, 1), (13, 1), (1049, 1), (12001097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1049
    · exact prime_12001097
  · decide +kernel

theorem prime_3927815035129 : Nat.Prime 3927815035129 := by
  apply nodeValid_prime [2, 3, 19, 743, 3864347] ⟨3927815035129, 7, [(2, 3), (3, 2), (19, 1), (743, 1), (3864347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_743
    · exact prime_3864347
  · decide +kernel

theorem prime_3931108192289 : Nat.Prime 3931108192289 := by
  apply nodeValid_prime [2, 151, 367, 2216777] ⟨3931108192289, 3, [(2, 5), (151, 1), (367, 1), (2216777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_367
    · exact prime_2216777
  · decide +kernel

theorem prime_3931108270819 : Nat.Prime 3931108270819 := by
  apply nodeValid_prime [2, 3, 1151, 3373, 168761] ⟨3931108270819, 3, [(2, 1), (3, 1), (1151, 1), (3373, 1), (168761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1151
    · exact prime_3373
    · exact prime_168761
  · decide +kernel

theorem prime_3931108274209 : Nat.Prime 3931108274209 := by
  apply nodeValid_prime [2, 3, 43, 67, 661, 21503] ⟨3931108274209, 11, [(2, 5), (3, 1), (43, 1), (67, 1), (661, 1), (21503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_67
    · exact prime_661
    · exact prime_21503
  · decide +kernel

theorem prime_3934403021539 : Nat.Prime 3934403021539 := by
  apply nodeValid_prime [2, 3, 11, 89513, 221987] ⟨3934403021539, 2, [(2, 1), (3, 2), (11, 1), (89513, 1), (221987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89513
    · exact prime_221987
  · decide +kernel

theorem prime_3934403022371 : Nat.Prime 3934403022371 := by
  apply nodeValid_prime [2, 5, 53, 101, 1129, 65101] ⟨3934403022371, 2, [(2, 1), (5, 1), (53, 1), (101, 1), (1129, 1), (65101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_101
    · exact prime_1129
    · exact prime_65101
  · decide +kernel

theorem prime_3934403228471 : Nat.Prime 3934403228471 := by
  apply nodeValid_prime [2, 5, 11, 13, 19, 433, 334427] ⟨3934403228471, 14, [(2, 1), (5, 1), (11, 1), (13, 1), (19, 1), (433, 1), (334427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_433
    · exact prime_334427
  · decide +kernel

theorem prime_3937700046097 : Nat.Prime 3937700046097 := by
  apply nodeValid_prime [2, 3, 3038348801] ⟨3937700046097, 7, [(2, 4), (3, 4), (3038348801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3038348801
  · decide +kernel

theorem prime_3937700046649 : Nat.Prime 3937700046649 := by
  apply nodeValid_prime [2, 3, 164070835277] ⟨3937700046649, 7, [(2, 3), (3, 1), (164070835277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_164070835277
  · decide +kernel

theorem prime_3937700135609 : Nat.Prime 3937700135609 := by
  apply nodeValid_prime [2, 181, 2467, 1102313] ⟨3937700135609, 3, [(2, 3), (181, 1), (2467, 1), (1102313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_2467
    · exact prime_1102313
  · decide +kernel

theorem prime_3940998913351 : Nat.Prime 3940998913351 := by
  apply nodeValid_prime [2, 3, 5, 8757775363] ⟨3940998913351, 3, [(2, 1), (3, 2), (5, 2), (8757775363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8757775363
  · decide +kernel

theorem prime_3940998927377 : Nat.Prime 3940998927377 := by
  apply nodeValid_prime [2, 7, 47, 748670009] ⟨3940998927377, 3, [(2, 4), (7, 1), (47, 1), (748670009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_748670009
  · decide +kernel

theorem prime_3940998927923 : Nat.Prime 3940998927923 := by
  apply nodeValid_prime [2, 7, 61, 4614752843] ⟨3940998927923, 2, [(2, 1), (7, 1), (61, 1), (4614752843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_4614752843
  · decide +kernel

theorem prime_3944299524559 : Nat.Prime 3944299524559 := by
  apply nodeValid_prime [2, 3, 677, 11933, 81373] ⟨3944299524559, 6, [(2, 1), (3, 1), (677, 1), (11933, 1), (81373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
    · exact prime_11933
    · exact prime_81373
  · decide +kernel

theorem prime_3944299525423 : Nat.Prime 3944299525423 := by
  apply nodeValid_prime [2, 3, 23, 31, 921996149] ⟨3944299525423, 6, [(2, 1), (3, 1), (23, 1), (31, 1), (921996149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_31
    · exact prime_921996149
  · decide +kernel

theorem prime_3944299560109 : Nat.Prime 3944299560109 := by
  apply nodeValid_prime [2, 3, 283, 739, 1571657] ⟨3944299560109, 6, [(2, 2), (3, 1), (283, 1), (739, 1), (1571657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_739
    · exact prime_1571657
  · decide +kernel

theorem prime_3947602052239 : Nat.Prime 3947602052239 := by
  apply nodeValid_prime [2, 3, 13, 601, 84210121] ⟨3947602052239, 3, [(2, 1), (3, 1), (13, 1), (601, 1), (84210121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_601
    · exact prime_84210121
  · decide +kernel

theorem prime_3947602052519 : Nat.Prime 3947602052519 := by
  apply nodeValid_prime [2, 997, 1979740247] ⟨3947602052519, 11, [(2, 1), (997, 1), (1979740247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_997
    · exact prime_1979740247
  · decide +kernel

theorem prime_3947602079303 : Nat.Prime 3947602079303 := by
  apply nodeValid_prime [2, 7, 101, 2791797793] ⟨3947602079303, 5, [(2, 1), (7, 1), (101, 1), (2791797793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_2791797793
  · decide +kernel

theorem prime_3950906470061 : Nat.Prime 3950906470061 := by
  apply nodeValid_prime [2, 5, 11, 29, 2207, 280591] ⟨3950906470061, 2, [(2, 2), (5, 1), (11, 1), (29, 1), (2207, 1), (280591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_2207
    · exact prime_280591
  · decide +kernel

theorem prime_3950906502769 : Nat.Prime 3950906502769 := by
  apply nodeValid_prime [2, 3, 43, 1914198887] ⟨3950906502769, 19, [(2, 4), (3, 1), (43, 1), (1914198887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1914198887
  · decide +kernel

theorem prime_3950906502947 : Nat.Prime 3950906502947 := by
  apply nodeValid_prime [2, 13, 29, 8573, 611213] ⟨3950906502947, 2, [(2, 1), (13, 1), (29, 1), (8573, 1), (611213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_8573
    · exact prime_611213
  · decide +kernel

theorem prime_3954212675297 : Nat.Prime 3954212675297 := by
  apply nodeValid_prime [2, 13, 9505318931] ⟨3954212675297, 3, [(2, 5), (13, 1), (9505318931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_9505318931
  · decide +kernel

theorem prime_3954212676847 : Nat.Prime 3954212676847 := by
  apply nodeValid_prime [2, 3, 39239, 5598473] ⟨3954212676847, 5, [(2, 1), (3, 2), (39239, 1), (5598473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39239
    · exact prime_5598473
  · decide +kernel

theorem prime_3954212725669 : Nat.Prime 3954212725669 := by
  apply nodeValid_prime [2, 3, 329517727139] ⟨3954212725669, 2, [(2, 2), (3, 1), (329517727139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_329517727139
  · decide +kernel

theorem prime_3957520808711 : Nat.Prime 3957520808711 := by
  apply nodeValid_prime [2, 5, 7, 577, 2477, 5651] ⟨3957520808711, 7, [(2, 1), (5, 1), (7, 2), (577, 1), (2477, 1), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_577
    · exact prime_2477
    · exact prime_5651
  · decide +kernel

theorem prime_3957520811507 : Nat.Prime 3957520811507 := by
  apply nodeValid_prime [2, 727, 2721816239] ⟨3957520811507, 2, [(2, 1), (727, 1), (2721816239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_727
    · exact prime_2721816239
  · decide +kernel

theorem prime_3957520855039 : Nat.Prime 3957520855039 := by
  apply nodeValid_prime [2, 3, 17, 38799224069] ⟨3957520855039, 3, [(2, 1), (3, 1), (17, 1), (38799224069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_38799224069
  · decide +kernel

theorem prime_3960830842219 : Nat.Prime 3960830842219 := by
  apply nodeValid_prime [2, 3, 41, 5366979461] ⟨3960830842219, 2, [(2, 1), (3, 2), (41, 1), (5366979461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_5366979461
  · decide +kernel

theorem prime_3960830993423 : Nat.Prime 3960830993423 := by
  apply nodeValid_prime [2, 73, 409, 66330023] ⟨3960830993423, 5, [(2, 1), (73, 1), (409, 1), (66330023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_409
    · exact prime_66330023
  · decide +kernel

theorem prime_3960830993993 : Nat.Prime 3960830993993 := by
  apply nodeValid_prime [2, 53, 211, 44272903] ⟨3960830993993, 3, [(2, 3), (53, 1), (211, 1), (44272903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_211
    · exact prime_44272903
  · decide +kernel

theorem prime_3964142674753 : Nat.Prime 3964142674753 := by
  apply nodeValid_prime [2, 3, 13, 1588198187] ⟨3964142674753, 11, [(2, 6), (3, 1), (13, 1), (1588198187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1588198187
  · decide +kernel

theorem prime_3964142674841 : Nat.Prime 3964142674841 := by
  apply nodeValid_prime [2, 5, 2069, 47899259] ⟨3964142674841, 3, [(2, 3), (5, 1), (2069, 1), (47899259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2069
    · exact prime_47899259
  · decide +kernel

theorem prime_3964142707697 : Nat.Prime 3964142707697 := by
  apply nodeValid_prime [2, 31, 52313, 152777] ⟨3964142707697, 3, [(2, 4), (31, 1), (52313, 1), (152777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_52313
    · exact prime_152777
  · decide +kernel

theorem prime_3967456456409 : Nat.Prime 3967456456409 := by
  apply nodeValid_prime [2, 495932057051] ⟨3967456456409, 3, [(2, 3), (495932057051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_495932057051
  · decide +kernel

theorem prime_3967456513597 : Nat.Prime 3967456513597 := by
  apply nodeValid_prime [2, 3, 330621376133] ⟨3967456513597, 2, [(2, 2), (3, 1), (330621376133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_330621376133
  · decide +kernel

theorem prime_3967456514053 : Nat.Prime 3967456514053 := by
  apply nodeValid_prime [2, 3, 71, 10321, 451181] ⟨3967456514053, 5, [(2, 2), (3, 1), (71, 1), (10321, 1), (451181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_10321
    · exact prime_451181
  · decide +kernel

theorem prime_3970771987961 : Nat.Prime 3970771987961 := by
  apply nodeValid_prime [2, 5, 99269299699] ⟨3970771987961, 6, [(2, 3), (5, 1), (99269299699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_99269299699
  · decide +kernel

theorem prime_3970771988873 : Nat.Prime 3970771988873 := by
  apply nodeValid_prime [2, 13, 79, 3203, 150889] ⟨3970771988873, 3, [(2, 3), (13, 1), (79, 1), (3203, 1), (150889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_3203
    · exact prime_150889
  · decide +kernel

theorem prime_3970772082559 : Nat.Prime 3970772082559 := by
  apply nodeValid_prime [2, 3, 31, 151, 2879, 16369] ⟨3970772082559, 3, [(2, 1), (3, 2), (31, 1), (151, 1), (2879, 1), (16369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_151
    · exact prime_2879
    · exact prime_16369
  · decide +kernel

theorem prime_3974089587509 : Nat.Prime 3974089587509 := by
  apply nodeValid_prime [2, 139, 4969, 1438447] ⟨3974089587509, 2, [(2, 2), (139, 1), (4969, 1), (1438447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_4969
    · exact prime_1438447
  · decide +kernel

theorem prime_3974089650709 : Nat.Prime 3974089650709 := by
  apply nodeValid_prime [2, 3, 151, 2193206209] ⟨3974089650709, 6, [(2, 2), (3, 1), (151, 1), (2193206209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_2193206209
  · decide +kernel

theorem prime_3974089650823 : Nat.Prime 3974089650823 := by
  apply nodeValid_prime [2, 3, 43, 1711494251] ⟨3974089650823, 3, [(2, 1), (3, 3), (43, 1), (1711494251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1711494251
  · decide +kernel

end Sude.Lucas.Generated
