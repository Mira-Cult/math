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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0119

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_12289 : Nat.Prime 12289 := by
  apply nodeValid_prime [2, 3] ⟨12289, 11, [(2, 12), (3, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_13757 : Nat.Prime 13757 := by
  apply nodeValid_prime [2, 19, 181] ⟨13757, 2, [(2, 2), (19, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_181
  · decide +kernel

theorem prime_18803 : Nat.Prime 18803 := by
  apply nodeValid_prime [2, 7, 17, 79] ⟨18803, 5, [(2, 1), (7, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_23633 : Nat.Prime 23633 := by
  apply nodeValid_prime [2, 7, 211] ⟨23633, 5, [(2, 4), (7, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
  · decide +kernel

theorem prime_23899 : Nat.Prime 23899 := by
  apply nodeValid_prime [2, 3, 7, 569] ⟨23899, 2, [(2, 1), (3, 1), (7, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_569
  · decide +kernel

theorem prime_27271 : Nat.Prime 27271 := by
  apply nodeValid_prime [2, 3, 5, 101] ⟨27271, 6, [(2, 1), (3, 3), (5, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_34369 : Nat.Prime 34369 := by
  apply nodeValid_prime [2, 3, 179] ⟨34369, 7, [(2, 6), (3, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
  · decide +kernel

theorem prime_37607 : Nat.Prime 37607 := by
  apply nodeValid_prime [2, 18803] ⟨37607, 5, [(2, 1), (18803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18803
  · decide +kernel

theorem prime_39383 : Nat.Prime 39383 := by
  apply nodeValid_prime [2, 7, 29, 97] ⟨39383, 5, [(2, 1), (7, 1), (29, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_97
  · decide +kernel

theorem prime_46307 : Nat.Prime 46307 := by
  apply nodeValid_prime [2, 13, 137] ⟨46307, 2, [(2, 1), (13, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_137
  · decide +kernel

theorem prime_52937 : Nat.Prime 52937 := by
  apply nodeValid_prime [2, 13, 509] ⟨52937, 5, [(2, 3), (13, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_509
  · decide +kernel

theorem prime_57149 : Nat.Prime 57149 := by
  apply nodeValid_prime [2, 7, 13, 157] ⟨57149, 2, [(2, 2), (7, 1), (13, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_157
  · decide +kernel

theorem prime_58711 : Nat.Prime 58711 := by
  apply nodeValid_prime [2, 3, 5, 19, 103] ⟨58711, 6, [(2, 1), (3, 1), (5, 1), (19, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_103
  · decide +kernel

theorem prime_59083 : Nat.Prime 59083 := by
  apply nodeValid_prime [2, 3, 43, 229] ⟨59083, 2, [(2, 1), (3, 1), (43, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_229
  · decide +kernel

theorem prime_65537 : Nat.Prime 65537 := by
  apply nodeValid_prime [2] ⟨65537, 3, [(2, 16)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact prime_2
  · decide +kernel

theorem prime_68311 : Nat.Prime 68311 := by
  apply nodeValid_prime [2, 3, 5, 11, 23] ⟨68311, 6, [(2, 1), (3, 3), (5, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_69073 : Nat.Prime 69073 := by
  apply nodeValid_prime [2, 3, 1439] ⟨69073, 10, [(2, 4), (3, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1439
  · decide +kernel

theorem prime_69383 : Nat.Prime 69383 := by
  apply nodeValid_prime [2, 113, 307] ⟨69383, 5, [(2, 1), (113, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_307
  · decide +kernel

theorem prime_74719 : Nat.Prime 74719 := by
  apply nodeValid_prime [2, 3, 7, 593] ⟨74719, 7, [(2, 1), (3, 2), (7, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_593
  · decide +kernel

theorem prime_87251 : Nat.Prime 87251 := by
  apply nodeValid_prime [2, 5, 349] ⟨87251, 2, [(2, 1), (5, 3), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_94033 : Nat.Prime 94033 := by
  apply nodeValid_prime [2, 3, 653] ⟨94033, 15, [(2, 4), (3, 2), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
  · decide +kernel

theorem prime_114299 : Nat.Prime 114299 := by
  apply nodeValid_prime [2, 57149] ⟨114299, 2, [(2, 1), (57149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57149
  · decide +kernel

theorem prime_116341 : Nat.Prime 116341 := by
  apply nodeValid_prime [2, 3, 5, 7, 277] ⟨116341, 14, [(2, 2), (3, 1), (5, 1), (7, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_117239 : Nat.Prime 117239 := by
  apply nodeValid_prime [2, 11, 73] ⟨117239, 11, [(2, 1), (11, 1), (73, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_163627 : Nat.Prime 163627 := by
  apply nodeValid_prime [2, 3, 27271] ⟨163627, 2, [(2, 1), (3, 1), (27271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27271
  · decide +kernel

theorem prime_171671 : Nat.Prime 171671 := by
  apply nodeValid_prime [2, 5, 17167] ⟨171671, 11, [(2, 1), (5, 1), (17167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17167
  · decide +kernel

theorem prime_187751 : Nat.Prime 187751 := by
  apply nodeValid_prime [2, 5, 751] ⟨187751, 7, [(2, 1), (5, 3), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_751
  · decide +kernel

theorem prime_236333 : Nat.Prime 236333 := by
  apply nodeValid_prime [2, 59083] ⟨236333, 2, [(2, 2), (59083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59083
  · decide +kernel

theorem prime_236377 : Nat.Prime 236377 := by
  apply nodeValid_prime [2, 3, 7, 67] ⟨236377, 10, [(2, 3), (3, 2), (7, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_310727 : Nat.Prime 310727 := by
  apply nodeValid_prime [2, 13, 17, 19, 37] ⟨310727, 7, [(2, 1), (13, 1), (17, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_319441 : Nat.Prime 319441 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨319441, 7, [(2, 4), (3, 1), (5, 1), (11, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_321709 : Nat.Prime 321709 := by
  apply nodeValid_prime [2, 3, 17, 19, 83] ⟨321709, 2, [(2, 2), (3, 1), (17, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_383459 : Nat.Prime 383459 := by
  apply nodeValid_prime [2, 19, 10091] ⟨383459, 2, [(2, 1), (19, 1), (10091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_10091
  · decide +kernel

theorem prime_389989 : Nat.Prime 389989 := by
  apply nodeValid_prime [2, 3, 23, 157] ⟨389989, 2, [(2, 2), (3, 3), (23, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_157
  · decide +kernel

theorem prime_422657 : Nat.Prime 422657 := by
  apply nodeValid_prime [2, 13, 127] ⟨422657, 3, [(2, 8), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_423497 : Nat.Prime 423497 := by
  apply nodeValid_prime [2, 52937] ⟨423497, 3, [(2, 3), (52937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_52937
  · decide +kernel

theorem prime_430289 : Nat.Prime 430289 := by
  apply nodeValid_prime [2, 26893] ⟨430289, 3, [(2, 4), (26893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26893
  · decide +kernel

theorem prime_509699 : Nat.Prime 509699 := by
  apply nodeValid_prime [2, 7, 743] ⟨509699, 2, [(2, 1), (7, 3), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_743
  · decide +kernel

theorem prime_540619 : Nat.Prime 540619 := by
  apply nodeValid_prime [2, 3, 13, 29, 239] ⟨540619, 3, [(2, 1), (3, 1), (13, 1), (29, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_239
  · decide +kernel

theorem prime_560597 : Nat.Prime 560597 := by
  apply nodeValid_prime [2, 269, 521] ⟨560597, 2, [(2, 2), (269, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_521
  · decide +kernel

theorem prime_666751 : Nat.Prime 666751 := by
  apply nodeValid_prime [2, 3, 5, 7, 127] ⟨666751, 14, [(2, 1), (3, 1), (5, 3), (7, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_743731 : Nat.Prime 743731 := by
  apply nodeValid_prime [2, 3, 5, 13, 1907] ⟨743731, 7, [(2, 1), (3, 1), (5, 1), (13, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1907
  · decide +kernel

theorem prime_825421 : Nat.Prime 825421 := by
  apply nodeValid_prime [2, 3, 5, 13757] ⟨825421, 2, [(2, 2), (3, 1), (5, 1), (13757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13757
  · decide +kernel

theorem prime_936827 : Nat.Prime 936827 := by
  apply nodeValid_prime [2, 11, 97, 439] ⟨936827, 2, [(2, 1), (11, 1), (97, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_97
    · exact prime_439
  · decide +kernel

theorem prime_950231 : Nat.Prime 950231 := by
  apply nodeValid_prime [2, 5, 167, 569] ⟨950231, 7, [(2, 1), (5, 1), (167, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_569
  · decide +kernel

theorem prime_1020707 : Nat.Prime 1020707 := by
  apply nodeValid_prime [2, 31, 101, 163] ⟨1020707, 2, [(2, 1), (31, 1), (101, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_101
    · exact prime_163
  · decide +kernel

theorem prime_1196281 : Nat.Prime 1196281 := by
  apply nodeValid_prime [2, 3, 5, 3323] ⟨1196281, 13, [(2, 3), (3, 2), (5, 1), (3323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3323
  · decide +kernel

theorem prime_1396093 : Nat.Prime 1396093 := by
  apply nodeValid_prime [2, 3, 116341] ⟨1396093, 2, [(2, 2), (3, 1), (116341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_116341
  · decide +kernel

theorem prime_1401679 : Nat.Prime 1401679 := by
  apply nodeValid_prime [2, 3, 101, 257] ⟨1401679, 3, [(2, 1), (3, 3), (101, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_257
  · decide +kernel

theorem prime_1529537 : Nat.Prime 1529537 := by
  apply nodeValid_prime [2, 23899] ⟨1529537, 3, [(2, 6), (23899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23899
  · decide +kernel

theorem prime_1557623 : Nat.Prime 1557623 := by
  apply nodeValid_prime [2, 11, 101, 701] ⟨1557623, 5, [(2, 1), (11, 1), (101, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_101
    · exact prime_701
  · decide +kernel

theorem prime_1646287 : Nat.Prime 1646287 := by
  apply nodeValid_prime [2, 3, 31, 53, 167] ⟨1646287, 6, [(2, 1), (3, 1), (31, 1), (53, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
    · exact prime_167
  · decide +kernel

theorem prime_1759607 : Nat.Prime 1759607 := by
  apply nodeValid_prime [2, 61, 14423] ⟨1759607, 5, [(2, 1), (61, 1), (14423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_14423
  · decide +kernel

theorem prime_1841087 : Nat.Prime 1841087 := by
  apply nodeValid_prime [2, 13, 419] ⟨1841087, 5, [(2, 1), (13, 3), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_419
  · decide +kernel

theorem prime_2205449 : Nat.Prime 2205449 := by
  apply nodeValid_prime [2, 7, 39383] ⟨2205449, 6, [(2, 3), (7, 1), (39383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_39383
  · decide +kernel

theorem prime_2422421 : Nat.Prime 2422421 := by
  apply nodeValid_prime [2, 5, 7, 11, 13] ⟨2422421, 10, [(2, 2), (5, 1), (7, 1), (11, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_2449963 : Nat.Prime 2449963 := by
  apply nodeValid_prime [2, 3, 131, 1039] ⟨2449963, 2, [(2, 1), (3, 2), (131, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_1039
  · decide +kernel

theorem prime_2579111 : Nat.Prime 2579111 := by
  apply nodeValid_prime [2, 5, 349, 739] ⟨2579111, 17, [(2, 1), (5, 1), (349, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
    · exact prime_739
  · decide +kernel

theorem prime_2681683 : Nat.Prime 2681683 := by
  apply nodeValid_prime [2, 3, 17, 61, 431] ⟨2681683, 5, [(2, 1), (3, 1), (17, 1), (61, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_431
  · decide +kernel

theorem prime_5305987 : Nat.Prime 5305987 := by
  apply nodeValid_prime [2, 3, 7, 4679] ⟨5305987, 2, [(2, 1), (3, 4), (7, 1), (4679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4679
  · decide +kernel

theorem prime_5928959 : Nat.Prime 5928959 := by
  apply nodeValid_prime [2, 7, 423497] ⟨5928959, 11, [(2, 1), (7, 1), (423497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_423497
  · decide +kernel

theorem prime_6948103 : Nat.Prime 6948103 := by
  apply nodeValid_prime [2, 3, 7, 23633] ⟨6948103, 3, [(2, 1), (3, 1), (7, 2), (23633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23633
  · decide +kernel

theorem prime_8597041 : Nat.Prime 8597041 := by
  apply nodeValid_prime [2, 3, 5, 113, 317] ⟨8597041, 7, [(2, 4), (3, 1), (5, 1), (113, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_317
  · decide +kernel

theorem prime_9703063 : Nat.Prime 9703063 := by
  apply nodeValid_prime [2, 3, 31, 17389] ⟨9703063, 3, [(2, 1), (3, 2), (31, 1), (17389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_17389
  · decide +kernel

theorem prime_9877723 : Nat.Prime 9877723 := by
  apply nodeValid_prime [2, 3, 1646287] ⟨9877723, 3, [(2, 1), (3, 1), (1646287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1646287
  · decide +kernel

theorem prime_10230119 : Nat.Prime 10230119 := by
  apply nodeValid_prime [2, 1201, 4259] ⟨10230119, 7, [(2, 1), (1201, 1), (4259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1201
    · exact prime_4259
  · decide +kernel

theorem prime_11396653 : Nat.Prime 11396653 := by
  apply nodeValid_prime [2, 3, 29, 32749] ⟨11396653, 2, [(2, 2), (3, 1), (29, 1), (32749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_32749
  · decide +kernel

theorem prime_11762477 : Nat.Prime 11762477 := by
  apply nodeValid_prime [2, 11, 23, 59, 197] ⟨11762477, 2, [(2, 2), (11, 1), (23, 1), (59, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_59
    · exact prime_197
  · decide +kernel

theorem prime_12945841 : Nat.Prime 12945841 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 167] ⟨12945841, 33, [(2, 4), (3, 1), (5, 1), (17, 1), (19, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_167
  · decide +kernel

theorem prime_16310369 : Nat.Prime 16310369 := by
  apply nodeValid_prime [2, 509699] ⟨16310369, 3, [(2, 5), (509699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_509699
  · decide +kernel

theorem prime_18669029 : Nat.Prime 18669029 := by
  apply nodeValid_prime [2, 7, 666751] ⟨18669029, 2, [(2, 2), (7, 1), (666751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_666751
  · decide +kernel

theorem prime_19302541 : Nat.Prime 19302541 := by
  apply nodeValid_prime [2, 3, 5, 321709] ⟨19302541, 2, [(2, 2), (3, 1), (5, 1), (321709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_321709
  · decide +kernel

theorem prime_20460239 : Nat.Prime 20460239 := by
  apply nodeValid_prime [2, 10230119] ⟨20460239, 7, [(2, 1), (10230119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10230119
  · decide +kernel

theorem prime_22311931 : Nat.Prime 22311931 := by
  apply nodeValid_prime [2, 3, 5, 743731] ⟨22311931, 2, [(2, 1), (3, 1), (5, 1), (743731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_743731
  · decide +kernel

theorem prime_29783959 : Nat.Prime 29783959 := by
  apply nodeValid_prime [2, 3, 41, 2953] ⟨29783959, 3, [(2, 1), (3, 1), (41, 2), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2953
  · decide +kernel

theorem prime_47865221 : Nat.Prime 47865221 := by
  apply nodeValid_prime [2, 5, 13, 227, 811] ⟨47865221, 3, [(2, 2), (5, 1), (13, 1), (227, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_227
    · exact prime_811
  · decide +kernel

theorem prime_53059871 : Nat.Prime 53059871 := by
  apply nodeValid_prime [2, 5, 5305987] ⟨53059871, 7, [(2, 1), (5, 1), (5305987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5305987
  · decide +kernel

theorem prime_56178757 : Nat.Prime 56178757 := by
  apply nodeValid_prime [2, 3, 73, 21377] ⟨56178757, 2, [(2, 2), (3, 2), (73, 1), (21377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_21377
  · decide +kernel

theorem prime_73072507 : Nat.Prime 73072507 := by
  apply nodeValid_prime [2, 3, 13, 936827] ⟨73072507, 5, [(2, 1), (3, 1), (13, 1), (936827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_936827
  · decide +kernel

theorem prime_77675047 : Nat.Prime 77675047 := by
  apply nodeValid_prime [2, 3, 12945841] ⟨77675047, 3, [(2, 1), (3, 1), (12945841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12945841
  · decide +kernel

theorem prime_93732367 : Nat.Prime 93732367 := by
  apply nodeValid_prime [2, 3, 7, 13, 171671] ⟨93732367, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (171671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_171671
  · decide +kernel

theorem prime_197572777 : Nat.Prime 197572777 := by
  apply nodeValid_prime [2, 3, 17, 683, 709] ⟨197572777, 5, [(2, 3), (3, 1), (17, 1), (683, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_683
    · exact prime_709
  · decide +kernel

theorem prime_220741841 : Nat.Prime 220741841 := by
  apply nodeValid_prime [2, 5, 11, 71, 3533] ⟨220741841, 3, [(2, 4), (5, 1), (11, 1), (71, 1), (3533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_71
    · exact prime_3533
  · decide +kernel

theorem prime_250131709 : Nat.Prime 250131709 := by
  apply nodeValid_prime [2, 3, 6948103] ⟨250131709, 2, [(2, 2), (3, 2), (6948103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6948103
  · decide +kernel

theorem prime_250726367 : Nat.Prime 250726367 := by
  apply nodeValid_prime [2, 11, 11396653] ⟨250726367, 5, [(2, 1), (11, 1), (11396653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11396653
  · decide +kernel

theorem prime_337861289 : Nat.Prime 337861289 := by
  apply nodeValid_prime [2, 1123, 37607] ⟨337861289, 3, [(2, 3), (1123, 1), (37607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1123
    · exact prime_37607
  · decide +kernel

theorem prime_448965323 : Nat.Prime 448965323 := by
  apply nodeValid_prime [2, 13, 43, 313, 1283] ⟨448965323, 2, [(2, 1), (13, 1), (43, 1), (313, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_313
    · exact prime_1283
  · decide +kernel

theorem prime_713504527 : Nat.Prime 713504527 := by
  apply nodeValid_prime [2, 3, 7, 1283, 13241] ⟨713504527, 3, [(2, 1), (3, 1), (7, 1), (1283, 1), (13241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1283
    · exact prime_13241
  · decide +kernel

theorem prime_831902171 : Nat.Prime 831902171 := by
  apply nodeValid_prime [2, 5, 11, 109, 69383] ⟨831902171, 2, [(2, 1), (5, 1), (11, 1), (109, 1), (69383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_109
    · exact prime_69383
  · decide +kernel

theorem prime_1294484623 : Nat.Prime 1294484623 := by
  apply nodeValid_prime [2, 3, 47, 67, 131, 523] ⟨1294484623, 3, [(2, 1), (3, 1), (47, 1), (67, 1), (131, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_67
    · exact prime_131
    · exact prime_523
  · decide +kernel

theorem prime_2352909187 : Nat.Prime 2352909187 := by
  apply nodeValid_prime [2, 3, 71, 1841087] ⟨2352909187, 5, [(2, 1), (3, 2), (71, 1), (1841087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_1841087
  · decide +kernel

theorem prime_2513610389 : Nat.Prime 2513610389 := by
  apply nodeValid_prime [2, 3347, 187751] ⟨2513610389, 2, [(2, 2), (3347, 1), (187751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3347
    · exact prime_187751
  · decide +kernel

theorem prime_3258367907 : Nat.Prime 3258367907 := by
  apply nodeValid_prime [2, 29, 56178757] ⟨3258367907, 2, [(2, 1), (29, 1), (56178757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_56178757
  · decide +kernel

theorem prime_5266500013 : Nat.Prime 5266500013 := by
  apply nodeValid_prime [2, 3, 2753, 17713] ⟨5266500013, 2, [(2, 2), (3, 3), (2753, 1), (17713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2753
    · exact prime_17713
  · decide +kernel

theorem prime_5513315167 : Nat.Prime 5513315167 := by
  apply nodeValid_prime [2, 3, 37, 47, 58711] ⟨5513315167, 3, [(2, 1), (3, 3), (37, 1), (47, 1), (58711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_47
    · exact prime_58711
  · decide +kernel

theorem prime_8625091399 : Nat.Prime 8625091399 := by
  apply nodeValid_prime [2, 3, 7, 11, 18669029] ⟨8625091399, 11, [(2, 1), (3, 1), (7, 1), (11, 1), (18669029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_18669029
  · decide +kernel

theorem prime_9411636749 : Nat.Prime 9411636749 := by
  apply nodeValid_prime [2, 2352909187] ⟨9411636749, 2, [(2, 2), (2352909187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2352909187
  · decide +kernel

theorem prime_12446183447 : Nat.Prime 12446183447 := by
  apply nodeValid_prime [2, 17, 10651, 34369] ⟨12446183447, 5, [(2, 1), (17, 1), (10651, 1), (34369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_10651
    · exact prime_34369
  · decide +kernel

theorem prime_12603974549 : Nat.Prime 12603974549 := by
  apply nodeValid_prime [2, 11, 29, 9877723] ⟨12603974549, 3, [(2, 2), (11, 1), (29, 1), (9877723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_9877723
  · decide +kernel

theorem prime_16179555653 : Nat.Prime 16179555653 := by
  apply nodeValid_prime [2, 13, 127, 2449963] ⟨16179555653, 2, [(2, 2), (13, 1), (127, 1), (2449963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_127
    · exact prime_2449963
  · decide +kernel

theorem prime_18952711469 : Nat.Prime 18952711469 := by
  apply nodeValid_prime [2, 61, 77675047] ⟨18952711469, 2, [(2, 2), (61, 1), (77675047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_77675047
  · decide +kernel

theorem prime_35702294057 : Nat.Prime 35702294057 := by
  apply nodeValid_prime [2, 11, 13, 4931, 6329] ⟨35702294057, 3, [(2, 3), (11, 1), (13, 1), (4931, 1), (6329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_4931
    · exact prime_6329
  · decide +kernel

theorem prime_37105345439 : Nat.Prime 37105345439 := by
  apply nodeValid_prime [2, 7, 37, 1093, 65537] ⟨37105345439, 7, [(2, 1), (7, 1), (37, 1), (1093, 1), (65537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_1093
    · exact prime_65537
  · decide +kernel

theorem prime_98947589407 : Nat.Prime 98947589407 := by
  apply nodeValid_prime [2, 3, 653, 1193, 21169] ⟨98947589407, 29, [(2, 1), (3, 1), (653, 1), (1193, 1), (21169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
    · exact prime_1193
    · exact prime_21169
  · decide +kernel

theorem prime_101665452433 : Nat.Prime 101665452433 := by
  apply nodeValid_prime [2, 3, 5431, 389989] ⟨101665452433, 5, [(2, 4), (3, 1), (5431, 1), (389989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5431
    · exact prime_389989
  · decide +kernel

theorem prime_106054478591 : Nat.Prime 106054478591 := by
  apply nodeValid_prime [2, 5, 1093, 9703063] ⟨106054478591, 17, [(2, 1), (5, 1), (1093, 1), (9703063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1093
    · exact prime_9703063
  · decide +kernel

theorem prime_297068099077 : Nat.Prime 297068099077 := by
  apply nodeValid_prime [2, 3, 7, 1753, 74719] ⟨297068099077, 5, [(2, 2), (3, 4), (7, 1), (1753, 1), (74719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1753
    · exact prime_74719
  · decide +kernel

theorem prime_377902174829 : Nat.Prime 377902174829 := by
  apply nodeValid_prime [2, 89, 2467, 430289] ⟨377902174829, 2, [(2, 2), (89, 1), (2467, 1), (430289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_2467
    · exact prime_430289
  · decide +kernel

theorem prime_380786731799 : Nat.Prime 380786731799 := by
  apply nodeValid_prime [2, 11, 463, 5471, 6833] ⟨380786731799, 11, [(2, 1), (11, 1), (463, 1), (5471, 1), (6833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_463
    · exact prime_5471
    · exact prime_6833
  · decide +kernel

theorem prime_438540460133 : Nat.Prime 438540460133 := by
  apply nodeValid_prime [2, 523, 887, 236333] ⟨438540460133, 2, [(2, 2), (523, 1), (887, 1), (236333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_523
    · exact prime_887
    · exact prime_236333
  · decide +kernel

theorem prime_2653379605661 : Nat.Prime 2653379605661 := by
  apply nodeValid_prime [2, 5, 7, 18952711469] ⟨2653379605661, 2, [(2, 2), (5, 1), (7, 1), (18952711469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_18952711469
  · decide +kernel

theorem prime_2661460384889 : Nat.Prime 2661460384889 := by
  apply nodeValid_prime [2, 257, 1294484623] ⟨2661460384889, 3, [(2, 3), (257, 1), (1294484623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_1294484623
  · decide +kernel

theorem prime_5258473101997 : Nat.Prime 5258473101997 := by
  apply nodeValid_prime [2, 3, 1297, 337861289] ⟨5258473101997, 2, [(2, 2), (3, 1), (1297, 1), (337861289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1297
    · exact prime_337861289
  · decide +kernel

theorem prime_5258473179061 : Nat.Prime 5258473179061 := by
  apply nodeValid_prime [2, 3, 5, 1831, 47865221] ⟨5258473179061, 2, [(2, 2), (3, 1), (5, 1), (1831, 1), (47865221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1831
    · exact prime_47865221
  · decide +kernel

theorem prime_5258473179877 : Nat.Prime 5258473179877 := by
  apply nodeValid_prime [2, 3, 7, 53, 79, 94033] ⟨5258473179877, 2, [(2, 2), (3, 2), (7, 1), (53, 2), (79, 1), (94033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_79
    · exact prime_94033
  · decide +kernel

theorem prime_5262485486761 : Nat.Prime 5262485486761 := by
  apply nodeValid_prime [2, 3, 5, 37, 263, 293, 1709] ⟨5262485486761, 7, [(2, 3), (3, 3), (5, 1), (37, 1), (263, 1), (293, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_263
    · exact prime_293
    · exact prime_1709
  · decide +kernel

theorem prime_5262485489441 : Nat.Prime 5262485489441 := by
  apply nodeValid_prime [2, 5, 149, 220741841] ⟨5262485489441, 6, [(2, 5), (5, 1), (149, 1), (220741841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_220741841
  · decide +kernel

theorem prime_5262485521597 : Nat.Prime 5262485521597 := by
  apply nodeValid_prime [2, 3, 438540460133] ⟨5262485521597, 6, [(2, 2), (3, 1), (438540460133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_438540460133
  · decide +kernel

theorem prime_5266499943713 : Nat.Prime 5266499943713 := by
  apply nodeValid_prime [2, 7, 17, 197572777] ⟨5266499943713, 3, [(2, 5), (7, 2), (17, 1), (197572777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_197572777
  · decide +kernel

theorem prime_5266500013001 : Nat.Prime 5266500013001 := by
  apply nodeValid_prime [2, 5, 5266500013] ⟨5266500013001, 3, [(2, 3), (5, 3), (5266500013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5266500013
  · decide +kernel

theorem prime_5270516579441 : Nat.Prime 5270516579441 := by
  apply nodeValid_prime [2, 5, 7, 9411636749] ⟨5270516579441, 6, [(2, 4), (5, 1), (7, 1), (9411636749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_9411636749
  · decide +kernel

theorem prime_5270516645923 : Nat.Prime 5270516645923 := by
  apply nodeValid_prime [2, 3, 11, 1301, 20460239] ⟨5270516645923, 2, [(2, 1), (3, 2), (11, 1), (1301, 1), (20460239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1301
    · exact prime_20460239
  · decide +kernel

theorem prime_5270516646613 : Nat.Prime 5270516646613 := by
  apply nodeValid_prime [2, 3, 7, 163627, 383459] ⟨5270516646613, 6, [(2, 2), (3, 1), (7, 1), (163627, 1), (383459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_163627
    · exact prime_383459
  · decide +kernel

theorem prime_5274535142879 : Nat.Prime 5274535142879 := by
  apply nodeValid_prime [2, 163, 16179555653] ⟨5274535142879, 7, [(2, 1), (163, 1), (16179555653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_16179555653
  · decide +kernel

theorem prime_5274535143497 : Nat.Prime 5274535143497 := by
  apply nodeValid_prime [2, 34157, 19302541] ⟨5274535143497, 3, [(2, 3), (34157, 1), (19302541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_34157
    · exact prime_19302541
  · decide +kernel

theorem prime_5274535217407 : Nat.Prime 5274535217407 := by
  apply nodeValid_prime [2, 3, 7, 13, 107, 167, 540619] ⟨5274535217407, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (107, 1), (167, 1), (540619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_107
    · exact prime_167
    · exact prime_540619
  · decide +kernel

theorem prime_5278555936189 : Nat.Prime 5278555936189 := by
  apply nodeValid_prime [2, 3, 17, 8625091399] ⟨5278555936189, 10, [(2, 2), (3, 2), (17, 1), (8625091399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8625091399
  · decide +kernel

theorem prime_5278556009341 : Nat.Prime 5278556009341 := by
  apply nodeValid_prime [2, 3, 5, 3258367907] ⟨5278556009341, 10, [(2, 2), (3, 4), (5, 1), (3258367907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3258367907
  · decide +kernel

theorem prime_5278556009383 : Nat.Prime 5278556009383 := by
  apply nodeValid_prime [2, 3, 83, 331, 1607, 19927] ⟨5278556009383, 13, [(2, 1), (3, 1), (83, 1), (331, 1), (1607, 1), (19927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_331
    · exact prime_1607
    · exact prime_19927
  · decide +kernel

theorem prime_5282578725913 : Nat.Prime 5282578725913 := by
  apply nodeValid_prime [2, 3, 31, 173, 2683, 5099] ⟨5282578725913, 5, [(2, 3), (3, 2), (31, 1), (173, 1), (2683, 1), (5099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_173
    · exact prime_2683
    · exact prime_5099
  · decide +kernel

theorem prime_5282578785329 : Nat.Prime 5282578785329 := by
  apply nodeValid_prime [2, 13, 41, 701, 719, 1229] ⟨5282578785329, 3, [(2, 4), (13, 1), (41, 1), (701, 1), (719, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_701
    · exact prime_719
    · exact prime_1229
  · decide +kernel

theorem prime_5282578785851 : Nat.Prime 5282578785851 := by
  apply nodeValid_prime [2, 5, 127, 831902171] ⟨5282578785851, 2, [(2, 1), (5, 2), (127, 1), (831902171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_831902171
  · decide +kernel

theorem prime_5286603523787 : Nat.Prime 5286603523787 := by
  apply nodeValid_prime [2, 13, 29, 47, 467, 319441] ⟨5286603523787, 2, [(2, 1), (13, 1), (29, 1), (47, 1), (467, 1), (319441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_47
    · exact prime_467
    · exact prime_319441
  · decide +kernel

theorem prime_5286603526517 : Nat.Prime 5286603526517 := by
  apply nodeValid_prime [2, 13, 101665452433] ⟨5286603526517, 2, [(2, 2), (13, 1), (101665452433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_101665452433
  · decide +kernel

theorem prime_5286603593857 : Nat.Prime 5286603593857 := by
  apply nodeValid_prime [2, 3, 13, 1283, 825421] ⟨5286603593857, 5, [(2, 7), (3, 1), (13, 1), (1283, 1), (825421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1283
    · exact prime_825421
  · decide +kernel

theorem prime_5290630446947 : Nat.Prime 5290630446947 := by
  apply nodeValid_prime [2, 13, 167, 503, 2422421] ⟨5290630446947, 2, [(2, 1), (13, 1), (167, 1), (503, 1), (2422421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_167
    · exact prime_503
    · exact prime_2422421
  · decide +kernel

theorem prime_5290630447607 : Nat.Prime 5290630447607 := by
  apply nodeValid_prime [2, 7, 377902174829] ⟨5290630447607, 5, [(2, 1), (7, 1), (377902174829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_377902174829
  · decide +kernel

theorem prime_5290630552741 : Nat.Prime 5290630552741 := by
  apply nodeValid_prime [2, 3, 5, 13, 83, 263, 310727] ⟨5290630552741, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (83, 1), (263, 1), (310727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_83
    · exact prime_263
    · exact prime_310727
  · decide +kernel

theorem prime_5294659587583 : Nat.Prime 5294659587583 := by
  apply nodeValid_prime [2, 3, 823, 12289, 87251] ⟨5294659587583, 5, [(2, 1), (3, 1), (823, 1), (12289, 1), (87251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_823
    · exact prime_12289
    · exact prime_87251
  · decide +kernel

theorem prime_5294659640617 : Nat.Prime 5294659640617 := by
  apply nodeValid_prime [2, 3, 15737, 1557623] ⟨5294659640617, 5, [(2, 3), (3, 3), (15737, 1), (1557623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15737
    · exact prime_1557623
  · decide +kernel

theorem prime_5294659640671 : Nat.Prime 5294659640671 := by
  apply nodeValid_prime [2, 3, 5, 2281, 8597041] ⟨5294659640671, 3, [(2, 1), (3, 3), (5, 1), (2281, 1), (8597041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2281
    · exact prime_8597041
  · decide +kernel

theorem prime_5298690700013 : Nat.Prime 5298690700013 := by
  apply nodeValid_prime [2, 17, 31, 2513610389] ⟨5298690700013, 2, [(2, 2), (17, 1), (31, 1), (2513610389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_2513610389
  · decide +kernel

theorem prime_5298690700049 : Nat.Prime 5298690700049 := by
  apply nodeValid_prime [2, 61, 46307, 117239] ⟨5298690700049, 3, [(2, 4), (61, 1), (46307, 1), (117239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_46307
    · exact prime_117239
  · decide +kernel

theorem prime_5298690706511 : Nat.Prime 5298690706511 := by
  apply nodeValid_prime [2, 5, 5653, 93732367] ⟨5298690706511, 13, [(2, 1), (5, 1), (5653, 1), (93732367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5653
    · exact prime_93732367
  · decide +kernel

theorem prime_5302723883207 : Nat.Prime 5302723883207 := by
  apply nodeValid_prime [2, 149, 157, 2053, 55207] ⟨5302723883207, 5, [(2, 1), (149, 1), (157, 1), (2053, 1), (55207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_157
    · exact prime_2053
    · exact prime_55207
  · decide +kernel

theorem prime_5302723929551 : Nat.Prime 5302723929551 := by
  apply nodeValid_prime [2, 5, 106054478591] ⟨5302723929551, 11, [(2, 1), (5, 2), (106054478591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_106054478591
  · decide +kernel

theorem prime_5302723929637 : Nat.Prime 5302723929637 := by
  apply nodeValid_prime [2, 3, 7, 23, 2689, 1020707] ⟨5302723929637, 2, [(2, 2), (3, 1), (7, 1), (23, 1), (2689, 1), (1020707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_2689
    · exact prime_1020707
  · decide +kernel

theorem prime_5306759123321 : Nat.Prime 5306759123321 := by
  apply nodeValid_prime [2, 5, 11279, 11762477] ⟨5306759123321, 3, [(2, 3), (5, 1), (11279, 1), (11762477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11279
    · exact prime_11762477
  · decide +kernel

theorem prime_5306759211323 : Nat.Prime 5306759211323 := by
  apply nodeValid_prime [2, 2653379605661] ⟨5306759211323, 2, [(2, 1), (2653379605661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2653379605661
  · decide +kernel

theorem prime_5306759212241 : Nat.Prime 5306759212241 := by
  apply nodeValid_prime [2, 5, 31, 1399, 1529537] ⟨5306759212241, 3, [(2, 4), (5, 1), (31, 1), (1399, 1), (1529537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1399
    · exact prime_1529537
  · decide +kernel

theorem prime_5310796407853 : Nat.Prime 5310796407853 := by
  apply nodeValid_prime [2, 3, 13, 73, 101, 787, 5867] ⟨5310796407853, 5, [(2, 2), (3, 1), (13, 1), (73, 1), (101, 1), (787, 1), (5867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_101
    · exact prime_787
    · exact prime_5867
  · decide +kernel

theorem prime_5310796407907 : Nat.Prime 5310796407907 := by
  apply nodeValid_prime [2, 3, 11, 57637, 1396093] ⟨5310796407907, 2, [(2, 1), (3, 1), (11, 1), (57637, 1), (1396093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_57637
    · exact prime_1396093
  · decide +kernel

theorem prime_5310796445489 : Nat.Prime 5310796445489 := by
  apply nodeValid_prime [2, 1327, 250131709] ⟨5310796445489, 3, [(2, 4), (1327, 1), (250131709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1327
    · exact prime_250131709
  · decide +kernel

theorem prime_5314835820989 : Nat.Prime 5314835820989 := by
  apply nodeValid_prime [2, 241, 5513315167] ⟨5314835820989, 2, [(2, 2), (241, 1), (5513315167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_5513315167
  · decide +kernel

theorem prime_5314835835787 : Nat.Prime 5314835835787 := by
  apply nodeValid_prime [2, 3, 29, 37, 22311931] ⟨5314835835787, 2, [(2, 1), (3, 1), (29, 1), (37, 2), (22311931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_37
    · exact prime_22311931
  · decide +kernel

theorem prime_5318877259679 : Nat.Prime 5318877259679 := by
  apply nodeValid_prime [2, 211, 12603974549] ⟨5318877259679, 7, [(2, 1), (211, 1), (12603974549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_12603974549
  · decide +kernel

theorem prime_5318877260237 : Nat.Prime 5318877260237 := by
  apply nodeValid_prime [2, 73, 97, 2749, 68311] ⟨5318877260237, 2, [(2, 2), (73, 1), (97, 1), (2749, 1), (68311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_97
    · exact prime_2749
    · exact prime_68311
  · decide +kernel

theorem prime_5318877304567 : Nat.Prime 5318877304567 := by
  apply nodeValid_prime [2, 3, 7, 127, 167, 293, 6793] ⟨5318877304567, 3, [(2, 1), (3, 2), (7, 1), (127, 1), (167, 1), (293, 1), (6793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127
    · exact prime_167
    · exact prime_293
    · exact prime_6793
  · decide +kernel

theorem prime_5322920769779 : Nat.Prime 5322920769779 := by
  apply nodeValid_prime [2, 2661460384889] ⟨5322920769779, 2, [(2, 1), (2661460384889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2661460384889
  · decide +kernel

theorem prime_5322920771411 : Nat.Prime 5322920771411 := by
  apply nodeValid_prime [2, 5, 11, 193, 250726367] ⟨5322920771411, 6, [(2, 1), (5, 1), (11, 1), (193, 1), (250726367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_193
    · exact prime_250726367
  · decide +kernel

theorem prime_5322920856229 : Nat.Prime 5322920856229 := by
  apply nodeValid_prime [2, 3, 37, 2851, 1401679] ⟨5322920856229, 2, [(2, 2), (3, 2), (37, 1), (2851, 1), (1401679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2851
    · exact prime_1401679
  · decide +kernel

theorem prime_5326966479071 : Nat.Prime 5326966479071 := by
  apply nodeValid_prime [2, 5, 560597, 950231] ⟨5326966479071, 31, [(2, 1), (5, 1), (560597, 1), (950231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_560597
    · exact prime_950231
  · decide +kernel

theorem prime_5326966515317 : Nat.Prime 5326966515317 := by
  apply nodeValid_prime [2, 107, 12446183447] ⟨5326966515317, 2, [(2, 2), (107, 1), (12446183447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_12446183447
  · decide +kernel

theorem prime_5326966515401 : Nat.Prime 5326966515401 := by
  apply nodeValid_prime [2, 5, 23, 71, 16310369] ⟨5326966515401, 3, [(2, 3), (5, 2), (23, 1), (71, 1), (16310369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_71
    · exact prime_16310369
  · decide +kernel

theorem prime_5331014176289 : Nat.Prime 5331014176289 := by
  apply nodeValid_prime [2, 23, 37, 73, 2681683] ⟨5331014176289, 6, [(2, 5), (23, 1), (37, 1), (73, 1), (2681683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_73
    · exact prime_2681683
  · decide +kernel

theorem prime_5331014245187 : Nat.Prime 5331014245187 := by
  apply nodeValid_prime [2, 7, 380786731799] ⟨5331014245187, 2, [(2, 1), (7, 1), (380786731799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_380786731799
  · decide +kernel

theorem prime_5331014245303 : Nat.Prime 5331014245303 := by
  apply nodeValid_prime [2, 3, 1979, 448965323] ⟨5331014245303, 3, [(2, 1), (3, 1), (1979, 1), (448965323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1979
    · exact prime_448965323
  · decide +kernel

theorem prime_5335063909309 : Nat.Prime 5335063909309 := by
  apply nodeValid_prime [2, 3, 7, 19, 53059871] ⟨5335063909309, 10, [(2, 2), (3, 3), (7, 2), (19, 1), (53059871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_53059871
  · decide +kernel

theorem prime_5335063909601 : Nat.Prime 5335063909601 := by
  apply nodeValid_prime [2, 5, 17, 53, 727, 10181] ⟨5335063909601, 3, [(2, 5), (5, 2), (17, 1), (53, 1), (727, 1), (10181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_53
    · exact prime_727
    · exact prime_10181
  · decide +kernel

theorem prime_5335063945949 : Nat.Prime 5335063945949 := by
  apply nodeValid_prime [2, 11, 79, 1283, 1196281] ⟨5335063945949, 2, [(2, 2), (11, 1), (79, 1), (1283, 1), (1196281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79
    · exact prime_1283
    · exact prime_1196281
  · decide +kernel

theorem prime_5339115685769 : Nat.Prime 5339115685769 := by
  apply nodeValid_prime [2, 1229, 4751, 114299] ⟨5339115685769, 3, [(2, 3), (1229, 1), (4751, 1), (114299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1229
    · exact prime_4751
    · exact prime_114299
  · decide +kernel

theorem prime_5339115687319 : Nat.Prime 5339115687319 := by
  apply nodeValid_prime [2, 3, 7, 23, 2143, 2579111] ⟨5339115687319, 3, [(2, 1), (3, 1), (7, 1), (23, 1), (2143, 1), (2579111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_2143
    · exact prime_2579111
  · decide +kernel

theorem prime_5339115796463 : Nat.Prime 5339115796463 := by
  apply nodeValid_prime [2, 7, 17, 307, 73072507] ⟨5339115796463, 5, [(2, 1), (7, 1), (17, 1), (307, 1), (73072507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_307
    · exact prime_73072507
  · decide +kernel

theorem prime_5343169743217 : Nat.Prime 5343169743217 := by
  apply nodeValid_prime [2, 3, 37105345439] ⟨5343169743217, 7, [(2, 4), (3, 2), (37105345439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37105345439
  · decide +kernel

theorem prime_5343169827979 : Nat.Prime 5343169827979 := by
  apply nodeValid_prime [2, 3, 98947589407] ⟨5343169827979, 2, [(2, 1), (3, 3), (98947589407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_98947589407
  · decide +kernel

theorem prime_5343169827991 : Nat.Prime 5343169827991 := by
  apply nodeValid_prime [2, 3, 5, 127, 797, 1759607] ⟨5343169827991, 6, [(2, 1), (3, 1), (5, 1), (127, 1), (797, 1), (1759607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
    · exact prime_797
    · exact prime_1759607
  · decide +kernel

theorem prime_5347225783387 : Nat.Prime 5347225783387 := by
  apply nodeValid_prime [2, 3, 297068099077] ⟨5347225783387, 2, [(2, 1), (3, 2), (297068099077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_297068099077
  · decide +kernel

theorem prime_5347225783849 : Nat.Prime 5347225783849 := by
  apply nodeValid_prime [2, 3, 13, 19, 409, 2205449] ⟨5347225783849, 7, [(2, 3), (3, 1), (13, 1), (19, 1), (409, 1), (2205449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_409
    · exact prime_2205449
  · decide +kernel

theorem prime_5347225787801 : Nat.Prime 5347225787801 := by
  apply nodeValid_prime [2, 5, 13, 17, 19, 53, 6323] ⟨5347225787801, 3, [(2, 3), (5, 2), (13, 1), (17, 1), (19, 2), (53, 1), (6323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_53
    · exact prime_6323
  · decide +kernel

theorem prime_5351283913531 : Nat.Prime 5351283913531 := by
  apply nodeValid_prime [2, 3, 5, 53, 113, 29783959] ⟨5351283913531, 2, [(2, 1), (3, 1), (5, 1), (53, 1), (113, 1), (29783959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_113
    · exact prime_29783959
  · decide +kernel

theorem prime_5351283945793 : Nat.Prime 5351283945793 := by
  apply nodeValid_prime [2, 3, 17, 431, 422657] ⟨5351283945793, 5, [(2, 6), (3, 3), (17, 1), (431, 1), (422657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_431
    · exact prime_422657
  · decide +kernel

theorem prime_5351283952501 : Nat.Prime 5351283952501 := by
  apply nodeValid_prime [2, 3, 5, 713504527] ⟨5351283952501, 6, [(2, 2), (3, 1), (5, 4), (713504527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_713504527
  · decide +kernel

theorem prime_5355344074669 : Nat.Prime 5355344074669 := by
  apply nodeValid_prime [2, 3, 7, 10753, 5928959] ⟨5355344074669, 2, [(2, 2), (3, 1), (7, 1), (10753, 1), (5928959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10753
    · exact prime_5928959
  · decide +kernel

theorem prime_5355344074889 : Nat.Prime 5355344074889 := by
  apply nodeValid_prime [2, 41, 69073, 236377] ⟨5355344074889, 3, [(2, 3), (41, 1), (69073, 1), (236377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_69073
    · exact prime_236377
  · decide +kernel

theorem prime_5355344108551 : Nat.Prime 5355344108551 := by
  apply nodeValid_prime [2, 3, 5, 35702294057] ⟨5355344108551, 3, [(2, 1), (3, 1), (5, 2), (35702294057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35702294057
  · decide +kernel

end Sude.Lucas.Generated
