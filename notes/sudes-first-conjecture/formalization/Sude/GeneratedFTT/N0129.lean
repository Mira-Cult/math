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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0113

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11927 : Nat.Prime 11927 := by
  apply nodeValid_prime [2, 67, 89] ⟨11927, 5, [(2, 1), (67, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_89
  · decide +kernel

theorem prime_21499 : Nat.Prime 21499 := by
  apply nodeValid_prime [2, 3, 3583] ⟨21499, 3, [(2, 1), (3, 1), (3583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3583
  · decide +kernel

theorem prime_25579 : Nat.Prime 25579 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨25579, 2, [(2, 1), (3, 2), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_27611 : Nat.Prime 27611 := by
  apply nodeValid_prime [2, 5, 11, 251] ⟨27611, 2, [(2, 1), (5, 1), (11, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_251
  · decide +kernel

theorem prime_39041 : Nat.Prime 39041 := by
  apply nodeValid_prime [2, 5, 61] ⟨39041, 3, [(2, 7), (5, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_53717 : Nat.Prime 53717 := by
  apply nodeValid_prime [2, 13, 1033] ⟨53717, 2, [(2, 2), (13, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1033
  · decide +kernel

theorem prime_56531 : Nat.Prime 56531 := by
  apply nodeValid_prime [2, 5, 5653] ⟨56531, 2, [(2, 1), (5, 1), (5653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5653
  · decide +kernel

theorem prime_60647 : Nat.Prime 60647 := by
  apply nodeValid_prime [2, 30323] ⟨60647, 5, [(2, 1), (30323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30323
  · decide +kernel

theorem prime_63467 : Nat.Prime 63467 := by
  apply nodeValid_prime [2, 13, 2441] ⟨63467, 2, [(2, 1), (13, 1), (2441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2441
  · decide +kernel

theorem prime_69401 : Nat.Prime 69401 := by
  apply nodeValid_prime [2, 5, 347] ⟨69401, 6, [(2, 3), (5, 2), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_347
  · decide +kernel

theorem prime_93683 : Nat.Prime 93683 := by
  apply nodeValid_prime [2, 31, 1511] ⟨93683, 2, [(2, 1), (31, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1511
  · decide +kernel

theorem prime_93979 : Nat.Prime 93979 := by
  apply nodeValid_prime [2, 3, 23, 227] ⟨93979, 3, [(2, 1), (3, 2), (23, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_227
  · decide +kernel

theorem prime_95311 : Nat.Prime 95311 := by
  apply nodeValid_prime [2, 3, 5, 353] ⟨95311, 3, [(2, 1), (3, 3), (5, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
  · decide +kernel

theorem prime_98453 : Nat.Prime 98453 := by
  apply nodeValid_prime [2, 151, 163] ⟨98453, 2, [(2, 2), (151, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_163
  · decide +kernel

theorem prime_113063 : Nat.Prime 113063 := by
  apply nodeValid_prime [2, 56531] ⟨113063, 5, [(2, 1), (56531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56531
  · decide +kernel

theorem prime_129497 : Nat.Prime 129497 := by
  apply nodeValid_prime [2, 16187] ⟨129497, 3, [(2, 3), (16187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16187
  · decide +kernel

theorem prime_137567 : Nat.Prime 137567 := by
  apply nodeValid_prime [2, 11, 13, 37] ⟨137567, 10, [(2, 1), (11, 1), (13, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_171271 : Nat.Prime 171271 := by
  apply nodeValid_prime [2, 3, 5, 11, 173] ⟨171271, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_173
  · decide +kernel

theorem prime_187367 : Nat.Prime 187367 := by
  apply nodeValid_prime [2, 93683] ⟨187367, 5, [(2, 1), (93683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93683
  · decide +kernel

theorem prime_196043 : Nat.Prime 196043 := by
  apply nodeValid_prime [2, 7, 11, 19, 67] ⟨196043, 5, [(2, 1), (7, 1), (11, 1), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_213929 : Nat.Prime 213929 := by
  apply nodeValid_prime [2, 11, 13, 17] ⟨213929, 6, [(2, 3), (11, 2), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_227699 : Nat.Prime 227699 := by
  apply nodeValid_prime [2, 17, 37, 181] ⟨227699, 2, [(2, 1), (17, 1), (37, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_181
  · decide +kernel

theorem prime_246707 : Nat.Prime 246707 := by
  apply nodeValid_prime [2, 293, 421] ⟨246707, 2, [(2, 1), (293, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_421
  · decide +kernel

theorem prime_246731 : Nat.Prime 246731 := by
  apply nodeValid_prime [2, 5, 11, 2243] ⟨246731, 2, [(2, 1), (5, 1), (11, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2243
  · decide +kernel

theorem prime_294949 : Nat.Prime 294949 := by
  apply nodeValid_prime [2, 3, 2731] ⟨294949, 2, [(2, 2), (3, 3), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2731
  · decide +kernel

theorem prime_328849 : Nat.Prime 328849 := by
  apply nodeValid_prime [2, 3, 13, 17, 31] ⟨328849, 7, [(2, 4), (3, 1), (13, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_338461 : Nat.Prime 338461 := by
  apply nodeValid_prime [2, 3, 5, 5641] ⟨338461, 2, [(2, 2), (3, 1), (5, 1), (5641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5641
  · decide +kernel

theorem prime_342697 : Nat.Prime 342697 := by
  apply nodeValid_prime [2, 3, 109, 131] ⟨342697, 5, [(2, 3), (3, 1), (109, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_131
  · decide +kernel

theorem prime_374317 : Nat.Prime 374317 := by
  apply nodeValid_prime [2, 3, 31193] ⟨374317, 2, [(2, 2), (3, 1), (31193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31193
  · decide +kernel

theorem prime_392087 : Nat.Prime 392087 := by
  apply nodeValid_prime [2, 196043] ⟨392087, 5, [(2, 1), (196043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_196043
  · decide +kernel

theorem prime_410233 : Nat.Prime 410233 := by
  apply nodeValid_prime [2, 3, 17093] ⟨410233, 5, [(2, 3), (3, 1), (17093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17093
  · decide +kernel

theorem prime_548629 : Nat.Prime 548629 := by
  apply nodeValid_prime [2, 3, 131, 349] ⟨548629, 2, [(2, 2), (3, 1), (131, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_349
  · decide +kernel

theorem prime_680507 : Nat.Prime 680507 := by
  apply nodeValid_prime [2, 59, 73, 79] ⟨680507, 2, [(2, 1), (59, 1), (73, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_73
    · exact prime_79
  · decide +kernel

theorem prime_886129 : Nat.Prime 886129 := by
  apply nodeValid_prime [2, 3, 18461] ⟨886129, 7, [(2, 4), (3, 1), (18461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18461
  · decide +kernel

theorem prime_918877 : Nat.Prime 918877 := by
  apply nodeValid_prime [2, 3, 7, 10939] ⟨918877, 2, [(2, 2), (3, 1), (7, 1), (10939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10939
  · decide +kernel

theorem prime_965953 : Nat.Prime 965953 := by
  apply nodeValid_prime [2, 3, 13, 43] ⟨965953, 5, [(2, 6), (3, 3), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_983329 : Nat.Prime 983329 := by
  apply nodeValid_prime [2, 3, 10243] ⟨983329, 22, [(2, 5), (3, 1), (10243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10243
  · decide +kernel

theorem prime_987299 : Nat.Prime 987299 := by
  apply nodeValid_prime [2, 13, 23, 127] ⟨987299, 2, [(2, 1), (13, 2), (23, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_127
  · decide +kernel

theorem prime_1015067 : Nat.Prime 1015067 := by
  apply nodeValid_prime [2, 13, 39041] ⟨1015067, 2, [(2, 1), (13, 1), (39041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_39041
  · decide +kernel

theorem prime_1035977 : Nat.Prime 1035977 := by
  apply nodeValid_prime [2, 129497] ⟨1035977, 3, [(2, 3), (129497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_129497
  · decide +kernel

theorem prime_1345859 : Nat.Prime 1345859 := by
  apply nodeValid_prime [2, 89, 7561] ⟨1345859, 2, [(2, 1), (89, 1), (7561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_7561
  · decide +kernel

theorem prime_1462327 : Nat.Prime 1462327 := by
  apply nodeValid_prime [2, 3, 251, 971] ⟨1462327, 3, [(2, 1), (3, 1), (251, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_971
  · decide +kernel

theorem prime_1580651 : Nat.Prime 1580651 := by
  apply nodeValid_prime [2, 5, 101, 313] ⟨1580651, 2, [(2, 1), (5, 2), (101, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_313
  · decide +kernel

theorem prime_1753229 : Nat.Prime 1753229 := by
  apply nodeValid_prime [2, 163, 2689] ⟨1753229, 2, [(2, 2), (163, 1), (2689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_2689
  · decide +kernel

theorem prime_1992673 : Nat.Prime 1992673 := by
  apply nodeValid_prime [2, 3, 11, 17, 37] ⟨1992673, 10, [(2, 5), (3, 2), (11, 1), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_2054971 : Nat.Prime 2054971 := by
  apply nodeValid_prime [2, 3, 5, 43, 59] ⟨2054971, 2, [(2, 1), (3, 4), (5, 1), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_2269931 : Nat.Prime 2269931 := by
  apply nodeValid_prime [2, 5, 13, 19, 919] ⟨2269931, 2, [(2, 1), (5, 1), (13, 1), (19, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_919
  · decide +kernel

theorem prime_3187787 : Nat.Prime 3187787 := by
  apply nodeValid_prime [2, 7, 227699] ⟨3187787, 2, [(2, 1), (7, 1), (227699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227699
  · decide +kernel

theorem prime_3386167 : Nat.Prime 3386167 := by
  apply nodeValid_prime [2, 3, 7, 37, 2179] ⟨3386167, 5, [(2, 1), (3, 1), (7, 1), (37, 1), (2179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_2179
  · decide +kernel

theorem prime_3396233 : Nat.Prime 3396233 := by
  apply nodeValid_prime [2, 7, 60647] ⟨3396233, 3, [(2, 3), (7, 1), (60647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_60647
  · decide +kernel

theorem prime_3439901 : Nat.Prime 3439901 := by
  apply nodeValid_prime [2, 5, 41, 839] ⟨3439901, 2, [(2, 2), (5, 2), (41, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_839
  · decide +kernel

theorem prime_3557821 : Nat.Prime 3557821 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 197] ⟨3557821, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_197
  · decide +kernel

theorem prime_3573503 : Nat.Prime 3573503 := by
  apply nodeValid_prime [2, 17, 61, 1723] ⟨3573503, 5, [(2, 1), (17, 1), (61, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_1723
  · decide +kernel

theorem prime_3812441 : Nat.Prime 3812441 := by
  apply nodeValid_prime [2, 5, 95311] ⟨3812441, 7, [(2, 3), (5, 1), (95311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_95311
  · decide +kernel

theorem prime_3890771 : Nat.Prime 3890771 := by
  apply nodeValid_prime [2, 5, 13, 173] ⟨3890771, 2, [(2, 1), (5, 1), (13, 1), (173, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_173
  · decide +kernel

theorem prime_4263863 : Nat.Prime 4263863 := by
  apply nodeValid_prime [2, 109, 19559] ⟨4263863, 5, [(2, 1), (109, 1), (19559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_19559
  · decide +kernel

theorem prime_4606487 : Nat.Prime 4606487 := by
  apply nodeValid_prime [2, 23, 239, 419] ⟨4606487, 5, [(2, 1), (23, 1), (239, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_239
    · exact prime_419
  · decide +kernel

theorem prime_4782607 : Nat.Prime 4782607 := by
  apply nodeValid_prime [2, 3, 373, 2137] ⟨4782607, 3, [(2, 1), (3, 1), (373, 1), (2137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_2137
  · decide +kernel

theorem prime_5947901 : Nat.Prime 5947901 := by
  apply nodeValid_prime [2, 5, 7, 29, 293] ⟨5947901, 3, [(2, 2), (5, 2), (7, 1), (29, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_293
  · decide +kernel

theorem prime_6431683 : Nat.Prime 6431683 := by
  apply nodeValid_prime [2, 3, 43, 97, 257] ⟨6431683, 5, [(2, 1), (3, 1), (43, 1), (97, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_97
    · exact prime_257
  · decide +kernel

theorem prime_6563729 : Nat.Prime 6563729 := by
  apply nodeValid_prime [2, 410233] ⟨6563729, 3, [(2, 4), (410233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_410233
  · decide +kernel

theorem prime_7970693 : Nat.Prime 7970693 := by
  apply nodeValid_prime [2, 1992673] ⟨7970693, 2, [(2, 2), (1992673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1992673
  · decide +kernel

theorem prime_9875323 : Nat.Prime 9875323 := by
  apply nodeValid_prime [2, 3, 548629] ⟨9875323, 2, [(2, 1), (3, 2), (548629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_548629
  · decide +kernel

theorem prime_13544669 : Nat.Prime 13544669 := by
  apply nodeValid_prime [2, 3386167] ⟨13544669, 2, [(2, 2), (3386167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3386167
  · decide +kernel

theorem prime_13772611 : Nat.Prime 13772611 := by
  apply nodeValid_prime [2, 3, 5, 137, 1117] ⟨13772611, 2, [(2, 1), (3, 2), (5, 1), (137, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_1117
  · decide +kernel

theorem prime_14086819 : Nat.Prime 14086819 := by
  apply nodeValid_prime [2, 3, 353, 739] ⟨14086819, 3, [(2, 1), (3, 3), (353, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353
    · exact prime_739
  · decide +kernel

theorem prime_16548577 : Nat.Prime 16548577 := by
  apply nodeValid_prime [2, 3, 11, 15671] ⟨16548577, 5, [(2, 5), (3, 1), (11, 1), (15671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_15671
  · decide +kernel

theorem prime_21633239 : Nat.Prime 21633239 := by
  apply nodeValid_prime [2, 11, 983329] ⟨21633239, 11, [(2, 1), (11, 1), (983329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_983329
  · decide +kernel

theorem prime_24659653 : Nat.Prime 24659653 := by
  apply nodeValid_prime [2, 3, 2054971] ⟨24659653, 2, [(2, 2), (3, 1), (2054971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2054971
  · decide +kernel

theorem prime_25583179 : Nat.Prime 25583179 := by
  apply nodeValid_prime [2, 3, 4263863] ⟨25583179, 2, [(2, 1), (3, 1), (4263863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4263863
  · decide +kernel

theorem prime_28618013 : Nat.Prime 28618013 := by
  apply nodeValid_prime [2, 29, 246707] ⟨28618013, 2, [(2, 2), (29, 1), (246707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_246707
  · decide +kernel

theorem prime_30128387 : Nat.Prime 30128387 := by
  apply nodeValid_prime [2, 17, 886129] ⟨30128387, 2, [(2, 1), (17, 1), (886129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_886129
  · decide +kernel

theorem prime_38518939 : Nat.Prime 38518939 := by
  apply nodeValid_prime [2, 3, 61, 35081] ⟨38518939, 3, [(2, 1), (3, 2), (61, 1), (35081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_35081
  · decide +kernel

theorem prime_43794887 : Nat.Prime 43794887 := by
  apply nodeValid_prime [2, 19, 107, 10771] ⟨43794887, 5, [(2, 1), (19, 1), (107, 1), (10771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_107
    · exact prime_10771
  · decide +kernel

theorem prime_44043491 : Nat.Prime 44043491 := by
  apply nodeValid_prime [2, 5, 563, 7823] ⟨44043491, 2, [(2, 1), (5, 1), (563, 1), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_563
    · exact prime_7823
  · decide +kernel

theorem prime_44629019 : Nat.Prime 44629019 := by
  apply nodeValid_prime [2, 7, 3187787] ⟨44629019, 2, [(2, 1), (7, 1), (3187787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3187787
  · decide +kernel

theorem prime_53765659 : Nat.Prime 53765659 := by
  apply nodeValid_prime [2, 3, 1531, 1951] ⟨53765659, 2, [(2, 1), (3, 2), (1531, 1), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1531
    · exact prime_1951
  · decide +kernel

theorem prime_68369123 : Nat.Prime 68369123 := by
  apply nodeValid_prime [2, 101, 338461] ⟨68369123, 2, [(2, 1), (101, 1), (338461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_338461
  · decide +kernel

theorem prime_81796933 : Nat.Prime 81796933 := by
  apply nodeValid_prime [2, 3, 7, 257, 421] ⟨81796933, 2, [(2, 2), (3, 3), (7, 1), (257, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_257
    · exact prime_421
  · decide +kernel

theorem prime_85291541 : Nat.Prime 85291541 := by
  apply nodeValid_prime [2, 5, 31, 137567] ⟨85291541, 2, [(2, 2), (5, 1), (31, 1), (137567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_137567
  · decide +kernel

theorem prime_96089039 : Nat.Prime 96089039 := by
  apply nodeValid_prime [2, 757, 63467] ⟨96089039, 7, [(2, 1), (757, 1), (63467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_757
    · exact prime_63467
  · decide +kernel

theorem prime_109708399 : Nat.Prime 109708399 := by
  apply nodeValid_prime [2, 3, 1327, 1531] ⟨109708399, 3, [(2, 1), (3, 3), (1327, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1327
    · exact prime_1531
  · decide +kernel

theorem prime_128081557 : Nat.Prime 128081557 := by
  apply nodeValid_prime [2, 3, 3557821] ⟨128081557, 2, [(2, 2), (3, 2), (3557821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3557821
  · decide +kernel

theorem prime_136738247 : Nat.Prime 136738247 := by
  apply nodeValid_prime [2, 68369123] ⟨136738247, 5, [(2, 1), (68369123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68369123
  · decide +kernel

theorem prime_204225353 : Nat.Prime 204225353 := by
  apply nodeValid_prime [2, 17, 97, 113, 137] ⟨204225353, 5, [(2, 3), (17, 1), (97, 1), (113, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97
    · exact prime_113
    · exact prime_137
  · decide +kernel

theorem prime_207806111 : Nat.Prime 207806111 := by
  apply nodeValid_prime [2, 5, 53, 392087] ⟨207806111, 7, [(2, 1), (5, 1), (53, 1), (392087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_392087
  · decide +kernel

theorem prime_243319907 : Nat.Prime 243319907 := by
  apply nodeValid_prime [2, 1753, 69401] ⟨243319907, 2, [(2, 1), (1753, 1), (69401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1753
    · exact prime_69401
  · decide +kernel

theorem prime_255831791 : Nat.Prime 255831791 := by
  apply nodeValid_prime [2, 5, 25583179] ⟨255831791, 13, [(2, 1), (5, 1), (25583179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25583179
  · decide +kernel

theorem prime_277391207 : Nat.Prime 277391207 := by
  apply nodeValid_prime [2, 29, 4782607] ⟨277391207, 5, [(2, 1), (29, 1), (4782607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_4782607
  · decide +kernel

theorem prime_302865347 : Nat.Prime 302865347 := by
  apply nodeValid_prime [2, 7, 21633239] ⟨302865347, 2, [(2, 1), (7, 1), (21633239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_21633239
  · decide +kernel

theorem prime_373619219 : Nat.Prime 373619219 := by
  apply nodeValid_prime [2, 7, 3812441] ⟨373619219, 2, [(2, 1), (7, 2), (3812441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3812441
  · decide +kernel

theorem prime_400641271 : Nat.Prime 400641271 := by
  apply nodeValid_prime [2, 3, 5, 59, 461, 491] ⟨400641271, 6, [(2, 1), (3, 1), (5, 1), (59, 1), (461, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_461
    · exact prime_491
  · decide +kernel

theorem prime_438360757 : Nat.Prime 438360757 := by
  apply nodeValid_prime [2, 3, 37, 987299] ⟨438360757, 5, [(2, 2), (3, 1), (37, 1), (987299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_987299
  · decide +kernel

theorem prime_567188747 : Nat.Prime 567188747 := by
  apply nodeValid_prime [2, 11087, 25579] ⟨567188747, 2, [(2, 1), (11087, 1), (25579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11087
    · exact prime_25579
  · decide +kernel

theorem prime_591831673 : Nat.Prime 591831673 := by
  apply nodeValid_prime [2, 3, 24659653] ⟨591831673, 5, [(2, 3), (3, 1), (24659653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24659653
  · decide +kernel

theorem prime_659989903 : Nat.Prime 659989903 := by
  apply nodeValid_prime [2, 3, 11, 13, 69929] ⟨659989903, 3, [(2, 1), (3, 1), (11, 2), (13, 1), (69929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_69929
  · decide +kernel

theorem prime_926812087 : Nat.Prime 926812087 := by
  apply nodeValid_prime [2, 3, 17, 2243, 4051] ⟨926812087, 3, [(2, 1), (3, 1), (17, 1), (2243, 1), (4051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2243
    · exact prime_4051
  · decide +kernel

theorem prime_1146568849 : Nat.Prime 1146568849 := by
  apply nodeValid_prime [2, 3, 1783, 13397] ⟨1146568849, 7, [(2, 4), (3, 1), (1783, 1), (13397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1783
    · exact prime_13397
  · decide +kernel

theorem prime_1596455083 : Nat.Prime 1596455083 := by
  apply nodeValid_prime [2, 3, 53, 61979] ⟨1596455083, 3, [(2, 1), (3, 5), (53, 1), (61979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_61979
  · decide +kernel

theorem prime_2632851209 : Nat.Prime 2632851209 := by
  apply nodeValid_prime [2, 13, 2857, 8861] ⟨2632851209, 6, [(2, 3), (13, 1), (2857, 1), (8861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2857
    · exact prime_8861
  · decide +kernel

theorem prime_3746030779 : Nat.Prime 3746030779 := by
  apply nodeValid_prime [2, 3, 7, 53, 97, 5783] ⟨3746030779, 2, [(2, 1), (3, 2), (7, 1), (53, 1), (97, 1), (5783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_97
    · exact prime_5783
  · decide +kernel

theorem prime_3784900099 : Nat.Prime 3784900099 := by
  apply nodeValid_prime [2, 3, 7, 83, 163, 6661] ⟨3784900099, 7, [(2, 1), (3, 1), (7, 1), (83, 1), (163, 1), (6661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_163
    · exact prime_6661
  · decide +kernel

theorem prime_3928931779 : Nat.Prime 3928931779 := by
  apply nodeValid_prime [2, 3, 17, 38518939] ⟨3928931779, 10, [(2, 1), (3, 1), (17, 1), (38518939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_38518939
  · decide +kernel

theorem prime_6140990953 : Nat.Prime 6140990953 := by
  apply nodeValid_prime [2, 3, 85291541] ⟨6140990953, 5, [(2, 3), (3, 2), (85291541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_85291541
  · decide +kernel

theorem prime_8321736211 : Nat.Prime 8321736211 := by
  apply nodeValid_prime [2, 3, 5, 277391207] ⟨8321736211, 3, [(2, 1), (3, 1), (5, 1), (277391207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_277391207
  · decide +kernel

theorem prime_8966861257 : Nat.Prime 8966861257 := by
  apply nodeValid_prime [2, 3, 373619219] ⟨8966861257, 5, [(2, 3), (3, 1), (373619219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373619219
  · decide +kernel

theorem prime_9995965723 : Nat.Prime 9995965723 := by
  apply nodeValid_prime [2, 3, 41, 13544669] ⟨9995965723, 2, [(2, 1), (3, 2), (41, 1), (13544669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_13544669
  · decide +kernel

theorem prime_12051694861 : Nat.Prime 12051694861 := by
  apply nodeValid_prime [2, 3, 5, 5711, 35171] ⟨12051694861, 2, [(2, 2), (3, 1), (5, 1), (5711, 1), (35171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5711
    · exact prime_35171
  · decide +kernel

theorem prime_17052667043 : Nat.Prime 17052667043 := by
  apply nodeValid_prime [2, 283, 30128387] ⟨17052667043, 2, [(2, 1), (283, 1), (30128387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_30128387
  · decide +kernel

theorem prime_17229019123 : Nat.Prime 17229019123 := by
  apply nodeValid_prime [2, 3, 7, 136738247] ⟨17229019123, 3, [(2, 1), (3, 2), (7, 1), (136738247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_136738247
  · decide +kernel

theorem prime_18719941243 : Nat.Prime 18719941243 := by
  apply nodeValid_prime [2, 3, 907, 3439901] ⟨18719941243, 2, [(2, 1), (3, 1), (907, 1), (3439901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
    · exact prime_3439901
  · decide +kernel

theorem prime_23655249269 : Nat.Prime 23655249269 := by
  apply nodeValid_prime [2, 7, 43, 677, 29021] ⟨23655249269, 3, [(2, 2), (7, 1), (43, 1), (677, 1), (29021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_677
    · exact prime_29021
  · decide +kernel

theorem prime_41841902789 : Nat.Prime 41841902789 := by
  apply nodeValid_prime [2, 7, 13217, 113063] ⟨41841902789, 2, [(2, 2), (7, 1), (13217, 1), (113063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13217
    · exact prime_113063
  · decide +kernel

theorem prime_90722427727 : Nat.Prime 90722427727 := by
  apply nodeValid_prime [2, 3, 7, 271, 7970693] ⟨90722427727, 5, [(2, 1), (3, 1), (7, 1), (271, 1), (7970693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_271
    · exact prime_7970693
  · decide +kernel

theorem prime_116554216871 : Nat.Prime 116554216871 := by
  apply nodeValid_prime [2, 5, 7, 13, 128081557] ⟨116554216871, 7, [(2, 1), (5, 1), (7, 1), (13, 1), (128081557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_128081557
  · decide +kernel

theorem prime_161403502627 : Nat.Prime 161403502627 := by
  apply nodeValid_prime [2, 3, 8966861257] ⟨161403502627, 2, [(2, 1), (3, 2), (8966861257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8966861257
  · decide +kernel

theorem prime_162838418467 : Nat.Prime 162838418467 := by
  apply nodeValid_prime [2, 3, 17, 1596455083] ⟨162838418467, 2, [(2, 1), (3, 1), (17, 1), (1596455083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1596455083
  · decide +kernel

theorem prime_192684518203 : Nat.Prime 192684518203 := by
  apply nodeValid_prime [2, 3, 11, 1847, 1580651] ⟨192684518203, 3, [(2, 1), (3, 1), (11, 1), (1847, 1), (1580651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1847
    · exact prime_1580651
  · decide +kernel

theorem prime_416572301633 : Nat.Prime 416572301633 := by
  apply nodeValid_prime [2, 34739, 187367] ⟨416572301633, 3, [(2, 6), (34739, 1), (187367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_34739
    · exact prime_187367
  · decide +kernel

theorem prime_487796010043 : Nat.Prime 487796010043 := by
  apply nodeValid_prime [2, 3, 11, 223, 4483, 7393] ⟨487796010043, 5, [(2, 1), (3, 1), (11, 1), (223, 1), (4483, 1), (7393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_223
    · exact prime_4483
    · exact prime_7393
  · decide +kernel

theorem prime_972719315501 : Nat.Prime 972719315501 := by
  apply nodeValid_prime [2, 5, 197, 9875323] ⟨972719315501, 2, [(2, 2), (5, 3), (197, 1), (9875323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
    · exact prime_9875323
  · decide +kernel

theorem prime_974154933811 : Nat.Prime 974154933811 := by
  apply nodeValid_prime [2, 3, 5, 53, 204225353] ⟨974154933811, 2, [(2, 1), (3, 2), (5, 1), (53, 1), (204225353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_204225353
  · decide +kernel

theorem prime_978470447741 : Nat.Prime 978470447741 := by
  apply nodeValid_prime [2, 5, 23, 151, 14086819] ⟨978470447741, 2, [(2, 2), (5, 1), (23, 1), (151, 1), (14086819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_151
    · exact prime_14086819
  · decide +kernel

theorem prime_1447273433497 : Nat.Prime 1447273433497 := by
  apply nodeValid_prime [2, 3, 11, 1409, 3890771] ⟨1447273433497, 5, [(2, 3), (3, 1), (11, 1), (1409, 1), (3890771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1409
    · exact prime_3890771
  · decide +kernel

theorem prime_1469867745943 : Nat.Prime 1469867745943 := by
  apply nodeValid_prime [2, 3, 367, 821, 30113] ⟨1469867745943, 3, [(2, 1), (3, 4), (367, 1), (821, 1), (30113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_821
    · exact prime_30113
  · decide +kernel

theorem prime_2907409517123 : Nat.Prime 2907409517123 := by
  apply nodeValid_prime [2, 11, 233, 567188747] ⟨2907409517123, 2, [(2, 1), (11, 1), (233, 1), (567188747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_233
    · exact prime_567188747
  · decide +kernel

theorem prime_2939735483831 : Nat.Prime 2939735483831 := by
  apply nodeValid_prime [2, 5, 167, 18731, 93979] ⟨2939735483831, 11, [(2, 1), (5, 1), (167, 1), (18731, 1), (93979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_18731
    · exact prime_93979
  · decide +kernel

theorem prime_5776259743921 : Nat.Prime 5776259743921 := by
  apply nodeValid_prime [2, 3, 5, 29, 28618013] ⟨5776259743921, 19, [(2, 4), (3, 1), (5, 1), (29, 2), (28618013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_28618013
  · decide +kernel

theorem prime_5776259809007 : Nat.Prime 5776259809007 := by
  apply nodeValid_prime [2, 53717, 53765659] ⟨5776259809007, 5, [(2, 1), (53717, 1), (53765659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53717
    · exact prime_53765659
  · decide +kernel

theorem prime_5776259810701 : Nat.Prime 5776259810701 := by
  apply nodeValid_prime [2, 3, 5, 23, 167, 571, 8779] ⟨5776259810701, 2, [(2, 2), (3, 1), (5, 2), (23, 1), (167, 1), (571, 1), (8779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_167
    · exact prime_571
    · exact prime_8779
  · decide +kernel

theorem prime_5780535543311 : Nat.Prime 5780535543311 := by
  apply nodeValid_prime [2, 5, 11, 479, 109708399] ⟨5780535543311, 11, [(2, 1), (5, 1), (11, 1), (479, 1), (109708399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_479
    · exact prime_109708399
  · decide +kernel

theorem prime_5780535546091 : Nat.Prime 5780535546091 := by
  apply nodeValid_prime [2, 3, 5, 192684518203] ⟨5780535546091, 3, [(2, 1), (3, 1), (5, 1), (192684518203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_192684518203
  · decide +kernel

theorem prime_5780535546479 : Nat.Prime 5780535546479 := by
  apply nodeValid_prime [2, 7, 11, 17, 379, 342697] ⟨5780535546479, 11, [(2, 1), (7, 1), (11, 1), (17, 2), (379, 1), (342697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_379
    · exact prime_342697
  · decide +kernel

theorem prime_5784813477727 : Nat.Prime 5784813477727 := by
  apply nodeValid_prime [2, 3, 157, 6140990953] ⟨5784813477727, 3, [(2, 1), (3, 1), (157, 1), (6140990953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_6140990953
  · decide +kernel

theorem prime_5784813529993 : Nat.Prime 5784813529993 := by
  apply nodeValid_prime [2, 3, 7, 47, 167, 1462327] ⟨5784813529993, 5, [(2, 3), (3, 2), (7, 1), (47, 1), (167, 1), (1462327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_167
    · exact prime_1462327
  · decide +kernel

theorem prime_5784813533281 : Nat.Prime 5784813533281 := by
  apply nodeValid_prime [2, 3, 5, 12051694861] ⟨5784813533281, 14, [(2, 5), (3, 1), (5, 1), (12051694861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12051694861
  · decide +kernel

theorem prime_5789093551471 : Nat.Prime 5789093551471 := by
  apply nodeValid_prime [2, 3, 5, 73, 137, 6431683] ⟨5789093551471, 6, [(2, 1), (3, 2), (5, 1), (73, 1), (137, 1), (6431683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_137
    · exact prime_6431683
  · decide +kernel

theorem prime_5789093733923 : Nat.Prime 5789093733923 := by
  apply nodeValid_prime [2, 79, 171271, 213929] ⟨5789093733923, 2, [(2, 1), (79, 1), (171271, 1), (213929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_171271
    · exact prime_213929
  · decide +kernel

theorem prime_5789093733989 : Nat.Prime 5789093733989 := by
  apply nodeValid_prime [2, 1447273433497] ⟨5789093733989, 2, [(2, 2), (1447273433497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1447273433497
  · decide +kernel

theorem prime_5793375760993 : Nat.Prime 5793375760993 := by
  apply nodeValid_prime [2, 3, 5923, 3396233] ⟨5793375760993, 5, [(2, 5), (3, 2), (5923, 1), (3396233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5923
    · exact prime_3396233
  · decide +kernel

theorem prime_5793375764327 : Nat.Prime 5793375764327 := by
  apply nodeValid_prime [2, 227, 953, 2111, 6343] ⟨5793375764327, 5, [(2, 1), (227, 1), (953, 1), (2111, 1), (6343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_953
    · exact prime_2111
    · exact prime_6343
  · decide +kernel

theorem prime_5793375764513 : Nat.Prime 5793375764513 := by
  apply nodeValid_prime [2, 7, 59, 438360757] ⟨5793375764513, 3, [(2, 5), (7, 1), (59, 1), (438360757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_438360757
  · decide +kernel

theorem prime_5797660047383 : Nat.Prime 5797660047383 := by
  apply nodeValid_prime [2, 7, 89899, 4606487] ⟨5797660047383, 5, [(2, 1), (7, 1), (89899, 1), (4606487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89899
    · exact prime_4606487
  · decide +kernel

theorem prime_5797660047643 : Nat.Prime 5797660047643 := by
  apply nodeValid_prime [2, 3, 1259, 255831791] ⟨5797660047643, 2, [(2, 1), (3, 2), (1259, 1), (255831791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1259
    · exact prime_255831791
  · decide +kernel

theorem prime_5797660119341 : Nat.Prime 5797660119341 := by
  apply nodeValid_prime [2, 5, 29, 9995965723] ⟨5797660119341, 2, [(2, 2), (5, 1), (29, 1), (9995965723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_9995965723
  · decide +kernel

theorem prime_5801946617807 : Nat.Prime 5801946617807 := by
  apply nodeValid_prime [2, 17, 53, 3573503] ⟨5801946617807, 5, [(2, 1), (17, 2), (53, 2), (3573503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_53
    · exact prime_3573503
  · decide +kernel

theorem prime_5801946619121 : Nat.Prime 5801946619121 := by
  apply nodeValid_prime [2, 5, 349, 207806111] ⟨5801946619121, 3, [(2, 4), (5, 1), (349, 1), (207806111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
    · exact prime_207806111
  · decide +kernel

theorem prime_5801946629761 : Nat.Prime 5801946629761 := by
  apply nodeValid_prime [2, 3, 5, 23, 43794887] ⟨5801946629761, 19, [(2, 7), (3, 2), (5, 1), (23, 1), (43794887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_43794887
  · decide +kernel

theorem prime_5806235291027 : Nat.Prime 5806235291027 := by
  apply nodeValid_prime [2, 257, 1721, 6563729] ⟨5806235291027, 2, [(2, 1), (257, 1), (1721, 1), (6563729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_1721
    · exact prime_6563729
  · decide +kernel

theorem prime_5806235371901 : Nat.Prime 5806235371901 := by
  apply nodeValid_prime [2, 5, 1301, 44629019] ⟨5806235371901, 2, [(2, 2), (5, 2), (1301, 1), (44629019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1301
    · exact prime_44629019
  · decide +kernel

theorem prime_5806235374529 : Nat.Prime 5806235374529 := by
  apply nodeValid_prime [2, 90722427727] ⟨5806235374529, 3, [(2, 6), (90722427727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90722427727
  · decide +kernel

theorem prime_5810526059491 : Nat.Prime 5810526059491 := by
  apply nodeValid_prime [2, 3, 5, 22279, 965953] ⟨5810526059491, 12, [(2, 1), (3, 3), (5, 1), (22279, 1), (965953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22279
    · exact prime_965953
  · decide +kernel

theorem prime_5810526060517 : Nat.Prime 5810526060517 := by
  apply nodeValid_prime [2, 3, 29, 673, 918877] ⟨5810526060517, 2, [(2, 2), (3, 4), (29, 1), (673, 1), (918877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_673
    · exact prime_918877
  · decide +kernel

theorem prime_5810526094573 : Nat.Prime 5810526094573 := by
  apply nodeValid_prime [2, 3, 161403502627] ⟨5810526094573, 2, [(2, 2), (3, 2), (161403502627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_161403502627
  · decide +kernel

theorem prime_5814819032921 : Nat.Prime 5814819032921 := by
  apply nodeValid_prime [2, 5, 37, 3928931779] ⟨5814819032921, 3, [(2, 3), (5, 1), (37, 1), (3928931779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_3928931779
  · decide +kernel

theorem prime_5814819033839 : Nat.Prime 5814819033839 := by
  apply nodeValid_prime [2, 3137, 926812087] ⟨5814819033839, 7, [(2, 1), (3137, 1), (926812087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3137
    · exact prime_926812087
  · decide +kernel

theorem prime_5814819034247 : Nat.Prime 5814819034247 := by
  apply nodeValid_prime [2, 2907409517123] ⟨5814819034247, 5, [(2, 1), (2907409517123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2907409517123
  · decide +kernel

theorem prime_5819114114101 : Nat.Prime 5819114114101 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 1283, 5413] ⟨5819114114101, 18, [(2, 2), (3, 2), (5, 2), (7, 2), (19, 1), (1283, 1), (5413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_1283
    · exact prime_5413
  · decide +kernel

theorem prime_5819114117903 : Nat.Prime 5819114117903 := by
  apply nodeValid_prime [2, 31, 2131, 44043491] ⟨5819114117903, 5, [(2, 1), (31, 1), (2131, 1), (44043491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2131
    · exact prime_44043491
  · decide +kernel

theorem prime_5823411336047 : Nat.Prime 5823411336047 := by
  apply nodeValid_prime [2, 83, 257, 2801, 48733] ⟨5823411336047, 5, [(2, 1), (83, 1), (257, 1), (2801, 1), (48733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_257
    · exact prime_2801
    · exact prime_48733
  · decide +kernel

theorem prime_5823411432071 : Nat.Prime 5823411432071 := by
  apply nodeValid_prime [2, 5, 19, 5153, 5947901] ⟨5823411432071, 14, [(2, 1), (5, 1), (19, 1), (5153, 1), (5947901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_5153
    · exact prime_5947901
  · decide +kernel

theorem prime_5823411432221 : Nat.Prime 5823411432221 := by
  apply nodeValid_prime [2, 5, 17, 25169, 680507] ⟨5823411432221, 3, [(2, 2), (5, 1), (17, 1), (25169, 1), (680507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_25169
    · exact prime_680507
  · decide +kernel

theorem prime_5827710707461 : Nat.Prime 5827710707461 := by
  apply nodeValid_prime [2, 3, 5, 98453, 328849] ⟨5827710707461, 2, [(2, 2), (3, 2), (5, 1), (98453, 1), (328849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_98453
    · exact prime_328849
  · decide +kernel

theorem prime_5827710843491 : Nat.Prime 5827710843491 := by
  apply nodeValid_prime [2, 5, 883, 659989903] ⟨5827710843491, 10, [(2, 1), (5, 1), (883, 1), (659989903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_883
    · exact prime_659989903
  · decide +kernel

theorem prime_5827710843551 : Nat.Prime 5827710843551 := by
  apply nodeValid_prime [2, 5, 116554216871] ⟨5827710843551, 7, [(2, 1), (5, 2), (116554216871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_116554216871
  · decide +kernel

theorem prime_5832012127951 : Nat.Prime 5832012127951 := by
  apply nodeValid_prime [2, 3, 5, 941, 13772611] ⟨5832012127951, 3, [(2, 1), (3, 2), (5, 2), (941, 1), (13772611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_941
    · exact prime_13772611
  · decide +kernel

theorem prime_5832012128707 : Nat.Prime 5832012128707 := by
  apply nodeValid_prime [2, 3, 19, 17052667043] ⟨5832012128707, 2, [(2, 1), (3, 2), (19, 1), (17052667043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_17052667043
  · decide +kernel

theorem prime_5832012222863 : Nat.Prime 5832012222863 := by
  apply nodeValid_prime [2, 7, 416572301633] ⟨5832012222863, 7, [(2, 1), (7, 1), (416572301633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_416572301633
  · decide +kernel

theorem prime_5836315893007 : Nat.Prime 5836315893007 := by
  apply nodeValid_prime [2, 3, 972719315501] ⟨5836315893007, 3, [(2, 1), (3, 1), (972719315501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_972719315501
  · decide +kernel

theorem prime_5836315952659 : Nat.Prime 5836315952659 := by
  apply nodeValid_prime [2, 3, 257, 3784900099] ⟨5836315952659, 2, [(2, 1), (3, 1), (257, 1), (3784900099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_3784900099
  · decide +kernel

theorem prime_5836315953683 : Nat.Prime 5836315953683 := by
  apply nodeValid_prime [2, 19, 41, 3746030779] ⟨5836315953683, 2, [(2, 1), (19, 1), (41, 1), (3746030779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_3746030779
  · decide +kernel

theorem prime_5840621667817 : Nat.Prime 5840621667817 := by
  apply nodeValid_prime [2, 3, 13, 18719941243] ⟨5840621667817, 7, [(2, 3), (3, 1), (13, 1), (18719941243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_18719941243
  · decide +kernel

theorem prime_5840621669227 : Nat.Prime 5840621669227 := by
  apply nodeValid_prime [2, 3, 59, 997, 16548577] ⟨5840621669227, 3, [(2, 1), (3, 1), (59, 1), (997, 1), (16548577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_997
    · exact prime_16548577
  · decide +kernel

theorem prime_5840621716807 : Nat.Prime 5840621716807 := by
  apply nodeValid_prime [2, 3, 283, 1146568849] ⟨5840621716807, 3, [(2, 1), (3, 2), (283, 1), (1146568849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1146568849
  · decide +kernel

theorem prime_5844929602549 : Nat.Prime 5844929602549 := by
  apply nodeValid_prime [2, 3, 823, 591831673] ⟨5844929602549, 2, [(2, 2), (3, 1), (823, 1), (591831673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_823
    · exact prime_591831673
  · decide +kernel

theorem prime_5844929602867 : Nat.Prime 5844929602867 := by
  apply nodeValid_prime [2, 3, 974154933811] ⟨5844929602867, 2, [(2, 1), (3, 1), (974154933811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_974154933811
  · decide +kernel

theorem prime_5844929683981 : Nat.Prime 5844929683981 := by
  apply nodeValid_prime [2, 3, 5, 37, 2632851209] ⟨5844929683981, 7, [(2, 2), (3, 1), (5, 1), (37, 1), (2632851209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_2632851209
  · decide +kernel

theorem prime_5849239800641 : Nat.Prime 5849239800641 := by
  apply nodeValid_prime [2, 5, 29, 2137, 294949] ⟨5849239800641, 6, [(2, 6), (5, 1), (29, 1), (2137, 1), (294949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_2137
    · exact prime_294949
  · decide +kernel

theorem prime_5849239895579 : Nat.Prime 5849239895579 := by
  apply nodeValid_prime [2, 17, 197, 2333, 374317] ⟨5849239895579, 2, [(2, 1), (17, 1), (197, 1), (2333, 1), (374317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_197
    · exact prime_2333
    · exact prime_374317
  · decide +kernel

theorem prime_5849239895677 : Nat.Prime 5849239895677 := by
  apply nodeValid_prime [2, 3, 37, 157, 1301, 21499] ⟨5849239895677, 5, [(2, 2), (3, 2), (37, 1), (157, 1), (1301, 1), (21499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_157
    · exact prime_1301
    · exact prime_21499
  · decide +kernel

theorem prime_5853552077803 : Nat.Prime 5853552077803 := by
  apply nodeValid_prime [2, 3, 11, 13, 71, 96089039] ⟨5853552077803, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (71, 1), (96089039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_71
    · exact prime_96089039
  · decide +kernel

theorem prime_5853552119347 : Nat.Prime 5853552119347 := by
  apply nodeValid_prime [2, 3, 11927, 81796933] ⟨5853552119347, 3, [(2, 1), (3, 1), (11927, 1), (81796933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11927
    · exact prime_81796933
  · decide +kernel

theorem prime_5853552120517 : Nat.Prime 5853552120517 := by
  apply nodeValid_prime [2, 3, 487796010043] ⟨5853552120517, 5, [(2, 2), (3, 1), (487796010043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487796010043
  · decide +kernel

theorem prime_5857866390461 : Nat.Prime 5857866390461 := by
  apply nodeValid_prime [2, 5, 7, 41841902789] ⟨5857866390461, 3, [(2, 2), (5, 1), (7, 1), (41841902789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41841902789
  · decide +kernel

theorem prime_5857866391373 : Nat.Prime 5857866391373 := by
  apply nodeValid_prime [2, 311, 4639, 1015067] ⟨5857866391373, 2, [(2, 2), (311, 1), (4639, 1), (1015067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_4639
    · exact prime_1015067
  · decide +kernel

theorem prime_5857866501821 : Nat.Prime 5857866501821 := by
  apply nodeValid_prime [2, 5, 17, 17229019123] ⟨5857866501821, 2, [(2, 2), (5, 1), (17, 1), (17229019123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_17229019123
  · decide +kernel

theorem prime_5862183064813 : Nat.Prime 5862183064813 := by
  apply nodeValid_prime [2, 3, 162838418467] ⟨5862183064813, 2, [(2, 2), (3, 2), (162838418467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_162838418467
  · decide +kernel

theorem prime_5862183064879 : Nat.Prime 5862183064879 := by
  apply nodeValid_prime [2, 3, 7, 17, 3617, 2269931] ⟨5862183064879, 6, [(2, 1), (3, 1), (7, 1), (17, 1), (3617, 1), (2269931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_3617
    · exact prime_2269931
  · decide +kernel

theorem prime_5862183077273 : Nat.Prime 5862183077273 := by
  apply nodeValid_prime [2, 31, 59, 400641271] ⟨5862183077273, 3, [(2, 3), (31, 1), (59, 1), (400641271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_59
    · exact prime_400641271
  · decide +kernel

theorem prime_5866501770253 : Nat.Prime 5866501770253 := by
  apply nodeValid_prime [2, 3, 929, 6353, 27611] ⟨5866501770253, 7, [(2, 2), (3, 2), (929, 1), (6353, 1), (27611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
    · exact prime_6353
    · exact prime_27611
  · decide +kernel

theorem prime_5866501771391 : Nat.Prime 5866501771391 := by
  apply nodeValid_prime [2, 5, 13, 149, 302865347] ⟨5866501771391, 7, [(2, 1), (5, 1), (13, 1), (149, 1), (302865347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_149
    · exact prime_302865347
  · decide +kernel

theorem prime_5866501818713 : Nat.Prime 5866501818713 := by
  apply nodeValid_prime [2, 31, 23655249269] ⟨5866501818713, 3, [(2, 3), (31, 1), (23655249269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_23655249269
  · decide +kernel

theorem prime_5870822686447 : Nat.Prime 5870822686447 := by
  apply nodeValid_prime [2, 3, 978470447741] ⟨5870822686447, 5, [(2, 1), (3, 1), (978470447741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_978470447741
  · decide +kernel

theorem prime_5870822686543 : Nat.Prime 5870822686543 := by
  apply nodeValid_prime [2, 3, 11, 22031, 1345859] ⟨5870822686543, 3, [(2, 1), (3, 2), (11, 1), (22031, 1), (1345859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_22031
    · exact prime_1345859
  · decide +kernel

theorem prime_5870822716097 : Nat.Prime 5870822716097 := by
  apply nodeValid_prime [2, 13, 29, 243319907] ⟨5870822716097, 5, [(2, 6), (13, 1), (29, 1), (243319907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_243319907
  · decide +kernel

theorem prime_5875145740333 : Nat.Prime 5875145740333 := by
  apply nodeValid_prime [2, 3, 11, 14321, 1035977] ⟨5875145740333, 5, [(2, 2), (3, 2), (11, 1), (14321, 1), (1035977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_14321
    · exact prime_1035977
  · decide +kernel

theorem prime_5875145741989 : Nat.Prime 5875145741989 := by
  apply nodeValid_prime [2, 3, 97, 2273, 246731] ⟨5875145741989, 2, [(2, 2), (3, 3), (97, 1), (2273, 1), (246731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_2273
    · exact prime_246731
  · decide +kernel

theorem prime_5875145764967 : Nat.Prime 5875145764967 := by
  apply nodeValid_prime [2, 353, 8321736211] ⟨5875145764967, 5, [(2, 1), (353, 1), (8321736211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_8321736211
  · decide +kernel

theorem prime_5879470967663 : Nat.Prime 5879470967663 := by
  apply nodeValid_prime [2, 2939735483831] ⟨5879470967663, 5, [(2, 1), (2939735483831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2939735483831
  · decide +kernel

theorem prime_5879470983773 : Nat.Prime 5879470983773 := by
  apply nodeValid_prime [2, 1469867745943] ⟨5879470983773, 2, [(2, 2), (1469867745943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1469867745943
  · decide +kernel

theorem prime_5879470983791 : Nat.Prime 5879470983791 := by
  apply nodeValid_prime [2, 5, 443, 757, 1753229] ⟨5879470983791, 11, [(2, 1), (5, 1), (443, 1), (757, 1), (1753229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_443
    · exact prime_757
    · exact prime_1753229
  · decide +kernel

end Sude.Lucas.Generated
