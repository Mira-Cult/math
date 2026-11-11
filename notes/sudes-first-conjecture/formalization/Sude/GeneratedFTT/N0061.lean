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
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6637 : Nat.Prime 6637 := by
  apply nodeValid_prime [2, 3, 7, 79] ⟨6637, 2, [(2, 2), (3, 1), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_6709 : Nat.Prime 6709 := by
  apply nodeValid_prime [2, 3, 13, 43] ⟨6709, 2, [(2, 2), (3, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_8689 : Nat.Prime 8689 := by
  apply nodeValid_prime [2, 3, 181] ⟨8689, 13, [(2, 4), (3, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel

theorem prime_10651 : Nat.Prime 10651 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨10651, 7, [(2, 1), (3, 1), (5, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_10973 : Nat.Prime 10973 := by
  apply nodeValid_prime [2, 13, 211] ⟨10973, 2, [(2, 2), (13, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_211
  · decide +kernel

theorem prime_11113 : Nat.Prime 11113 := by
  apply nodeValid_prime [2, 3, 463] ⟨11113, 13, [(2, 3), (3, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
  · decide +kernel

theorem prime_11617 : Nat.Prime 11617 := by
  apply nodeValid_prime [2, 3, 11] ⟨11617, 10, [(2, 5), (3, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_12437 : Nat.Prime 12437 := by
  apply nodeValid_prime [2, 3109] ⟨12437, 2, [(2, 2), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3109
  · decide +kernel

theorem prime_12637 : Nat.Prime 12637 := by
  apply nodeValid_prime [2, 3, 13] ⟨12637, 2, [(2, 2), (3, 5), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_13007 : Nat.Prime 13007 := by
  apply nodeValid_prime [2, 7, 929] ⟨13007, 5, [(2, 1), (7, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_929
  · decide +kernel

theorem prime_15149 : Nat.Prime 15149 := by
  apply nodeValid_prime [2, 7, 541] ⟨15149, 2, [(2, 2), (7, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_541
  · decide +kernel

theorem prime_16223 : Nat.Prime 16223 := by
  apply nodeValid_prime [2, 8111] ⟨16223, 5, [(2, 1), (8111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8111
  · decide +kernel

theorem prime_17851 : Nat.Prime 17851 := by
  apply nodeValid_prime [2, 3, 5, 7, 17] ⟨17851, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_21617 : Nat.Prime 21617 := by
  apply nodeValid_prime [2, 7, 193] ⟨21617, 3, [(2, 4), (7, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_193
  · decide +kernel

theorem prime_26347 : Nat.Prime 26347 := by
  apply nodeValid_prime [2, 3, 4391] ⟨26347, 3, [(2, 1), (3, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4391
  · decide +kernel

theorem prime_31033 : Nat.Prime 31033 := by
  apply nodeValid_prime [2, 3, 431] ⟨31033, 10, [(2, 3), (3, 2), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
  · decide +kernel

theorem prime_33577 : Nat.Prime 33577 := by
  apply nodeValid_prime [2, 3, 1399] ⟨33577, 5, [(2, 3), (3, 1), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1399
  · decide +kernel

theorem prime_48473 : Nat.Prime 48473 := by
  apply nodeValid_prime [2, 73, 83] ⟨48473, 3, [(2, 3), (73, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_83
  · decide +kernel

theorem prime_49433 : Nat.Prime 49433 := by
  apply nodeValid_prime [2, 37, 167] ⟨49433, 3, [(2, 3), (37, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_167
  · decide +kernel

theorem prime_49663 : Nat.Prime 49663 := by
  apply nodeValid_prime [2, 3, 31, 89] ⟨49663, 3, [(2, 1), (3, 2), (31, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_89
  · decide +kernel

theorem prime_53923 : Nat.Prime 53923 := by
  apply nodeValid_prime [2, 3, 11, 19, 43] ⟨53923, 5, [(2, 1), (3, 1), (11, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_77081 : Nat.Prime 77081 := by
  apply nodeValid_prime [2, 5, 41, 47] ⟨77081, 3, [(2, 3), (5, 1), (41, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_47
  · decide +kernel

theorem prime_78541 : Nat.Prime 78541 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 17] ⟨78541, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_82549 : Nat.Prime 82549 := by
  apply nodeValid_prime [2, 3, 2293] ⟨82549, 2, [(2, 2), (3, 2), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2293
  · decide +kernel

theorem prime_83579 : Nat.Prime 83579 := by
  apply nodeValid_prime [2, 11, 29, 131] ⟨83579, 2, [(2, 1), (11, 1), (29, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_131
  · decide +kernel

theorem prime_85297 : Nat.Prime 85297 := by
  apply nodeValid_prime [2, 3, 1777] ⟨85297, 15, [(2, 4), (3, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1777
  · decide +kernel

theorem prime_86927 : Nat.Prime 86927 := by
  apply nodeValid_prime [2, 7, 887] ⟨86927, 5, [(2, 1), (7, 2), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_887
  · decide +kernel

theorem prime_98867 : Nat.Prime 98867 := by
  apply nodeValid_prime [2, 49433] ⟨98867, 2, [(2, 1), (49433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49433
  · decide +kernel

theorem prime_100801 : Nat.Prime 100801 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨100801, 11, [(2, 6), (3, 2), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_102107 : Nat.Prime 102107 := by
  apply nodeValid_prime [2, 19, 2687] ⟨102107, 2, [(2, 1), (19, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2687
  · decide +kernel

theorem prime_105389 : Nat.Prime 105389 := by
  apply nodeValid_prime [2, 26347] ⟨105389, 2, [(2, 2), (26347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26347
  · decide +kernel

theorem prime_133583 : Nat.Prime 133583 := by
  apply nodeValid_prime [2, 66791] ⟨133583, 5, [(2, 1), (66791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_66791
  · decide +kernel

theorem prime_142151 : Nat.Prime 142151 := by
  apply nodeValid_prime [2, 5, 2843] ⟨142151, 11, [(2, 1), (5, 2), (2843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2843
  · decide +kernel

theorem prime_144701 : Nat.Prime 144701 := by
  apply nodeValid_prime [2, 5, 1447] ⟨144701, 2, [(2, 2), (5, 2), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1447
  · decide +kernel

theorem prime_149711 : Nat.Prime 149711 := by
  apply nodeValid_prime [2, 5, 11, 1361] ⟨149711, 7, [(2, 1), (5, 1), (11, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1361
  · decide +kernel

theorem prime_157051 : Nat.Prime 157051 := by
  apply nodeValid_prime [2, 3, 5, 349] ⟨157051, 2, [(2, 1), (3, 2), (5, 2), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_176201 : Nat.Prime 176201 := by
  apply nodeValid_prime [2, 5, 881] ⟨176201, 6, [(2, 3), (5, 2), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_881
  · decide +kernel

theorem prime_178931 : Nat.Prime 178931 := by
  apply nodeValid_prime [2, 5, 29, 617] ⟨178931, 2, [(2, 1), (5, 1), (29, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_617
  · decide +kernel

theorem prime_194827 : Nat.Prime 194827 := by
  apply nodeValid_prime [2, 3, 19, 1709] ⟨194827, 2, [(2, 1), (3, 1), (19, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1709
  · decide +kernel

theorem prime_197711 : Nat.Prime 197711 := by
  apply nodeValid_prime [2, 5, 17, 1163] ⟨197711, 13, [(2, 1), (5, 1), (17, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1163
  · decide +kernel

theorem prime_206597 : Nat.Prime 206597 := by
  apply nodeValid_prime [2, 13, 29, 137] ⟨206597, 2, [(2, 2), (13, 1), (29, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_137
  · decide +kernel

theorem prime_219937 : Nat.Prime 219937 := by
  apply nodeValid_prime [2, 3, 29, 79] ⟨219937, 5, [(2, 5), (3, 1), (29, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_79
  · decide +kernel

theorem prime_228353 : Nat.Prime 228353 := by
  apply nodeValid_prime [2, 223] ⟨228353, 3, [(2, 10), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_223
  · decide +kernel

theorem prime_253751 : Nat.Prime 253751 := by
  apply nodeValid_prime [2, 5, 7, 29] ⟨253751, 7, [(2, 1), (5, 4), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_267167 : Nat.Prime 267167 := by
  apply nodeValid_prime [2, 133583] ⟨267167, 5, [(2, 1), (133583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_133583
  · decide +kernel

theorem prime_269441 : Nat.Prime 269441 := by
  apply nodeValid_prime [2, 5, 421] ⟨269441, 3, [(2, 7), (5, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_421
  · decide +kernel

theorem prime_284633 : Nat.Prime 284633 := by
  apply nodeValid_prime [2, 47, 757] ⟨284633, 3, [(2, 3), (47, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_757
  · decide +kernel

theorem prime_295541 : Nat.Prime 295541 := by
  apply nodeValid_prime [2, 5, 7, 2111] ⟨295541, 2, [(2, 2), (5, 1), (7, 1), (2111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2111
  · decide +kernel

theorem prime_312353 : Nat.Prime 312353 := by
  apply nodeValid_prime [2, 43, 227] ⟨312353, 3, [(2, 5), (43, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_227
  · decide +kernel

theorem prime_373063 : Nat.Prime 373063 := by
  apply nodeValid_prime [2, 3, 97, 641] ⟨373063, 5, [(2, 1), (3, 1), (97, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_641
  · decide +kernel

theorem prime_435889 : Nat.Prime 435889 := by
  apply nodeValid_prime [2, 3, 1009] ⟨435889, 19, [(2, 4), (3, 3), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1009
  · decide +kernel

theorem prime_538151 : Nat.Prime 538151 := by
  apply nodeValid_prime [2, 5, 47, 229] ⟨538151, 11, [(2, 1), (5, 2), (47, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_229
  · decide +kernel

theorem prime_556931 : Nat.Prime 556931 := by
  apply nodeValid_prime [2, 5, 11, 61, 83] ⟨556931, 2, [(2, 1), (5, 1), (11, 1), (61, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_61
    · exact prime_83
  · decide +kernel

theorem prime_567181 : Nat.Prime 567181 := by
  apply nodeValid_prime [2, 3, 5, 23, 137] ⟨567181, 10, [(2, 2), (3, 2), (5, 1), (23, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_137
  · decide +kernel

theorem prime_640457 : Nat.Prime 640457 := by
  apply nodeValid_prime [2, 223, 359] ⟨640457, 3, [(2, 3), (223, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_359
  · decide +kernel

theorem prime_778213 : Nat.Prime 778213 := by
  apply nodeValid_prime [2, 3, 21617] ⟨778213, 2, [(2, 2), (3, 2), (21617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21617
  · decide +kernel

theorem prime_781129 : Nat.Prime 781129 := by
  apply nodeValid_prime [2, 3, 19, 571] ⟨781129, 7, [(2, 3), (3, 2), (19, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_571
  · decide +kernel

theorem prime_1000931 : Nat.Prime 1000931 := by
  apply nodeValid_prime [2, 5, 7, 79, 181] ⟨1000931, 2, [(2, 1), (5, 1), (7, 1), (79, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
    · exact prime_181
  · decide +kernel

theorem prime_1113863 : Nat.Prime 1113863 := by
  apply nodeValid_prime [2, 556931] ⟨1113863, 5, [(2, 1), (556931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_556931
  · decide +kernel

theorem prime_1152707 : Nat.Prime 1152707 := by
  apply nodeValid_prime [2, 227, 2539] ⟨1152707, 2, [(2, 1), (227, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_2539
  · decide +kernel

theorem prime_1170107 : Nat.Prime 1170107 := by
  apply nodeValid_prime [2, 7, 83579] ⟨1170107, 2, [(2, 1), (7, 1), (83579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83579
  · decide +kernel

theorem prime_1316671 : Nat.Prime 1316671 := by
  apply nodeValid_prime [2, 3, 5, 43889] ⟨1316671, 6, [(2, 1), (3, 1), (5, 1), (43889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43889
  · decide +kernel

theorem prime_1550597 : Nat.Prime 1550597 := by
  apply nodeValid_prime [2, 37, 10477] ⟨1550597, 2, [(2, 2), (37, 1), (10477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_10477
  · decide +kernel

theorem prime_1650911 : Nat.Prime 1650911 := by
  apply nodeValid_prime [2, 5, 19, 8689] ⟨1650911, 11, [(2, 1), (5, 1), (19, 1), (8689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_8689
  · decide +kernel

theorem prime_1672961 : Nat.Prime 1672961 := by
  apply nodeValid_prime [2, 5, 1307] ⟨1672961, 3, [(2, 8), (5, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1307
  · decide +kernel

theorem prime_1743557 : Nat.Prime 1743557 := by
  apply nodeValid_prime [2, 435889] ⟨1743557, 2, [(2, 2), (435889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_435889
  · decide +kernel

theorem prime_2345131 : Nat.Prime 2345131 := by
  apply nodeValid_prime [2, 3, 5, 71, 367] ⟨2345131, 2, [(2, 1), (3, 2), (5, 1), (71, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_367
  · decide +kernel

theorem prime_2843021 : Nat.Prime 2843021 := by
  apply nodeValid_prime [2, 5, 142151] ⟨2843021, 2, [(2, 2), (5, 1), (142151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_142151
  · decide +kernel

theorem prime_3394301 : Nat.Prime 3394301 := by
  apply nodeValid_prime [2, 5, 7, 13, 373] ⟨3394301, 3, [(2, 2), (5, 2), (7, 1), (13, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_373
  · decide +kernel

theorem prime_3434287 : Nat.Prime 3434287 := by
  apply nodeValid_prime [2, 3, 67, 8543] ⟨3434287, 3, [(2, 1), (3, 1), (67, 1), (8543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_8543
  · decide +kernel

theorem prime_3687407 : Nat.Prime 3687407 := by
  apply nodeValid_prime [2, 19, 23, 4219] ⟨3687407, 5, [(2, 1), (19, 1), (23, 1), (4219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_4219
  · decide +kernel

theorem prime_3740339 : Nat.Prime 3740339 := by
  apply nodeValid_prime [2, 7, 267167] ⟨3740339, 2, [(2, 1), (7, 1), (267167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_267167
  · decide +kernel

theorem prime_3955243 : Nat.Prime 3955243 := by
  apply nodeValid_prime [2, 3, 59, 11173] ⟨3955243, 2, [(2, 1), (3, 1), (59, 1), (11173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_11173
  · decide +kernel

theorem prime_3967141 : Nat.Prime 3967141 := by
  apply nodeValid_prime [2, 3, 5, 37, 1787] ⟨3967141, 2, [(2, 2), (3, 1), (5, 1), (37, 1), (1787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_1787
  · decide +kernel

theorem prime_4068683 : Nat.Prime 4068683 := by
  apply nodeValid_prime [2, 191, 10651] ⟨4068683, 2, [(2, 1), (191, 1), (10651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_10651
  · decide +kernel

theorem prime_4469671 : Nat.Prime 4469671 := by
  apply nodeValid_prime [2, 3, 5, 49663] ⟨4469671, 3, [(2, 1), (3, 2), (5, 1), (49663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_49663
  · decide +kernel

theorem prime_5579153 : Nat.Prime 5579153 := by
  apply nodeValid_prime [2, 157, 2221] ⟨5579153, 3, [(2, 4), (157, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_2221
  · decide +kernel

theorem prime_5671811 : Nat.Prime 5671811 := by
  apply nodeValid_prime [2, 5, 567181] ⟨5671811, 2, [(2, 1), (5, 1), (567181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_567181
  · decide +kernel

theorem prime_6055169 : Nat.Prime 6055169 := by
  apply nodeValid_prime [2, 7, 31, 109] ⟨6055169, 3, [(2, 8), (7, 1), (31, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_109
  · decide +kernel

theorem prime_6516539 : Nat.Prime 6516539 := by
  apply nodeValid_prime [2, 7, 191, 2437] ⟨6516539, 2, [(2, 1), (7, 1), (191, 1), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_191
    · exact prime_2437
  · decide +kernel

theorem prime_13865653 : Nat.Prime 13865653 := by
  apply nodeValid_prime [2, 3, 599, 643] ⟨13865653, 6, [(2, 2), (3, 2), (599, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_599
    · exact prime_643
  · decide +kernel

theorem prime_18733361 : Nat.Prime 18733361 := by
  apply nodeValid_prime [2, 5, 234167] ⟨18733361, 3, [(2, 4), (5, 1), (234167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_234167
  · decide +kernel

theorem prime_19244749 : Nat.Prime 19244749 := by
  apply nodeValid_prime [2, 3, 17, 29, 3253] ⟨19244749, 18, [(2, 2), (3, 1), (17, 1), (29, 1), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_3253
  · decide +kernel

theorem prime_19646663 : Nat.Prime 19646663 := by
  apply nodeValid_prime [2, 7, 17, 82549] ⟨19646663, 5, [(2, 1), (7, 1), (17, 1), (82549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_82549
  · decide +kernel

theorem prime_19822669 : Nat.Prime 19822669 := by
  apply nodeValid_prime [2, 3, 127, 13007] ⟨19822669, 6, [(2, 2), (3, 1), (127, 1), (13007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_13007
  · decide +kernel

theorem prime_21142393 : Nat.Prime 21142393 := by
  apply nodeValid_prime [2, 3, 29, 37, 821] ⟨21142393, 5, [(2, 3), (3, 1), (29, 1), (37, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_37
    · exact prime_821
  · decide +kernel

theorem prime_23967763 : Nat.Prime 23967763 := by
  apply nodeValid_prime [2, 3, 7, 13, 6271] ⟨23967763, 2, [(2, 1), (3, 1), (7, 2), (13, 1), (6271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_6271
  · decide +kernel

theorem prime_24720977 : Nat.Prime 24720977 := by
  apply nodeValid_prime [2, 7, 19, 11617] ⟨24720977, 3, [(2, 4), (7, 1), (19, 1), (11617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_11617
  · decide +kernel

theorem prime_31017991 : Nat.Prime 31017991 := by
  apply nodeValid_prime [2, 3, 5, 641, 1613] ⟨31017991, 6, [(2, 1), (3, 1), (5, 1), (641, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_641
    · exact prime_1613
  · decide +kernel

theorem prime_32280713 : Nat.Prime 32280713 := by
  apply nodeValid_prime [2, 29, 61, 2281] ⟨32280713, 3, [(2, 3), (29, 1), (61, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_61
    · exact prime_2281
  · decide +kernel

theorem prime_39293327 : Nat.Prime 39293327 := by
  apply nodeValid_prime [2, 19646663] ⟨39293327, 5, [(2, 1), (19646663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19646663
  · decide +kernel

theorem prime_43116769 : Nat.Prime 43116769 := by
  apply nodeValid_prime [2, 3, 149711] ⟨43116769, 7, [(2, 5), (3, 2), (149711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149711
  · decide +kernel

theorem prime_44068747 : Nat.Prime 44068747 := by
  apply nodeValid_prime [2, 3, 127, 151, 383] ⟨44068747, 2, [(2, 1), (3, 1), (127, 1), (151, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_151
    · exact prime_383
  · decide +kernel

theorem prime_51151073 : Nat.Prime 51151073 := by
  apply nodeValid_prime [2, 7, 228353] ⟨51151073, 3, [(2, 5), (7, 1), (228353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_228353
  · decide +kernel

theorem prime_62246179 : Nat.Prime 62246179 := by
  apply nodeValid_prime [2, 3, 1152707] ⟨62246179, 3, [(2, 1), (3, 3), (1152707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1152707
  · decide +kernel

theorem prime_62768053 : Nat.Prime 62768053 := by
  apply nodeValid_prime [2, 3, 1743557] ⟨62768053, 6, [(2, 2), (3, 2), (1743557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1743557
  · decide +kernel

theorem prime_66699187 : Nat.Prime 66699187 := by
  apply nodeValid_prime [2, 3, 1069, 10399] ⟨66699187, 2, [(2, 1), (3, 1), (1069, 1), (10399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
    · exact prime_10399
  · decide +kernel

theorem prime_70353931 : Nat.Prime 70353931 := by
  apply nodeValid_prime [2, 3, 5, 2345131] ⟨70353931, 2, [(2, 1), (3, 1), (5, 1), (2345131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2345131
  · decide +kernel

theorem prime_76952231 : Nat.Prime 76952231 := by
  apply nodeValid_prime [2, 5, 31, 37, 6709] ⟨76952231, 13, [(2, 1), (5, 1), (31, 1), (37, 1), (6709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_37
    · exact prime_6709
  · decide +kernel

theorem prime_96068551 : Nat.Prime 96068551 := by
  apply nodeValid_prime [2, 3, 5, 640457] ⟨96068551, 3, [(2, 1), (3, 1), (5, 2), (640457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_640457
  · decide +kernel

theorem prime_124980641 : Nat.Prime 124980641 := by
  apply nodeValid_prime [2, 5, 781129] ⟨124980641, 3, [(2, 5), (5, 1), (781129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_781129
  · decide +kernel

theorem prime_266796749 : Nat.Prime 266796749 := by
  apply nodeValid_prime [2, 66699187] ⟨266796749, 2, [(2, 2), (66699187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_66699187
  · decide +kernel

theorem prime_282256309 : Nat.Prime 282256309 := by
  apply nodeValid_prime [2, 3, 241, 32533] ⟨282256309, 6, [(2, 2), (3, 2), (241, 1), (32533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_32533
  · decide +kernel

theorem prime_533593499 : Nat.Prime 533593499 := by
  apply nodeValid_prime [2, 266796749] ⟨533593499, 2, [(2, 1), (266796749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_266796749
  · decide +kernel

theorem prime_637263923 : Nat.Prime 637263923 := by
  apply nodeValid_prime [2, 29, 109, 100801] ⟨637263923, 2, [(2, 1), (29, 1), (109, 1), (100801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_109
    · exact prime_100801
  · decide +kernel

theorem prime_641147777 : Nat.Prime 641147777 := by
  apply nodeValid_prime [2, 29, 83, 2081] ⟨641147777, 3, [(2, 7), (29, 1), (83, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_83
    · exact prime_2081
  · decide +kernel

theorem prime_838148699 : Nat.Prime 838148699 := by
  apply nodeValid_prime [2, 103, 4068683] ⟨838148699, 2, [(2, 1), (103, 1), (4068683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_4068683
  · decide +kernel

theorem prime_923747953 : Nat.Prime 923747953 := by
  apply nodeValid_prime [2, 3, 19244749] ⟨923747953, 10, [(2, 4), (3, 1), (19244749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19244749
  · decide +kernel

theorem prime_945152809 : Nat.Prime 945152809 := by
  apply nodeValid_prime [2, 3, 17, 277, 8363] ⟨945152809, 19, [(2, 3), (3, 1), (17, 1), (277, 1), (8363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_277
    · exact prime_8363
  · decide +kernel

theorem prime_1414296607 : Nat.Prime 1414296607 := by
  apply nodeValid_prime [2, 3, 17, 13865653] ⟨1414296607, 11, [(2, 1), (3, 1), (17, 1), (13865653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_13865653
  · decide +kernel

theorem prime_1777279169 : Nat.Prime 1777279169 := by
  apply nodeValid_prime [2, 7, 3967141] ⟨1777279169, 3, [(2, 6), (7, 1), (3967141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3967141
  · decide +kernel

theorem prime_2185399207 : Nat.Prime 2185399207 := by
  apply nodeValid_prime [2, 3, 109, 1113863] ⟨2185399207, 19, [(2, 1), (3, 2), (109, 1), (1113863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1113863
  · decide +kernel

theorem prime_4017155393 : Nat.Prime 4017155393 := by
  apply nodeValid_prime [2, 62768053] ⟨4017155393, 3, [(2, 6), (62768053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_62768053
  · decide +kernel

theorem prime_5488716547 : Nat.Prime 5488716547 := by
  apply nodeValid_prime [2, 3, 59, 157, 10973] ⟨5488716547, 2, [(2, 1), (3, 3), (59, 1), (157, 1), (10973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_157
    · exact prime_10973
  · decide +kernel

theorem prime_7944221393 : Nat.Prime 7944221393 := by
  apply nodeValid_prime [2, 5821, 85297] ⟨7944221393, 3, [(2, 4), (5821, 1), (85297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5821
    · exact prime_85297
  · decide +kernel

theorem prime_8477805421 : Nat.Prime 8477805421 := by
  apply nodeValid_prime [2, 3, 5, 7, 541, 12437] ⟨8477805421, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (541, 1), (12437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_541
    · exact prime_12437
  · decide +kernel

theorem prime_9986033543 : Nat.Prime 9986033543 := by
  apply nodeValid_prime [2, 1471, 3394301] ⟨9986033543, 5, [(2, 1), (1471, 1), (3394301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1471
    · exact prime_3394301
  · decide +kernel

theorem prime_12838919251 : Nat.Prime 12838919251 := by
  apply nodeValid_prime [2, 3, 5, 109, 157051] ⟨12838919251, 3, [(2, 1), (3, 1), (5, 3), (109, 1), (157051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_157051
  · decide +kernel

theorem prime_13161031813 : Nat.Prime 13161031813 := by
  apply nodeValid_prime [2, 3, 1237, 295541] ⟨13161031813, 2, [(2, 2), (3, 2), (1237, 1), (295541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1237
    · exact prime_295541
  · decide +kernel

theorem prime_15241840687 : Nat.Prime 15241840687 := by
  apply nodeValid_prime [2, 3, 282256309] ⟨15241840687, 21, [(2, 1), (3, 3), (282256309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_282256309
  · decide +kernel

theorem prime_18706779803 : Nat.Prime 18706779803 := by
  apply nodeValid_prime [2, 19, 41, 863, 13913] ⟨18706779803, 5, [(2, 1), (19, 1), (41, 1), (863, 1), (13913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_863
    · exact prime_13913
  · decide +kernel

theorem prime_26820758369 : Nat.Prime 26820758369 := by
  apply nodeValid_prime [2, 838148699] ⟨26820758369, 3, [(2, 5), (838148699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_838148699
  · decide +kernel

theorem prime_35930093809 : Nat.Prime 35930093809 := by
  apply nodeValid_prime [2, 3, 7, 29, 3687407] ⟨35930093809, 37, [(2, 4), (3, 1), (7, 1), (29, 1), (3687407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_3687407
  · decide +kernel

theorem prime_41731720741 : Nat.Prime 41731720741 := by
  apply nodeValid_prime [2, 3, 5, 31, 461, 16223] ⟨41731720741, 11, [(2, 2), (3, 2), (5, 1), (31, 1), (461, 1), (16223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_461
    · exact prime_16223
  · decide +kernel

theorem prime_45445074527 : Nat.Prime 45445074527 := by
  apply nodeValid_prime [2, 17, 31, 43116769] ⟨45445074527, 5, [(2, 1), (17, 1), (31, 1), (43116769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_43116769
  · decide +kernel

theorem prime_83050339997 : Nat.Prime 83050339997 := by
  apply nodeValid_prime [2, 13, 1213, 1316671] ⟨83050339997, 2, [(2, 2), (13, 1), (1213, 1), (1316671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1213
    · exact prime_1316671
  · decide +kernel

theorem prime_96411729433 : Nat.Prime 96411729433 := by
  apply nodeValid_prime [2, 3, 4017155393] ⟨96411729433, 5, [(2, 3), (3, 1), (4017155393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4017155393
  · decide +kernel

theorem prime_98342776811 : Nat.Prime 98342776811 := by
  apply nodeValid_prime [2, 5, 12637, 778213] ⟨98342776811, 2, [(2, 1), (5, 1), (12637, 1), (778213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12637
    · exact prime_778213
  · decide +kernel

theorem prime_143720375237 : Nat.Prime 143720375237 := by
  apply nodeValid_prime [2, 35930093809] ⟨143720375237, 2, [(2, 2), (35930093809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35930093809
  · decide +kernel

theorem prime_145157748299 : Nat.Prime 145157748299 := by
  apply nodeValid_prime [2, 61, 15149, 78541] ⟨145157748299, 2, [(2, 1), (61, 1), (15149, 1), (78541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_15149
    · exact prime_78541
  · decide +kernel

theorem prime_192344338553 : Nat.Prime 192344338553 := by
  apply nodeValid_prime [2, 17, 1414296607] ⟨192344338553, 3, [(2, 3), (17, 1), (1414296607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1414296607
  · decide +kernel

theorem prime_294299934319 : Nat.Prime 294299934319 := by
  apply nodeValid_prime [2, 3, 13, 193, 6516539] ⟨294299934319, 3, [(2, 1), (3, 2), (13, 1), (193, 1), (6516539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_193
    · exact prime_6516539
  · decide +kernel

theorem prime_579910174241 : Nat.Prime 579910174241 := by
  apply nodeValid_prime [2, 5, 29, 124980641] ⟨579910174241, 3, [(2, 5), (5, 1), (29, 1), (124980641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_124980641
  · decide +kernel

theorem prime_580630977779 : Nat.Prime 580630977779 := by
  apply nodeValid_prime [2, 277, 13597, 77081] ⟨580630977779, 2, [(2, 1), (277, 1), (13597, 1), (77081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_13597
    · exact prime_77081
  · decide +kernel

theorem prime_587872383083 : Nat.Prime 587872383083 := by
  apply nodeValid_prime [2, 37, 7944221393] ⟨587872383083, 2, [(2, 1), (37, 1), (7944221393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_7944221393
  · decide +kernel

theorem prime_590056684109 : Nat.Prime 590056684109 := by
  apply nodeValid_prime [2, 83, 1777279169] ⟨590056684109, 2, [(2, 2), (83, 1), (1777279169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_1777279169
  · decide +kernel

theorem prime_590785968743 : Nat.Prime 590785968743 := by
  apply nodeValid_prime [2, 67, 757, 86927] ⟨590785968743, 5, [(2, 1), (67, 2), (757, 1), (86927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_757
    · exact prime_86927
  · decide +kernel

theorem prime_1149763001897 : Nat.Prime 1149763001897 := by
  apply nodeValid_prime [2, 143720375237] ⟨1149763001897, 3, [(2, 3), (143720375237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_143720375237
  · decide +kernel

theorem prime_1149763008019 : Nat.Prime 1149763008019 := by
  apply nodeValid_prime [2, 3, 541, 3469, 102107] ⟨1149763008019, 3, [(2, 1), (3, 1), (541, 1), (3469, 1), (102107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
    · exact prime_3469
    · exact prime_102107
  · decide +kernel

theorem prime_1149763008547 : Nat.Prime 1149763008547 := by
  apply nodeValid_prime [2, 3, 107, 5579153] ⟨1149763008547, 2, [(2, 1), (3, 2), (107, 2), (5579153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_5579153
  · decide +kernel

theorem prime_1151196121363 : Nat.Prime 1151196121363 := by
  apply nodeValid_prime [2, 3, 7, 29, 945152809] ⟨1151196121363, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (945152809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_945152809
  · decide +kernel

theorem prime_1151196134953 : Nat.Prime 1151196134953 := by
  apply nodeValid_prime [2, 3, 31, 137, 233, 48473] ⟨1151196134953, 5, [(2, 3), (3, 1), (31, 1), (137, 1), (233, 1), (48473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_137
    · exact prime_233
    · exact prime_48473
  · decide +kernel

theorem prime_1151196135049 : Nat.Prime 1151196135049 := by
  apply nodeValid_prime [2, 3, 2819, 5671811] ⟨1151196135049, 19, [(2, 3), (3, 2), (2819, 1), (5671811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2819
    · exact prime_5671811
  · decide +kernel

theorem prime_1152630454219 : Nat.Prime 1152630454219 := by
  apply nodeValid_prime [2, 3, 4889, 39293327] ⟨1152630454219, 3, [(2, 1), (3, 1), (4889, 1), (39293327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4889
    · exact prime_39293327
  · decide +kernel

theorem prime_1152630474871 : Nat.Prime 1152630474871 := by
  apply nodeValid_prime [2, 3, 5, 7, 5488716547] ⟨1152630474871, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (5488716547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_5488716547
  · decide +kernel

theorem prime_1152630474899 : Nat.Prime 1152630474899 := by
  apply nodeValid_prime [2, 7, 857, 96068551] ⟨1152630474899, 2, [(2, 1), (7, 1), (857, 1), (96068551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_857
    · exact prime_96068551
  · decide +kernel

theorem prime_1154065998601 : Nat.Prime 1154065998601 := by
  apply nodeValid_prime [2, 3, 5, 641147777] ⟨1154065998601, 7, [(2, 3), (3, 2), (5, 2), (641147777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_641147777
  · decide +kernel

theorem prime_1154066031319 : Nat.Prime 1154066031319 := by
  apply nodeValid_prime [2, 3, 192344338553] ⟨1154066031319, 3, [(2, 1), (3, 1), (192344338553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_192344338553
  · decide +kernel

theorem prime_1154066032729 : Nat.Prime 1154066032729 := by
  apply nodeValid_prime [2, 3, 7, 19, 73, 1650911] ⟨1154066032729, 17, [(2, 3), (3, 2), (7, 1), (19, 1), (73, 1), (1650911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_73
    · exact prime_1650911
  · decide +kernel

theorem prime_1155502732591 : Nat.Prime 1155502732591 := by
  apply nodeValid_prime [2, 3, 5, 12838919251] ⟨1155502732591, 6, [(2, 1), (3, 2), (5, 1), (12838919251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12838919251
  · decide +kernel

theorem prime_1155502739071 : Nat.Prime 1155502739071 := by
  apply nodeValid_prime [2, 3, 5, 251, 51151073] ⟨1155502739071, 3, [(2, 1), (3, 2), (5, 1), (251, 1), (51151073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_251
    · exact prime_51151073
  · decide +kernel

theorem prime_1155502758973 : Nat.Prime 1155502758973 := by
  apply nodeValid_prime [2, 3, 178931, 538151] ⟨1155502758973, 2, [(2, 2), (3, 1), (178931, 1), (538151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_178931
    · exact prime_538151
  · decide +kernel

theorem prime_1156940737223 : Nat.Prime 1156940737223 := by
  apply nodeValid_prime [2, 373063, 1550597] ⟨1156940737223, 5, [(2, 1), (373063, 1), (1550597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373063
    · exact prime_1550597
  · decide +kernel

theorem prime_1156940753197 : Nat.Prime 1156940753197 := by
  apply nodeValid_prime [2, 3, 96411729433] ⟨1156940753197, 2, [(2, 2), (3, 1), (96411729433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_96411729433
  · decide +kernel

theorem prime_1156940753921 : Nat.Prime 1156940753921 := by
  apply nodeValid_prime [2, 5, 7, 32280713] ⟨1156940753921, 3, [(2, 10), (5, 1), (7, 1), (32280713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_32280713
  · decide +kernel

theorem prime_1158379890989 : Nat.Prime 1158379890989 := by
  apply nodeValid_prime [2, 29, 9986033543] ⟨1158379890989, 2, [(2, 2), (29, 1), (9986033543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_9986033543
  · decide +kernel

theorem prime_1158379892213 : Nat.Prime 1158379892213 := by
  apply nodeValid_prime [2, 19, 15241840687] ⟨1158379892213, 2, [(2, 2), (19, 1), (15241840687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_15241840687
  · decide +kernel

theorem prime_1158379933063 : Nat.Prime 1158379933063 := by
  apply nodeValid_prime [2, 3, 11, 19, 923747953] ⟨1158379933063, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (923747953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_923747953
  · decide +kernel

theorem prime_1159820339861 : Nat.Prime 1159820339861 := by
  apply nodeValid_prime [2, 5, 7, 13, 637263923] ⟨1159820339861, 2, [(2, 2), (5, 1), (7, 1), (13, 1), (637263923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_637263923
  · decide +kernel

theorem prime_1159820347787 : Nat.Prime 1159820347787 := by
  apply nodeValid_prime [2, 31, 18706779803] ⟨1159820347787, 2, [(2, 1), (31, 1), (18706779803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_18706779803
  · decide +kernel

theorem prime_1159820348483 : Nat.Prime 1159820348483 := by
  apply nodeValid_prime [2, 579910174241] ⟨1159820348483, 2, [(2, 1), (579910174241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_579910174241
  · decide +kernel

theorem prime_1161261955559 : Nat.Prime 1161261955559 := by
  apply nodeValid_prime [2, 580630977779] ⟨1161261955559, 17, [(2, 1), (580630977779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_580630977779
  · decide +kernel

theorem prime_1161261985087 : Nat.Prime 1161261985087 := by
  apply nodeValid_prime [2, 3, 7, 131, 70353931] ⟨1161261985087, 5, [(2, 1), (3, 2), (7, 1), (131, 1), (70353931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_131
    · exact prime_70353931
  · decide +kernel

theorem prime_1161261986393 : Nat.Prime 1161261986393 := by
  apply nodeValid_prime [2, 145157748299] ⟨1161261986393, 3, [(2, 3), (145157748299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_145157748299
  · decide +kernel

theorem prime_1162704759959 : Nat.Prime 1162704759959 := by
  apply nodeValid_prime [2, 7, 83050339997] ⟨1162704759959, 7, [(2, 1), (7, 1), (83050339997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83050339997
  · decide +kernel

theorem prime_1162704760643 : Nat.Prime 1162704760643 := by
  apply nodeValid_prime [2, 31, 887, 21142393] ⟨1162704760643, 2, [(2, 1), (31, 1), (887, 1), (21142393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_887
    · exact prime_21142393
  · decide +kernel

theorem prime_1162704783827 : Nat.Prime 1162704783827 := by
  apply nodeValid_prime [2, 31033, 18733361] ⟨1162704783827, 2, [(2, 1), (31033, 1), (18733361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31033
    · exact prime_18733361
  · decide +kernel

theorem prime_1164148814447 : Nat.Prime 1164148814447 := by
  apply nodeValid_prime [2, 19, 127, 241, 1000931] ⟨1164148814447, 5, [(2, 1), (19, 1), (127, 1), (241, 1), (1000931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_127
    · exact prime_241
    · exact prime_1000931
  · decide +kernel

theorem prime_1164148815157 : Nat.Prime 1164148815157 := by
  apply nodeValid_prime [2, 3, 17, 4877, 1170107] ⟨1164148815157, 2, [(2, 2), (3, 1), (17, 1), (4877, 1), (1170107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4877
    · exact prime_1170107
  · decide +kernel

theorem prime_1164148823569 : Nat.Prime 1164148823569 := by
  apply nodeValid_prime [2, 3, 293, 4637, 17851] ⟨1164148823569, 11, [(2, 4), (3, 1), (293, 1), (4637, 1), (17851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_4637
    · exact prime_17851
  · decide +kernel

theorem prime_1165594065551 : Nat.Prime 1165594065551 := by
  apply nodeValid_prime [2, 5, 23, 41, 24720977] ⟨1165594065551, 11, [(2, 1), (5, 2), (23, 1), (41, 1), (24720977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_41
    · exact prime_24720977
  · decide +kernel

theorem prime_1165594065799 : Nat.Prime 1165594065799 := by
  apply nodeValid_prime [2, 3, 6263, 31017991] ⟨1165594065799, 6, [(2, 1), (3, 1), (6263, 1), (31017991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6263
    · exact prime_31017991
  · decide +kernel

theorem prime_1165594078373 : Nat.Prime 1165594078373 := by
  apply nodeValid_prime [2, 113, 26083, 98867] ⟨1165594078373, 2, [(2, 2), (113, 1), (26083, 1), (98867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_26083
    · exact prime_98867
  · decide +kernel

theorem prime_1167040540949 : Nat.Prime 1167040540949 := by
  apply nodeValid_prime [2, 149, 11113, 176201] ⟨1167040540949, 2, [(2, 2), (149, 1), (11113, 1), (176201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_11113
    · exact prime_176201
  · decide +kernel

theorem prime_1167040580941 : Nat.Prime 1167040580941 := by
  apply nodeValid_prime [2, 3, 5, 13, 617, 269441] ⟨1167040580941, 10, [(2, 2), (3, 3), (5, 1), (13, 1), (617, 1), (269441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_617
    · exact prime_269441
  · decide +kernel

theorem prime_1167040582361 : Nat.Prime 1167040582361 := by
  apply nodeValid_prime [2, 5, 173, 853, 197711] ⟨1167040582361, 3, [(2, 3), (5, 1), (173, 1), (853, 1), (197711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_853
    · exact prime_197711
  · decide +kernel

theorem prime_1168488180737 : Nat.Prime 1168488180737 := by
  apply nodeValid_prime [2, 5857, 194827] ⟨1168488180737, 3, [(2, 10), (5857, 1), (194827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5857
    · exact prime_194827
  · decide +kernel

theorem prime_1168488180749 : Nat.Prime 1168488180749 := by
  apply nodeValid_prime [2, 7, 41731720741] ⟨1168488180749, 3, [(2, 2), (7, 1), (41731720741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41731720741
  · decide +kernel

theorem prime_1168488210847 : Nat.Prime 1168488210847 := by
  apply nodeValid_prime [2, 3, 11, 17, 233, 4469671] ⟨1168488210847, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (233, 1), (4469671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_233
    · exact prime_4469671
  · decide +kernel

theorem prime_1169937095357 : Nat.Prime 1169937095357 := by
  apply nodeValid_prime [2, 6637, 44068747] ⟨1169937095357, 2, [(2, 2), (6637, 1), (44068747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6637
    · exact prime_44068747
  · decide +kernel

theorem prime_1169937147943 : Nat.Prime 1169937147943 := by
  apply nodeValid_prime [2, 3, 16433, 3955243] ⟨1169937147943, 5, [(2, 1), (3, 2), (16433, 1), (3955243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16433
    · exact prime_3955243
  · decide +kernel

theorem prime_1169937148099 : Nat.Prime 1169937148099 := by
  apply nodeValid_prime [2, 3, 23, 8477805421] ⟨1169937148099, 3, [(2, 1), (3, 1), (23, 1), (8477805421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_8477805421
  · decide +kernel

theorem prime_1171387198463 : Nat.Prime 1171387198463 := by
  apply nodeValid_prime [2, 13, 23, 53, 2843021] ⟨1171387198463, 5, [(2, 1), (13, 2), (23, 1), (53, 1), (2843021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_53
    · exact prime_2843021
  · decide +kernel

theorem prime_1171387215683 : Nat.Prime 1171387215683 := by
  apply nodeValid_prime [2, 199, 857, 3434287] ⟨1171387215683, 2, [(2, 1), (199, 1), (857, 1), (3434287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_857
    · exact prime_3434287
  · decide +kernel

theorem prime_1171387216669 : Nat.Prime 1171387216669 := by
  apply nodeValid_prime [2, 3, 19, 37, 83, 1672961] ⟨1171387216669, 2, [(2, 2), (3, 1), (19, 1), (37, 1), (83, 1), (1672961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_83
    · exact prime_1672961
  · decide +kernel

theorem prime_1172838510803 : Nat.Prime 1172838510803 := by
  apply nodeValid_prime [2, 7, 157, 533593499] ⟨1172838510803, 5, [(2, 1), (7, 1), (157, 1), (533593499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_157
    · exact prime_533593499
  · decide +kernel

theorem prime_1172838514643 : Nat.Prime 1172838514643 := by
  apply nodeValid_prime [2, 43, 569, 23967763] ⟨1172838514643, 2, [(2, 1), (43, 1), (569, 1), (23967763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_569
    · exact prime_23967763
  · decide +kernel

theorem prime_1172838515059 : Nat.Prime 1172838515059 := by
  apply nodeValid_prime [2, 3, 7, 53, 3257, 53923] ⟨1172838515059, 2, [(2, 1), (3, 2), (7, 1), (53, 1), (3257, 1), (53923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_3257
    · exact prime_53923
  · decide +kernel

theorem prime_1174291034509 : Nat.Prime 1174291034509 := by
  apply nodeValid_prime [2, 3, 5387, 6055169] ⟨1174291034509, 10, [(2, 2), (3, 2), (5387, 1), (6055169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5387
    · exact prime_6055169
  · decide +kernel

theorem prime_1174291045061 : Nat.Prime 1174291045061 := by
  apply nodeValid_prime [2, 5, 7, 109, 76952231] ⟨1174291045061, 2, [(2, 2), (5, 1), (7, 1), (109, 1), (76952231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_109
    · exact prime_76952231
  · decide +kernel

theorem prime_1174291045243 : Nat.Prime 1174291045243 := by
  apply nodeValid_prime [2, 3, 7, 911, 4759, 6449] ⟨1174291045243, 5, [(2, 1), (3, 1), (7, 1), (911, 1), (4759, 1), (6449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_911
    · exact prime_4759
    · exact prime_6449
  · decide +kernel

theorem prime_1175744766167 : Nat.Prime 1175744766167 := by
  apply nodeValid_prime [2, 587872383083] ⟨1175744766167, 5, [(2, 1), (587872383083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_587872383083
  · decide +kernel

theorem prime_1175744766583 : Nat.Prime 1175744766583 := by
  apply nodeValid_prime [2, 3, 105389, 206597] ⟨1175744766583, 3, [(2, 1), (3, 3), (105389, 1), (206597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105389
    · exact prime_206597
  · decide +kernel

theorem prime_1175744773367 : Nat.Prime 1175744773367 := by
  apply nodeValid_prime [2, 269, 2185399207] ⟨1175744773367, 5, [(2, 1), (269, 1), (2185399207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_2185399207
  · decide +kernel

theorem prime_1177199734637 : Nat.Prime 1177199734637 := by
  apply nodeValid_prime [2, 191, 4933, 312353] ⟨1177199734637, 2, [(2, 2), (191, 1), (4933, 1), (312353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_4933
    · exact prime_312353
  · decide +kernel

theorem prime_1177199737249 : Nat.Prime 1177199737249 := by
  apply nodeValid_prime [2, 3, 197, 62246179] ⟨1177199737249, 11, [(2, 5), (3, 1), (197, 1), (62246179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_62246179
  · decide +kernel

theorem prime_1177199737277 : Nat.Prime 1177199737277 := by
  apply nodeValid_prime [2, 294299934319] ⟨1177199737277, 2, [(2, 2), (294299934319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_294299934319
  · decide +kernel

theorem prime_1178655898741 : Nat.Prime 1178655898741 := by
  apply nodeValid_prime [2, 3, 5, 991, 19822669] ⟨1178655898741, 2, [(2, 2), (3, 1), (5, 1), (991, 1), (19822669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_991
    · exact prime_19822669
  · decide +kernel

theorem prime_1178655900673 : Nat.Prime 1178655900673 := by
  apply nodeValid_prime [2, 3, 19, 2663, 7583] ⟨1178655900673, 7, [(2, 10), (3, 1), (19, 1), (2663, 1), (7583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2663
    · exact prime_7583
  · decide +kernel

theorem prime_1178655918059 : Nat.Prime 1178655918059 := by
  apply nodeValid_prime [2, 67, 89, 683, 144701] ⟨1178655918059, 2, [(2, 1), (67, 1), (89, 1), (683, 1), (144701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_89
    · exact prime_683
    · exact prime_144701
  · decide +kernel

theorem prime_1180113321733 : Nat.Prime 1180113321733 := by
  apply nodeValid_prime [2, 3, 98342776811] ⟨1180113321733, 2, [(2, 2), (3, 1), (98342776811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_98342776811
  · decide +kernel

theorem prime_1180113368219 : Nat.Prime 1180113368219 := by
  apply nodeValid_prime [2, 590056684109] ⟨1180113368219, 2, [(2, 1), (590056684109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_590056684109
  · decide +kernel

theorem prime_1180113368237 : Nat.Prime 1180113368237 := by
  apply nodeValid_prime [2, 11, 26820758369] ⟨1180113368237, 2, [(2, 2), (11, 1), (26820758369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_26820758369
  · decide +kernel

theorem prime_1181571937487 : Nat.Prime 1181571937487 := by
  apply nodeValid_prime [2, 590785968743] ⟨1181571937487, 5, [(2, 1), (590785968743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_590785968743
  · decide +kernel

theorem prime_1181571937703 : Nat.Prime 1181571937703 := by
  apply nodeValid_prime [2, 13, 45445074527] ⟨1181571937703, 10, [(2, 1), (13, 1), (45445074527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_45445074527
  · decide +kernel

theorem prime_1181571943841 : Nat.Prime 1181571943841 := by
  apply nodeValid_prime [2, 5, 33577, 219937] ⟨1181571943841, 3, [(2, 5), (5, 1), (33577, 1), (219937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33577
    · exact prime_219937
  · decide +kernel

theorem prime_1183031792269 : Nat.Prime 1183031792269 := by
  apply nodeValid_prime [2, 3, 19, 97, 103, 619, 839] ⟨1183031792269, 2, [(2, 2), (3, 1), (19, 1), (97, 1), (103, 1), (619, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_97
    · exact prime_103
    · exact prime_619
    · exact prime_839
  · decide +kernel

theorem prime_1183031822177 : Nat.Prime 1183031822177 := by
  apply nodeValid_prime [2, 89, 1637, 253751] ⟨1183031822177, 3, [(2, 5), (89, 1), (1637, 1), (253751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1637
    · exact prime_253751
  · decide +kernel

theorem prime_1183031822311 : Nat.Prime 1183031822311 := by
  apply nodeValid_prime [2, 3, 5, 13, 811, 3740339] ⟨1183031822311, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (811, 1), (3740339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_811
    · exact prime_3740339
  · decide +kernel

theorem prime_1184492829043 : Nat.Prime 1184492829043 := by
  apply nodeValid_prime [2, 3, 47, 4919, 284633] ⟨1184492829043, 3, [(2, 1), (3, 2), (47, 1), (4919, 1), (284633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_4919
    · exact prime_284633
  · decide +kernel

theorem prime_1184492829977 : Nat.Prime 1184492829977 := by
  apply nodeValid_prime [2, 29, 227, 1033, 21773] ⟨1184492829977, 3, [(2, 3), (29, 1), (227, 1), (1033, 1), (21773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_227
    · exact prime_1033
    · exact prime_21773
  · decide +kernel

theorem prime_1184492863171 : Nat.Prime 1184492863171 := by
  apply nodeValid_prime [2, 3, 5, 13161031813] ⟨1184492863171, 2, [(2, 1), (3, 2), (5, 1), (13161031813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13161031813
  · decide +kernel

end Sude.Lucas.Generated
