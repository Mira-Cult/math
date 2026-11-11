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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0061

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5641 : Nat.Prime 5641 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨5641, 14, [(2, 3), (3, 1), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_11807 : Nat.Prime 11807 := by
  apply nodeValid_prime [2, 5903] ⟨11807, 5, [(2, 1), (5903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5903
  · decide +kernel

theorem prime_12569 : Nat.Prime 12569 := by
  apply nodeValid_prime [2, 1571] ⟨12569, 3, [(2, 3), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1571
  · decide +kernel

theorem prime_12973 : Nat.Prime 12973 := by
  apply nodeValid_prime [2, 3, 23, 47] ⟨12973, 14, [(2, 2), (3, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_13003 : Nat.Prime 13003 := by
  apply nodeValid_prime [2, 3, 11, 197] ⟨13003, 5, [(2, 1), (3, 1), (11, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_197
  · decide +kernel

theorem prime_15641 : Nat.Prime 15641 := by
  apply nodeValid_prime [2, 5, 17, 23] ⟨15641, 3, [(2, 3), (5, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_15679 : Nat.Prime 15679 := by
  apply nodeValid_prime [2, 3, 13, 67] ⟨15679, 11, [(2, 1), (3, 2), (13, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_19861 : Nat.Prime 19861 := by
  apply nodeValid_prime [2, 3, 5, 331] ⟨19861, 11, [(2, 2), (3, 1), (5, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_331
  · decide +kernel

theorem prime_21323 : Nat.Prime 21323 := by
  apply nodeValid_prime [2, 7, 1523] ⟨21323, 5, [(2, 1), (7, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1523
  · decide +kernel

theorem prime_21487 : Nat.Prime 21487 := by
  apply nodeValid_prime [2, 3, 3581] ⟨21487, 3, [(2, 1), (3, 1), (3581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3581
  · decide +kernel

theorem prime_21893 : Nat.Prime 21893 := by
  apply nodeValid_prime [2, 13, 421] ⟨21893, 2, [(2, 2), (13, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_421
  · decide +kernel

theorem prime_25733 : Nat.Prime 25733 := by
  apply nodeValid_prime [2, 7, 919] ⟨25733, 2, [(2, 2), (7, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_919
  · decide +kernel

theorem prime_33493 : Nat.Prime 33493 := by
  apply nodeValid_prime [2, 3, 2791] ⟨33493, 2, [(2, 2), (3, 1), (2791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2791
  · decide +kernel

theorem prime_36739 : Nat.Prime 36739 := by
  apply nodeValid_prime [2, 3, 13, 157] ⟨36739, 2, [(2, 1), (3, 2), (13, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_157
  · decide +kernel

theorem prime_36899 : Nat.Prime 36899 := by
  apply nodeValid_prime [2, 19, 971] ⟨36899, 2, [(2, 1), (19, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_971
  · decide +kernel

theorem prime_37649 : Nat.Prime 37649 := by
  apply nodeValid_prime [2, 13, 181] ⟨37649, 3, [(2, 4), (13, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_181
  · decide +kernel

theorem prime_39397 : Nat.Prime 39397 := by
  apply nodeValid_prime [2, 3, 7, 67] ⟨39397, 2, [(2, 2), (3, 1), (7, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_41183 : Nat.Prime 41183 := by
  apply nodeValid_prime [2, 59, 349] ⟨41183, 5, [(2, 1), (59, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_349
  · decide +kernel

theorem prime_43151 : Nat.Prime 43151 := by
  apply nodeValid_prime [2, 5, 863] ⟨43151, 11, [(2, 1), (5, 2), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_863
  · decide +kernel

theorem prime_43787 : Nat.Prime 43787 := by
  apply nodeValid_prime [2, 21893] ⟨43787, 2, [(2, 1), (21893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21893
  · decide +kernel

theorem prime_44507 : Nat.Prime 44507 := by
  apply nodeValid_prime [2, 7, 11, 17] ⟨44507, 2, [(2, 1), (7, 1), (11, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_54583 : Nat.Prime 54583 := by
  apply nodeValid_prime [2, 3, 11, 827] ⟨54583, 5, [(2, 1), (3, 1), (11, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_827
  · decide +kernel

theorem prime_54983 : Nat.Prime 54983 := by
  apply nodeValid_prime [2, 37, 743] ⟨54983, 5, [(2, 1), (37, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_743
  · decide +kernel

theorem prime_55439 : Nat.Prime 55439 := by
  apply nodeValid_prime [2, 53, 523] ⟨55439, 13, [(2, 1), (53, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_523
  · decide +kernel

theorem prime_60289 : Nat.Prime 60289 := by
  apply nodeValid_prime [2, 3, 157] ⟨60289, 7, [(2, 7), (3, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
  · decide +kernel

theorem prime_76679 : Nat.Prime 76679 := by
  apply nodeValid_prime [2, 7, 5477] ⟨76679, 7, [(2, 1), (7, 1), (5477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5477
  · decide +kernel

theorem prime_91513 : Nat.Prime 91513 := by
  apply nodeValid_prime [2, 3, 31, 41] ⟨91513, 10, [(2, 3), (3, 2), (31, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_41
  · decide +kernel

theorem prime_99767 : Nat.Prime 99767 := by
  apply nodeValid_prime [2, 83, 601] ⟨99767, 5, [(2, 1), (83, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_601
  · decide +kernel

theorem prime_115693 : Nat.Prime 115693 := by
  apply nodeValid_prime [2, 3, 31, 311] ⟨115693, 2, [(2, 2), (3, 1), (31, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_311
  · decide +kernel

theorem prime_128923 : Nat.Prime 128923 := by
  apply nodeValid_prime [2, 3, 21487] ⟨128923, 5, [(2, 1), (3, 1), (21487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21487
  · decide +kernel

theorem prime_135511 : Nat.Prime 135511 := by
  apply nodeValid_prime [2, 3, 5, 4517] ⟨135511, 3, [(2, 1), (3, 1), (5, 1), (4517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4517
  · decide +kernel

theorem prime_146603 : Nat.Prime 146603 := by
  apply nodeValid_prime [2, 23, 3187] ⟨146603, 2, [(2, 1), (23, 1), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3187
  · decide +kernel

theorem prime_153337 : Nat.Prime 153337 := by
  apply nodeValid_prime [2, 3, 6389] ⟨153337, 10, [(2, 3), (3, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6389
  · decide +kernel

theorem prime_160033 : Nat.Prime 160033 := by
  apply nodeValid_prime [2, 3, 1667] ⟨160033, 7, [(2, 5), (3, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1667
  · decide +kernel

theorem prime_197569 : Nat.Prime 197569 := by
  apply nodeValid_prime [2, 3, 7] ⟨197569, 13, [(2, 6), (3, 2), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_198827 : Nat.Prime 198827 := by
  apply nodeValid_prime [2, 89, 1117] ⟨198827, 2, [(2, 1), (89, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1117
  · decide +kernel

theorem prime_206953 : Nat.Prime 206953 := by
  apply nodeValid_prime [2, 3, 8623] ⟨206953, 5, [(2, 3), (3, 1), (8623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8623
  · decide +kernel

theorem prime_213361 : Nat.Prime 213361 := by
  apply nodeValid_prime [2, 3, 5, 7, 127] ⟨213361, 17, [(2, 4), (3, 1), (5, 1), (7, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_217489 : Nat.Prime 217489 := by
  apply nodeValid_prime [2, 3, 23, 197] ⟨217489, 7, [(2, 4), (3, 1), (23, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_197
  · decide +kernel

theorem prime_222113 : Nat.Prime 222113 := by
  apply nodeValid_prime [2, 11, 631] ⟨222113, 3, [(2, 5), (11, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_631
  · decide +kernel

theorem prime_234931 : Nat.Prime 234931 := by
  apply nodeValid_prime [2, 3, 5, 41, 191] ⟨234931, 3, [(2, 1), (3, 1), (5, 1), (41, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_191
  · decide +kernel

theorem prime_252169 : Nat.Prime 252169 := by
  apply nodeValid_prime [2, 3, 7, 19, 79] ⟨252169, 23, [(2, 3), (3, 1), (7, 1), (19, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_79
  · decide +kernel

theorem prime_281959 : Nat.Prime 281959 := by
  apply nodeValid_prime [2, 3, 46993] ⟨281959, 3, [(2, 1), (3, 1), (46993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_46993
  · decide +kernel

theorem prime_290369 : Nat.Prime 290369 := by
  apply nodeValid_prime [2, 13, 349] ⟨290369, 3, [(2, 6), (13, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_349
  · decide +kernel

theorem prime_314339 : Nat.Prime 314339 := by
  apply nodeValid_prime [2, 73, 2153] ⟨314339, 2, [(2, 1), (73, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_2153
  · decide +kernel

theorem prime_323987 : Nat.Prime 323987 := by
  apply nodeValid_prime [2, 13, 17, 733] ⟨323987, 2, [(2, 1), (13, 1), (17, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_733
  · decide +kernel

theorem prime_334931 : Nat.Prime 334931 := by
  apply nodeValid_prime [2, 5, 33493] ⟨334931, 2, [(2, 1), (5, 1), (33493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33493
  · decide +kernel

theorem prime_338203 : Nat.Prime 338203 := by
  apply nodeValid_prime [2, 3, 6263] ⟨338203, 2, [(2, 1), (3, 3), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6263
  · decide +kernel

theorem prime_453133 : Nat.Prime 453133 := by
  apply nodeValid_prime [2, 3, 41, 307] ⟨453133, 11, [(2, 2), (3, 2), (41, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_307
  · decide +kernel

theorem prime_453877 : Nat.Prime 453877 := by
  apply nodeValid_prime [2, 3, 109, 347] ⟨453877, 2, [(2, 2), (3, 1), (109, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_347
  · decide +kernel

theorem prime_477047 : Nat.Prime 477047 := by
  apply nodeValid_prime [2, 97, 2459] ⟨477047, 5, [(2, 1), (97, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_2459
  · decide +kernel

theorem prime_675511 : Nat.Prime 675511 := by
  apply nodeValid_prime [2, 3, 5, 11, 23, 89] ⟨675511, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_89
  · decide +kernel

theorem prime_733331 : Nat.Prime 733331 := by
  apply nodeValid_prime [2, 5, 13, 5641] ⟨733331, 7, [(2, 1), (5, 1), (13, 1), (5641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_5641
  · decide +kernel

theorem prime_869471 : Nat.Prime 869471 := by
  apply nodeValid_prime [2, 5, 7, 12421] ⟨869471, 7, [(2, 1), (5, 1), (7, 1), (12421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_12421
  · decide +kernel

theorem prime_949043 : Nat.Prime 949043 := by
  apply nodeValid_prime [2, 17, 103, 271] ⟨949043, 2, [(2, 1), (17, 1), (103, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
    · exact prime_271
  · decide +kernel

theorem prime_1078817 : Nat.Prime 1078817 := by
  apply nodeValid_prime [2, 33713] ⟨1078817, 3, [(2, 5), (33713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33713
  · decide +kernel

theorem prime_1107157 : Nat.Prime 1107157 := by
  apply nodeValid_prime [2, 3, 257, 359] ⟨1107157, 2, [(2, 2), (3, 1), (257, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_359
  · decide +kernel

theorem prime_1128143 : Nat.Prime 1128143 := by
  apply nodeValid_prime [2, 73, 7727] ⟨1128143, 5, [(2, 1), (73, 1), (7727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_7727
  · decide +kernel

theorem prime_1291421 : Nat.Prime 1291421 := by
  apply nodeValid_prime [2, 5, 13, 4967] ⟨1291421, 3, [(2, 2), (5, 1), (13, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4967
  · decide +kernel

theorem prime_1738943 : Nat.Prime 1738943 := by
  apply nodeValid_prime [2, 869471] ⟨1738943, 5, [(2, 1), (869471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_869471
  · decide +kernel

theorem prime_1929073 : Nat.Prime 1929073 := by
  apply nodeValid_prime [2, 3, 40189] ⟨1929073, 5, [(2, 4), (3, 1), (40189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40189
  · decide +kernel

theorem prime_2013287 : Nat.Prime 2013287 := by
  apply nodeValid_prime [2, 11, 91513] ⟨2013287, 10, [(2, 1), (11, 1), (91513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_91513
  · decide +kernel

theorem prime_2782643 : Nat.Prime 2782643 := by
  apply nodeValid_prime [2, 107, 13003] ⟨2782643, 2, [(2, 1), (107, 1), (13003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_13003
  · decide +kernel

theorem prime_2959597 : Nat.Prime 2959597 := by
  apply nodeValid_prime [2, 3, 229, 359] ⟨2959597, 2, [(2, 2), (3, 2), (229, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_359
  · decide +kernel

theorem prime_3099517 : Nat.Prime 3099517 := by
  apply nodeValid_prime [2, 3, 7, 36899] ⟨3099517, 6, [(2, 2), (3, 1), (7, 1), (36899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_36899
  · decide +kernel

theorem prime_3639763 : Nat.Prime 3639763 := by
  apply nodeValid_prime [2, 3, 7, 9629] ⟨3639763, 2, [(2, 1), (3, 3), (7, 1), (9629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9629
  · decide +kernel

theorem prime_3705917 : Nat.Prime 3705917 := by
  apply nodeValid_prime [2, 71, 13049] ⟨3705917, 2, [(2, 2), (71, 1), (13049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_13049
  · decide +kernel

theorem prime_3985073 : Nat.Prime 3985073 := by
  apply nodeValid_prime [2, 7, 13, 17, 23] ⟨3985073, 10, [(2, 4), (7, 2), (13, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_3990859 : Nat.Prime 3990859 := by
  apply nodeValid_prime [2, 3, 41, 16223] ⟨3990859, 2, [(2, 1), (3, 1), (41, 1), (16223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_16223
  · decide +kernel

theorem prime_4535819 : Nat.Prime 4535819 := by
  apply nodeValid_prime [2, 7, 323987] ⟨4535819, 2, [(2, 1), (7, 1), (323987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_323987
  · decide +kernel

theorem prime_4558501 : Nat.Prime 4558501 := by
  apply nodeValid_prime [2, 3, 5, 1013] ⟨4558501, 2, [(2, 2), (3, 2), (5, 3), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1013
  · decide +kernel

theorem prime_5441123 : Nat.Prime 5441123 := by
  apply nodeValid_prime [2, 17, 160033] ⟨5441123, 2, [(2, 1), (17, 1), (160033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_160033
  · decide +kernel

theorem prime_5974109 : Nat.Prime 5974109 := by
  apply nodeValid_prime [2, 7, 213361] ⟨5974109, 2, [(2, 2), (7, 1), (213361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_213361
  · decide +kernel

theorem prime_8792669 : Nat.Prime 8792669 := by
  apply nodeValid_prime [2, 19, 115693] ⟨8792669, 2, [(2, 2), (19, 1), (115693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_115693
  · decide +kernel

theorem prime_9477137 : Nat.Prime 9477137 := by
  apply nodeValid_prime [2, 592321] ⟨9477137, 3, [(2, 4), (592321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_592321
  · decide +kernel

theorem prime_11838389 : Nat.Prime 11838389 := by
  apply nodeValid_prime [2, 2959597] ⟨11838389, 2, [(2, 2), (2959597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2959597
  · decide +kernel

theorem prime_11841307 : Nat.Prime 11841307 := by
  apply nodeValid_prime [2, 3, 1213, 1627] ⟨11841307, 2, [(2, 1), (3, 1), (1213, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1213
    · exact prime_1627
  · decide +kernel

theorem prime_16047637 : Nat.Prime 16047637 := by
  apply nodeValid_prime [2, 3, 11, 61, 1993] ⟨16047637, 2, [(2, 2), (3, 1), (11, 1), (61, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
    · exact prime_1993
  · decide +kernel

theorem prime_16106297 : Nat.Prime 16106297 := by
  apply nodeValid_prime [2, 2013287] ⟨16106297, 3, [(2, 3), (2013287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2013287
  · decide +kernel

theorem prime_17324563 : Nat.Prime 17324563 := by
  apply nodeValid_prime [2, 3, 89, 32443] ⟨17324563, 3, [(2, 1), (3, 1), (89, 1), (32443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_32443
  · decide +kernel

theorem prime_21333973 : Nat.Prime 21333973 := by
  apply nodeValid_prime [2, 3, 11, 23, 7027] ⟨21333973, 6, [(2, 2), (3, 1), (11, 1), (23, 1), (7027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_7027
  · decide +kernel

theorem prime_23148877 : Nat.Prime 23148877 := by
  apply nodeValid_prime [2, 3, 1929073] ⟨23148877, 5, [(2, 2), (3, 1), (1929073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1929073
  · decide +kernel

theorem prime_26967881 : Nat.Prime 26967881 := by
  apply nodeValid_prime [2, 5, 43, 15679] ⟨26967881, 6, [(2, 3), (5, 1), (43, 1), (15679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_15679
  · decide +kernel

theorem prime_37347809 : Nat.Prime 37347809 := by
  apply nodeValid_prime [2, 31, 37649] ⟨37347809, 3, [(2, 5), (31, 1), (37649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37649
  · decide +kernel

theorem prime_37726069 : Nat.Prime 37726069 := by
  apply nodeValid_prime [2, 3, 41, 76679] ⟨37726069, 7, [(2, 2), (3, 1), (41, 1), (76679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_76679
  · decide +kernel

theorem prime_38703193 : Nat.Prime 38703193 := by
  apply nodeValid_prime [2, 3, 11, 146603] ⟨38703193, 5, [(2, 3), (3, 1), (11, 1), (146603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_146603
  · decide +kernel

theorem prime_40364509 : Nat.Prime 40364509 := by
  apply nodeValid_prime [2, 3, 487, 6907] ⟨40364509, 2, [(2, 2), (3, 1), (487, 1), (6907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
    · exact prime_6907
  · decide +kernel

theorem prime_50143589 : Nat.Prime 50143589 := by
  apply nodeValid_prime [2, 11, 23, 49549] ⟨50143589, 3, [(2, 2), (11, 1), (23, 1), (49549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_49549
  · decide +kernel

theorem prime_55854361 : Nat.Prime 55854361 := by
  apply nodeValid_prime [2, 3, 5, 17239] ⟨55854361, 11, [(2, 3), (3, 4), (5, 1), (17239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17239
  · decide +kernel

theorem prime_61643579 : Nat.Prime 61643579 := by
  apply nodeValid_prime [2, 4993, 6173] ⟨61643579, 2, [(2, 1), (4993, 1), (6173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4993
    · exact prime_6173
  · decide +kernel

theorem prime_67506557 : Nat.Prime 67506557 := by
  apply nodeValid_prime [2, 13, 83, 15641] ⟨67506557, 2, [(2, 2), (13, 1), (83, 1), (15641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_83
    · exact prime_15641
  · decide +kernel

theorem prime_71047843 : Nat.Prime 71047843 := by
  apply nodeValid_prime [2, 3, 11841307] ⟨71047843, 3, [(2, 1), (3, 1), (11841307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11841307
  · decide +kernel

theorem prime_92982313 : Nat.Prime 92982313 := by
  apply nodeValid_prime [2, 3, 1291421] ⟨92982313, 10, [(2, 3), (3, 2), (1291421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1291421
  · decide +kernel

theorem prime_120948791 : Nat.Prime 120948791 := by
  apply nodeValid_prime [2, 5, 307, 39397] ⟨120948791, 13, [(2, 1), (5, 1), (307, 1), (39397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_307
    · exact prime_39397
  · decide +kernel

theorem prime_130493401 : Nat.Prime 130493401 := by
  apply nodeValid_prime [2, 3, 5, 217489] ⟨130493401, 17, [(2, 3), (3, 1), (5, 2), (217489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_217489
  · decide +kernel

theorem prime_136074571 : Nat.Prime 136074571 := by
  apply nodeValid_prime [2, 3, 5, 4535819] ⟨136074571, 3, [(2, 1), (3, 1), (5, 1), (4535819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4535819
  · decide +kernel

theorem prime_158999053 : Nat.Prime 158999053 := by
  apply nodeValid_prime [2, 3, 239, 55439] ⟨158999053, 2, [(2, 2), (3, 1), (239, 1), (55439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_55439
  · decide +kernel

theorem prime_241897583 : Nat.Prime 241897583 := by
  apply nodeValid_prime [2, 120948791] ⟨241897583, 5, [(2, 1), (120948791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120948791
  · decide +kernel

theorem prime_337302377 : Nat.Prime 337302377 := by
  apply nodeValid_prime [2, 3571, 11807] ⟨337302377, 3, [(2, 3), (3571, 1), (11807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3571
    · exact prime_11807
  · decide +kernel

theorem prime_371929253 : Nat.Prime 371929253 := by
  apply nodeValid_prime [2, 92982313] ⟨371929253, 2, [(2, 2), (92982313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92982313
  · decide +kernel

theorem prime_482720453 : Nat.Prime 482720453 := by
  apply nodeValid_prime [2, 109, 1107157] ⟨482720453, 2, [(2, 2), (109, 1), (1107157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_1107157
  · decide +kernel

theorem prime_505575061 : Nat.Prime 505575061 := by
  apply nodeValid_prime [2, 3, 5, 1489, 5659] ⟨505575061, 6, [(2, 2), (3, 1), (5, 1), (1489, 1), (5659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1489
    · exact prime_5659
  · decide +kernel

theorem prime_515372687 : Nat.Prime 515372687 := by
  apply nodeValid_prime [2, 4721, 54583] ⟨515372687, 5, [(2, 1), (4721, 1), (54583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4721
    · exact prime_54583
  · decide +kernel

theorem prime_767564587 : Nat.Prime 767564587 := by
  apply nodeValid_prime [2, 3, 17, 61, 1523] ⟨767564587, 3, [(2, 1), (3, 5), (17, 1), (61, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_1523
  · decide +kernel

theorem prime_965440907 : Nat.Prime 965440907 := by
  apply nodeValid_prime [2, 482720453] ⟨965440907, 2, [(2, 1), (482720453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_482720453
  · decide +kernel

theorem prime_965969581 : Nat.Prime 965969581 := by
  apply nodeValid_prime [2, 3, 5, 17, 73, 12973] ⟨965969581, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (73, 1), (12973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_73
    · exact prime_12973
  · decide +kernel

theorem prime_1264553803 : Nat.Prime 1264553803 := by
  apply nodeValid_prime [2, 3, 2549, 9187] ⟨1264553803, 2, [(2, 1), (3, 3), (2549, 1), (9187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2549
    · exact prime_9187
  · decide +kernel

theorem prime_1597961569 : Nat.Prime 1597961569 := by
  apply nodeValid_prime [2, 3, 7, 883, 2693] ⟨1597961569, 17, [(2, 5), (3, 1), (7, 1), (883, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_883
    · exact prime_2693
  · decide +kernel

theorem prime_2106030739 : Nat.Prime 2106030739 := by
  apply nodeValid_prime [2, 3, 7, 50143589] ⟨2106030739, 2, [(2, 1), (3, 1), (7, 1), (50143589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_50143589
  · decide +kernel

theorem prime_2240256673 : Nat.Prime 2240256673 := by
  apply nodeValid_prime [2, 3, 23, 338203] ⟨2240256673, 13, [(2, 5), (3, 2), (23, 1), (338203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_338203
  · decide +kernel

theorem prime_2704156307 : Nat.Prime 2704156307 := by
  apply nodeValid_prime [2, 17, 1787, 44507] ⟨2704156307, 2, [(2, 1), (17, 1), (1787, 1), (44507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1787
    · exact prime_44507
  · decide +kernel

theorem prime_2913929981 : Nat.Prime 2913929981 := by
  apply nodeValid_prime [2, 5, 13, 3307, 3389] ⟨2913929981, 3, [(2, 2), (5, 1), (13, 1), (3307, 1), (3389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_3307
    · exact prime_3389
  · decide +kernel

theorem prime_3271361579 : Nat.Prime 3271361579 := by
  apply nodeValid_prime [2, 17, 9613, 10009] ⟨3271361579, 2, [(2, 1), (17, 1), (9613, 1), (10009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9613
    · exact prime_10009
  · decide +kernel

theorem prime_5058215213 : Nat.Prime 5058215213 := by
  apply nodeValid_prime [2, 1264553803] ⟨5058215213, 2, [(2, 2), (1264553803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1264553803
  · decide +kernel

theorem prime_5399636069 : Nat.Prime 5399636069 := by
  apply nodeValid_prime [2, 19, 71047843] ⟨5399636069, 2, [(2, 2), (19, 1), (71047843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71047843
  · decide +kernel

theorem prime_27522764723 : Nat.Prime 27522764723 := by
  apply nodeValid_prime [2, 37, 371929253] ⟨27522764723, 2, [(2, 1), (37, 1), (371929253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_371929253
  · decide +kernel

theorem prime_30349291279 : Nat.Prime 30349291279 := by
  apply nodeValid_prime [2, 3, 5058215213] ⟨30349291279, 6, [(2, 1), (3, 1), (5058215213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5058215213
  · decide +kernel

theorem prime_38122701343 : Nat.Prime 38122701343 := by
  apply nodeValid_prime [2, 3, 11, 23, 103, 10601] ⟨38122701343, 3, [(2, 1), (3, 1), (11, 1), (23, 2), (103, 1), (10601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_103
    · exact prime_10601
  · decide +kernel

theorem prime_74122199587 : Nat.Prime 74122199587 := by
  apply nodeValid_prime [2, 3, 61, 67506557] ⟨74122199587, 2, [(2, 1), (3, 2), (61, 1), (67506557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_67506557
  · decide +kernel

theorem prime_118595519473 : Nat.Prime 118595519473 := by
  apply nodeValid_prime [2, 3, 281, 8792669] ⟨118595519473, 5, [(2, 4), (3, 1), (281, 1), (8792669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_8792669
  · decide +kernel

theorem prime_203569705561 : Nat.Prime 203569705561 := by
  apply nodeValid_prime [2, 3, 5, 13, 130493401] ⟨203569705561, 14, [(2, 3), (3, 1), (5, 1), (13, 1), (130493401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_130493401
  · decide +kernel

theorem prime_607729277453 : Nat.Prime 607729277453 := by
  apply nodeValid_prime [2, 11, 59, 353, 60289] ⟨607729277453, 2, [(2, 2), (11, 2), (59, 1), (353, 1), (60289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_353
    · exact prime_60289
  · decide +kernel

theorem prime_609963221489 : Nat.Prime 609963221489 := by
  apply nodeValid_prime [2, 38122701343] ⟨609963221489, 3, [(2, 4), (38122701343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38122701343
  · decide +kernel

theorem prime_1185955157533 : Nat.Prime 1185955157533 := by
  apply nodeValid_prime [2, 3, 293, 337302377] ⟨1185955157533, 2, [(2, 2), (3, 1), (293, 1), (337302377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_337302377
  · decide +kernel

theorem prime_1185955193393 : Nat.Prime 1185955193393 := by
  apply nodeValid_prime [2, 74122199587] ⟨1185955193393, 3, [(2, 4), (74122199587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_74122199587
  · decide +kernel

theorem prime_1185955194731 : Nat.Prime 1185955194731 := by
  apply nodeValid_prime [2, 5, 118595519473] ⟨1185955194731, 10, [(2, 1), (5, 1), (118595519473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_118595519473
  · decide +kernel

theorem prime_1187418670849 : Nat.Prime 1187418670849 := by
  apply nodeValid_prime [2, 3, 515372687] ⟨1187418670849, 13, [(2, 8), (3, 2), (515372687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_515372687
  · decide +kernel

theorem prime_1187418763357 : Nat.Prime 1187418763357 := by
  apply nodeValid_prime [2, 3, 7, 31, 2053, 222113] ⟨1187418763357, 5, [(2, 2), (3, 1), (7, 1), (31, 1), (2053, 1), (222113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_2053
    · exact prime_222113
  · decide +kernel

theorem prime_1187418763667 : Nat.Prime 1187418763667 := by
  apply nodeValid_prime [2, 31, 37, 167, 3099517] ⟨1187418763667, 2, [(2, 1), (31, 1), (37, 1), (167, 1), (3099517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37
    · exact prime_167
    · exact prime_3099517
  · decide +kernel

theorem prime_1188883407337 : Nat.Prime 1188883407337 := by
  apply nodeValid_prime [2, 3, 31, 1597961569] ⟨1188883407337, 5, [(2, 3), (3, 1), (31, 1), (1597961569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1597961569
  · decide +kernel

theorem prime_1188883432201 : Nat.Prime 1188883432201 := by
  apply nodeValid_prime [2, 3, 5, 19861, 99767] ⟨1188883432201, 7, [(2, 3), (3, 1), (5, 2), (19861, 1), (99767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19861
    · exact prime_99767
  · decide +kernel

theorem prime_1188883432249 : Nat.Prime 1188883432249 := by
  apply nodeValid_prime [2, 3, 17, 2913929981] ⟨1188883432249, 11, [(2, 3), (3, 1), (17, 1), (2913929981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2913929981
  · decide +kernel

theorem prime_1190349368059 : Nat.Prime 1190349368059 := by
  apply nodeValid_prime [2, 3, 193, 4967, 206953] ⟨1190349368059, 2, [(2, 1), (3, 1), (193, 1), (4967, 1), (206953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_4967
    · exact prime_206953
  · decide +kernel

theorem prime_1190349368449 : Nat.Prime 1190349368449 := by
  apply nodeValid_prime [2, 3, 83, 37347809] ⟨1190349368449, 11, [(2, 7), (3, 1), (83, 1), (37347809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_37347809
  · decide +kernel

theorem prime_1190349370411 : Nat.Prime 1190349370411 := by
  apply nodeValid_prime [2, 3, 5, 983, 40364509] ⟨1190349370411, 2, [(2, 1), (3, 1), (5, 1), (983, 1), (40364509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_983
    · exact prime_40364509
  · decide +kernel

theorem prime_1191816550037 : Nat.Prime 1191816550037 := by
  apply nodeValid_prime [2, 7, 19, 2240256673] ⟨1191816550037, 2, [(2, 2), (7, 1), (19, 1), (2240256673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_2240256673
  · decide +kernel

theorem prime_1191816551467 : Nat.Prime 1191816551467 := by
  apply nodeValid_prime [2, 3, 1801, 453877] ⟨1191816551467, 2, [(2, 1), (3, 6), (1801, 1), (453877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1801
    · exact prime_453877
  · decide +kernel

theorem prime_1191816552271 : Nat.Prime 1191816552271 := by
  apply nodeValid_prime [2, 3, 5, 563, 7603, 9281] ⟨1191816552271, 7, [(2, 1), (3, 1), (5, 1), (563, 1), (7603, 1), (9281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_563
    · exact prime_7603
    · exact prime_9281
  · decide +kernel

theorem prime_1193284910309 : Nat.Prime 1193284910309 := by
  apply nodeValid_prime [2, 314339, 949043] ⟨1193284910309, 2, [(2, 2), (314339, 1), (949043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_314339
    · exact prime_949043
  · decide +kernel

theorem prime_1193284911809 : Nat.Prime 1193284911809 := by
  apply nodeValid_prime [2, 11, 199, 331, 25733] ⟨1193284911809, 3, [(2, 6), (11, 1), (199, 1), (331, 1), (25733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_199
    · exact prime_331
    · exact prime_25733
  · decide +kernel

theorem prime_1193284961053 : Nat.Prime 1193284961053 := by
  apply nodeValid_prime [2, 3, 103, 965440907] ⟨1193284961053, 2, [(2, 2), (3, 1), (103, 1), (965440907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_965440907
  · decide +kernel

theorem prime_1194754598497 : Nat.Prime 1194754598497 := by
  apply nodeValid_prime [2, 3, 5657, 733331] ⟨1194754598497, 10, [(2, 5), (3, 2), (5657, 1), (733331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5657
    · exact prime_733331
  · decide +kernel

theorem prime_1194754610353 : Nat.Prime 1194754610353 := by
  apply nodeValid_prime [2, 3, 23, 3727, 290369] ⟨1194754610353, 7, [(2, 4), (3, 1), (23, 1), (3727, 1), (290369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3727
    · exact prime_290369
  · decide +kernel

theorem prime_1196225459753 : Nat.Prime 1196225459753 := by
  apply nodeValid_prime [2, 71, 2106030739] ⟨1196225459753, 3, [(2, 3), (71, 1), (2106030739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2106030739
  · decide +kernel

theorem prime_1196225463049 : Nat.Prime 1196225463049 := by
  apply nodeValid_prime [2, 3, 7, 11, 2143, 43151] ⟨1196225463049, 13, [(2, 3), (3, 1), (7, 2), (11, 1), (2143, 1), (43151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_2143
    · exact prime_43151
  · decide +kernel

theorem prime_1196225463493 : Nat.Prime 1196225463493 := by
  apply nodeValid_prime [2, 3, 53, 1621, 128923] ⟨1196225463493, 2, [(2, 2), (3, 3), (53, 1), (1621, 1), (128923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1621
    · exact prime_128923
  · decide +kernel

theorem prime_1197697528523 : Nat.Prime 1197697528523 := by
  apply nodeValid_prime [2, 11, 41, 107, 1128143] ⟨1197697528523, 2, [(2, 1), (11, 2), (41, 1), (107, 1), (1128143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_107
    · exact prime_1128143
  · decide +kernel

theorem prime_1197697530973 : Nat.Prime 1197697530973 := by
  apply nodeValid_prime [2, 3, 3701, 26967881] ⟨1197697530973, 2, [(2, 2), (3, 1), (3701, 1), (26967881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3701
    · exact prime_26967881
  · decide +kernel

theorem prime_1197697545349 : Nat.Prime 1197697545349 := by
  apply nodeValid_prime [2, 3, 479, 739, 281959] ⟨1197697545349, 2, [(2, 2), (3, 1), (479, 1), (739, 1), (281959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
    · exact prime_739
    · exact prime_281959
  · decide +kernel

theorem prime_1199170857727 : Nat.Prime 1199170857727 := by
  apply nodeValid_prime [2, 3, 419, 158999053] ⟨1199170857727, 5, [(2, 1), (3, 2), (419, 1), (158999053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419
    · exact prime_158999053
  · decide +kernel

theorem prime_1199170875713 : Nat.Prime 1199170875713 := by
  apply nodeValid_prime [2, 43, 1301, 334931] ⟨1199170875713, 3, [(2, 6), (43, 1), (1301, 1), (334931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1301
    · exact prime_334931
  · decide +kernel

theorem prime_1199170877033 : Nat.Prime 1199170877033 := by
  apply nodeValid_prime [2, 41183, 3639763] ⟨1199170877033, 3, [(2, 3), (41183, 1), (3639763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41183
    · exact prime_3639763
  · decide +kernel

theorem prime_1200645344057 : Nat.Prime 1200645344057 := by
  apply nodeValid_prime [2, 2687, 55854361] ⟨1200645344057, 3, [(2, 3), (2687, 1), (55854361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2687
    · exact prime_55854361
  · decide +kernel

theorem prime_1200645344387 : Nat.Prime 1200645344387 := by
  apply nodeValid_prime [2, 79, 1667, 4558501] ⟨1200645344387, 2, [(2, 1), (79, 1), (1667, 1), (4558501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1667
    · exact prime_4558501
  · decide +kernel

theorem prime_1200645400309 : Nat.Prime 1200645400309 := by
  apply nodeValid_prime [2, 3, 37, 2704156307] ⟨1200645400309, 2, [(2, 2), (3, 1), (37, 1), (2704156307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2704156307
  · decide +kernel

theorem prime_1202121174581 : Nat.Prime 1202121174581 := by
  apply nodeValid_prime [2, 5, 1553, 38703193] ⟨1202121174581, 2, [(2, 2), (5, 1), (1553, 1), (38703193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1553
    · exact prime_38703193
  · decide +kernel

theorem prime_1202121180889 : Nat.Prime 1202121180889 := by
  apply nodeValid_prime [2, 3, 12569, 3985073] ⟨1202121180889, 7, [(2, 3), (3, 1), (12569, 1), (3985073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12569
    · exact prime_3985073
  · decide +kernel

theorem prime_1202121182611 : Nat.Prime 1202121182611 := by
  apply nodeValid_prime [2, 3, 5, 577, 23148877] ⟨1202121182611, 3, [(2, 1), (3, 2), (5, 1), (577, 1), (23148877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_577
    · exact prime_23148877
  · decide +kernel

theorem prime_1203598097927 : Nat.Prime 1203598097927 := by
  apply nodeValid_prime [2, 7, 89, 965969581] ⟨1203598097927, 5, [(2, 1), (7, 1), (89, 1), (965969581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_965969581
  · decide +kernel

theorem prime_1203598097959 : Nat.Prime 1203598097959 := by
  apply nodeValid_prime [2, 3, 59, 97, 139, 252169] ⟨1203598097959, 3, [(2, 1), (3, 1), (59, 1), (97, 1), (139, 1), (252169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_97
    · exact prime_139
    · exact prime_252169
  · decide +kernel

theorem prime_1203598172093 : Nat.Prime 1203598172093 := by
  apply nodeValid_prime [2, 17, 3253, 5441123] ⟨1203598172093, 3, [(2, 2), (17, 1), (3253, 1), (5441123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3253
    · exact prime_5441123
  · decide +kernel

theorem prime_1205076400457 : Nat.Prime 1205076400457 := by
  apply nodeValid_prime [2, 401, 829, 453133] ⟨1205076400457, 3, [(2, 3), (401, 1), (829, 1), (453133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_401
    · exact prime_829
    · exact prime_453133
  · decide +kernel

theorem prime_1205076400777 : Nat.Prime 1205076400777 := by
  apply nodeValid_prime [2, 3, 41, 136074571] ⟨1205076400777, 5, [(2, 3), (3, 3), (41, 1), (136074571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_136074571
  · decide +kernel

theorem prime_1205076401591 : Nat.Prime 1205076401591 := by
  apply nodeValid_prime [2, 5, 157, 767564587] ⟨1205076401591, 17, [(2, 1), (5, 1), (157, 1), (767564587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_767564587
  · decide +kernel

theorem prime_1206555858691 : Nat.Prime 1206555858691 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 2237, 197569] ⟨1206555858691, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (2237, 1), (197569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_2237
    · exact prime_197569
  · decide +kernel

theorem prime_1206555859247 : Nat.Prime 1206555859247 := by
  apply nodeValid_prime [2, 23, 54983, 477047] ⟨1206555859247, 5, [(2, 1), (23, 1), (54983, 1), (477047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_54983
    · exact prime_477047
  · decide +kernel

theorem prime_1206555866519 : Nat.Prime 1206555866519 := by
  apply nodeValid_prime [2, 37, 24137, 675511] ⟨1206555866519, 11, [(2, 1), (37, 1), (24137, 1), (675511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_24137
    · exact prime_675511
  · decide +kernel

theorem prime_1208036529109 : Nat.Prime 1208036529109 := by
  apply nodeValid_prime [2, 3, 41, 137, 5974109] ⟨1208036529109, 10, [(2, 2), (3, 2), (41, 1), (137, 1), (5974109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_137
    · exact prime_5974109
  · decide +kernel

theorem prime_1208036529503 : Nat.Prime 1208036529503 := by
  apply nodeValid_prime [2, 11, 227, 241897583] ⟨1208036529503, 5, [(2, 1), (11, 1), (227, 1), (241897583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_227
    · exact prime_241897583
  · decide +kernel

theorem prime_1208036567117 : Nat.Prime 1208036567117 := by
  apply nodeValid_prime [2, 97, 263, 11838389] ⟨1208036567117, 2, [(2, 2), (97, 1), (263, 1), (11838389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_263
    · exact prime_11838389
  · decide +kernel

theorem prime_1209518479457 : Nat.Prime 1209518479457 := by
  apply nodeValid_prime [2, 7, 5399636069] ⟨1209518479457, 3, [(2, 5), (7, 1), (5399636069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5399636069
  · decide +kernel

theorem prime_1209518479513 : Nat.Prime 1209518479513 := by
  apply nodeValid_prime [2, 3, 7, 149, 16106297] ⟨1209518479513, 5, [(2, 3), (3, 2), (7, 1), (149, 1), (16106297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
    · exact prime_16106297
  · decide +kernel

theorem prime_1209518492359 : Nat.Prime 1209518492359 := by
  apply nodeValid_prime [2, 3, 11, 137, 331, 36739] ⟨1209518492359, 6, [(2, 1), (3, 1), (11, 2), (137, 1), (331, 1), (36739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
    · exact prime_331
    · exact prime_36739
  · decide +kernel

theorem prime_1211001643373 : Nat.Prime 1211001643373 := by
  apply nodeValid_prime [2, 23, 617, 21333973] ⟨1211001643373, 2, [(2, 2), (23, 1), (617, 1), (21333973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_617
    · exact prime_21333973
  · decide +kernel

theorem prime_1211001644873 : Nat.Prime 1211001644873 := by
  apply nodeValid_prime [2, 59, 67, 163, 234931] ⟨1211001644873, 3, [(2, 3), (59, 1), (67, 1), (163, 1), (234931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_67
    · exact prime_163
    · exact prime_234931
  · decide +kernel

theorem prime_1211001647813 : Nat.Prime 1211001647813 := by
  apply nodeValid_prime [2, 11, 27522764723] ⟨1211001647813, 2, [(2, 2), (11, 1), (27522764723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_27522764723
  · decide +kernel

theorem prime_1212485953507 : Nat.Prime 1212485953507 := by
  apply nodeValid_prime [2, 3, 21323, 9477137] ⟨1212485953507, 2, [(2, 1), (3, 1), (21323, 1), (9477137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21323
    · exact prime_9477137
  · decide +kernel

theorem prime_1212485953537 : Nat.Prime 1212485953537 := by
  apply nodeValid_prime [2, 3, 11, 13, 153337] ⟨1212485953537, 5, [(2, 11), (3, 3), (11, 1), (13, 1), (153337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_153337
  · decide +kernel

theorem prime_1212486026683 : Nat.Prime 1212486026683 := by
  apply nodeValid_prime [2, 3, 7, 647, 5147, 8669] ⟨1212486026683, 2, [(2, 1), (3, 1), (7, 1), (647, 1), (5147, 1), (8669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_647
    · exact prime_5147
    · exact prime_8669
  · decide +kernel

theorem prime_1213971643777 : Nat.Prime 1213971643777 := by
  apply nodeValid_prime [2, 3, 197, 16047637] ⟨1213971643777, 5, [(2, 7), (3, 1), (197, 1), (16047637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_16047637
  · decide +kernel

theorem prime_1213971651161 : Nat.Prime 1213971651161 := by
  apply nodeValid_prime [2, 5, 30349291279] ⟨1213971651161, 3, [(2, 3), (5, 1), (30349291279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30349291279
  · decide +kernel

theorem prime_1213971651437 : Nat.Prime 1213971651437 := by
  apply nodeValid_prime [2, 419, 3643, 198827] ⟨1213971651437, 2, [(2, 2), (419, 1), (3643, 1), (198827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_3643
    · exact prime_198827
  · decide +kernel

theorem prime_1215458491043 : Nat.Prime 1215458491043 := by
  apply nodeValid_prime [2, 89, 181, 37726069] ⟨1215458491043, 2, [(2, 1), (89, 1), (181, 1), (37726069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_181
    · exact prime_37726069
  · decide +kernel

theorem prime_1215458554907 : Nat.Prime 1215458554907 := by
  apply nodeValid_prime [2, 607729277453] ⟨1215458554907, 2, [(2, 1), (607729277453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_607729277453
  · decide +kernel

theorem prime_1215458555053 : Nat.Prime 1215458555053 := by
  apply nodeValid_prime [2, 3, 7, 53, 157, 1738943] ⟨1215458555053, 5, [(2, 2), (3, 1), (7, 1), (53, 1), (157, 1), (1738943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_157
    · exact prime_1738943
  · decide +kernel

theorem prime_1216946507389 : Nat.Prime 1216946507389 := by
  apply nodeValid_prime [2, 3, 31, 3271361579] ⟨1216946507389, 2, [(2, 2), (3, 1), (31, 1), (3271361579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3271361579
  · decide +kernel

theorem prime_1216946507687 : Nat.Prime 1216946507687 := by
  apply nodeValid_prime [2, 7, 13, 19, 53, 135511] ⟨1216946507687, 5, [(2, 1), (7, 3), (13, 1), (19, 1), (53, 1), (135511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_53
    · exact prime_135511
  · decide +kernel

theorem prime_1216946571047 : Nat.Prime 1216946571047 := by
  apply nodeValid_prime [2, 283, 1993, 1078817] ⟨1216946571047, 5, [(2, 1), (283, 1), (1993, 1), (1078817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_1993
    · exact prime_1078817
  · decide +kernel

theorem prime_1218435890411 : Nat.Prime 1218435890411 := by
  apply nodeValid_prime [2, 5, 43787, 2782643] ⟨1218435890411, 2, [(2, 1), (5, 1), (43787, 1), (2782643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43787
    · exact prime_2782643
  · decide +kernel

theorem prime_1218435892703 : Nat.Prime 1218435892703 := by
  apply nodeValid_prime [2, 7, 1069, 3607, 22571] ⟨1218435892703, 5, [(2, 1), (7, 1), (1069, 1), (3607, 1), (22571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1069
    · exact prime_3607
    · exact prime_22571
  · decide +kernel

theorem prime_1218435897011 : Nat.Prime 1218435897011 := by
  apply nodeValid_prime [2, 5, 241, 505575061] ⟨1218435897011, 2, [(2, 1), (5, 1), (241, 1), (505575061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_241
    · exact prime_505575061
  · decide +kernel

theorem prime_1219926428209 : Nat.Prime 1219926428209 := by
  apply nodeValid_prime [2, 3, 163, 17324563] ⟨1219926428209, 7, [(2, 4), (3, 3), (163, 1), (17324563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_17324563
  · decide +kernel

theorem prime_1219926428411 : Nat.Prime 1219926428411 := by
  apply nodeValid_prime [2, 5, 1979, 61643579] ⟨1219926428411, 2, [(2, 1), (5, 1), (1979, 1), (61643579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1979
    · exact prime_61643579
  · decide +kernel

theorem prime_1219926442979 : Nat.Prime 1219926442979 := by
  apply nodeValid_prime [2, 609963221489] ⟨1219926442979, 2, [(2, 1), (609963221489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_609963221489
  · decide +kernel

theorem prime_1221418233367 : Nat.Prime 1221418233367 := by
  apply nodeValid_prime [2, 3, 203569705561] ⟨1221418233367, 5, [(2, 1), (3, 1), (203569705561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_203569705561
  · decide +kernel

theorem prime_1221418360363 : Nat.Prime 1221418360363 := by
  apply nodeValid_prime [2, 3, 163, 337, 3705917] ⟨1221418360363, 3, [(2, 1), (3, 1), (163, 1), (337, 1), (3705917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_337
    · exact prime_3705917
  · decide +kernel

theorem prime_1221418360387 : Nat.Prime 1221418360387 := by
  apply nodeValid_prime [2, 3, 7, 347, 3990859] ⟨1221418360387, 2, [(2, 1), (3, 2), (7, 2), (347, 1), (3990859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_347
    · exact prime_3990859
  · decide +kernel

end Sude.Lucas.Generated
