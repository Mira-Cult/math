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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1879 : Nat.Prime 1879 := by
  apply nodeValid_prime [2, 3, 313] ⟨1879, 6, [(2, 1), (3, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
  · decide +kernel

theorem prime_2011 : Nat.Prime 2011 := by
  apply nodeValid_prime [2, 3, 5, 67] ⟨2011, 3, [(2, 1), (3, 1), (5, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_2377 : Nat.Prime 2377 := by
  apply nodeValid_prime [2, 3, 11] ⟨2377, 5, [(2, 3), (3, 3), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_2897 : Nat.Prime 2897 := by
  apply nodeValid_prime [2, 181] ⟨2897, 3, [(2, 4), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_181
  · decide +kernel

theorem prime_2957 : Nat.Prime 2957 := by
  apply nodeValid_prime [2, 739] ⟨2957, 2, [(2, 2), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_739
  · decide +kernel

theorem prime_3019 : Nat.Prime 3019 := by
  apply nodeValid_prime [2, 3, 503] ⟨3019, 2, [(2, 1), (3, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
  · decide +kernel

theorem prime_3557 : Nat.Prime 3557 := by
  apply nodeValid_prime [2, 7, 127] ⟨3557, 2, [(2, 2), (7, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_4153 : Nat.Prime 4153 := by
  apply nodeValid_prime [2, 3, 173] ⟨4153, 5, [(2, 3), (3, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
  · decide +kernel

theorem prime_5279 : Nat.Prime 5279 := by
  apply nodeValid_prime [2, 7, 13, 29] ⟨5279, 7, [(2, 1), (7, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_5309 : Nat.Prime 5309 := by
  apply nodeValid_prime [2, 1327] ⟨5309, 2, [(2, 2), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1327
  · decide +kernel

theorem prime_5659 : Nat.Prime 5659 := by
  apply nodeValid_prime [2, 3, 23, 41] ⟨5659, 2, [(2, 1), (3, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_5741 : Nat.Prime 5741 := by
  apply nodeValid_prime [2, 5, 7, 41] ⟨5741, 2, [(2, 2), (5, 1), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_6247 : Nat.Prime 6247 := by
  apply nodeValid_prime [2, 3, 347] ⟨6247, 5, [(2, 1), (3, 2), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
  · decide +kernel

theorem prime_7309 : Nat.Prime 7309 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨7309, 6, [(2, 2), (3, 2), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_7517 : Nat.Prime 7517 := by
  apply nodeValid_prime [2, 1879] ⟨7517, 2, [(2, 2), (1879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1879
  · decide +kernel

theorem prime_7621 : Nat.Prime 7621 := by
  apply nodeValid_prime [2, 3, 5, 127] ⟨7621, 2, [(2, 2), (3, 1), (5, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_9187 : Nat.Prime 9187 := by
  apply nodeValid_prime [2, 3, 1531] ⟨9187, 3, [(2, 1), (3, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1531
  · decide +kernel

theorem prime_9677 : Nat.Prime 9677 := by
  apply nodeValid_prime [2, 41, 59] ⟨9677, 2, [(2, 2), (41, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_59
  · decide +kernel

theorem prime_9839 : Nat.Prime 9839 := by
  apply nodeValid_prime [2, 4919] ⟨9839, 7, [(2, 1), (4919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4919
  · decide +kernel

theorem prime_10433 : Nat.Prime 10433 := by
  apply nodeValid_prime [2, 163] ⟨10433, 3, [(2, 6), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163
  · decide +kernel

theorem prime_10709 : Nat.Prime 10709 := by
  apply nodeValid_prime [2, 2677] ⟨10709, 2, [(2, 2), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2677
  · decide +kernel

theorem prime_11057 : Nat.Prime 11057 := by
  apply nodeValid_prime [2, 691] ⟨11057, 3, [(2, 4), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_691
  · decide +kernel

theorem prime_11483 : Nat.Prime 11483 := by
  apply nodeValid_prime [2, 5741] ⟨11483, 2, [(2, 1), (5741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5741
  · decide +kernel

theorem prime_11909 : Nat.Prime 11909 := by
  apply nodeValid_prime [2, 13, 229] ⟨11909, 2, [(2, 2), (13, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_229
  · decide +kernel

theorem prime_13219 : Nat.Prime 13219 := by
  apply nodeValid_prime [2, 3, 2203] ⟨13219, 3, [(2, 1), (3, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2203
  · decide +kernel

theorem prime_14683 : Nat.Prime 14683 := by
  apply nodeValid_prime [2, 3, 2447] ⟨14683, 3, [(2, 1), (3, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2447
  · decide +kernel

theorem prime_14897 : Nat.Prime 14897 := by
  apply nodeValid_prime [2, 7, 19] ⟨14897, 3, [(2, 4), (7, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_16267 : Nat.Prime 16267 := by
  apply nodeValid_prime [2, 3, 2711] ⟨16267, 3, [(2, 1), (3, 1), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2711
  · decide +kernel

theorem prime_16573 : Nat.Prime 16573 := by
  apply nodeValid_prime [2, 3, 1381] ⟨16573, 2, [(2, 2), (3, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1381
  · decide +kernel

theorem prime_19609 : Nat.Prime 19609 := by
  apply nodeValid_prime [2, 3, 19, 43] ⟨19609, 13, [(2, 3), (3, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_19753 : Nat.Prime 19753 := by
  apply nodeValid_prime [2, 3, 823] ⟨19753, 5, [(2, 3), (3, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_823
  · decide +kernel

theorem prime_21419 : Nat.Prime 21419 := by
  apply nodeValid_prime [2, 10709] ⟨21419, 2, [(2, 1), (10709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10709
  · decide +kernel

theorem prime_24071 : Nat.Prime 24071 := by
  apply nodeValid_prime [2, 5, 29, 83] ⟨24071, 11, [(2, 1), (5, 1), (29, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_83
  · decide +kernel

theorem prime_25849 : Nat.Prime 25849 := by
  apply nodeValid_prime [2, 3, 359] ⟨25849, 7, [(2, 3), (3, 2), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
  · decide +kernel

theorem prime_32309 : Nat.Prime 32309 := by
  apply nodeValid_prime [2, 41, 197] ⟨32309, 2, [(2, 2), (41, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_197
  · decide +kernel

theorem prime_35543 : Nat.Prime 35543 := by
  apply nodeValid_prime [2, 13, 1367] ⟨35543, 5, [(2, 1), (13, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1367
  · decide +kernel

theorem prime_37483 : Nat.Prime 37483 := by
  apply nodeValid_prime [2, 3, 6247] ⟨37483, 2, [(2, 1), (3, 1), (6247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6247
  · decide +kernel

theorem prime_44909 : Nat.Prime 44909 := by
  apply nodeValid_prime [2, 103, 109] ⟨44909, 2, [(2, 2), (103, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_109
  · decide +kernel

theorem prime_45667 : Nat.Prime 45667 := by
  apply nodeValid_prime [2, 3, 43, 59] ⟨45667, 2, [(2, 1), (3, 2), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_46279 : Nat.Prime 46279 := by
  apply nodeValid_prime [2, 3, 857] ⟨46279, 3, [(2, 1), (3, 3), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_857
  · decide +kernel

theorem prime_46619 : Nat.Prime 46619 := by
  apply nodeValid_prime [2, 11, 13, 163] ⟨46619, 6, [(2, 1), (11, 1), (13, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_163
  · decide +kernel

theorem prime_46819 : Nat.Prime 46819 := by
  apply nodeValid_prime [2, 3, 17] ⟨46819, 2, [(2, 1), (3, 4), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_50723 : Nat.Prime 50723 := by
  apply nodeValid_prime [2, 7, 3623] ⟨50723, 2, [(2, 1), (7, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3623
  · decide +kernel

theorem prime_52529 : Nat.Prime 52529 := by
  apply nodeValid_prime [2, 7, 67] ⟨52529, 3, [(2, 4), (7, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_52999 : Nat.Prime 52999 := by
  apply nodeValid_prime [2, 3, 11, 73] ⟨52999, 3, [(2, 1), (3, 1), (11, 2), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_54181 : Nat.Prime 54181 := by
  apply nodeValid_prime [2, 3, 5, 7, 43] ⟨54181, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_55201 : Nat.Prime 55201 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨55201, 7, [(2, 5), (3, 1), (5, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_58733 : Nat.Prime 58733 := by
  apply nodeValid_prime [2, 14683] ⟨58733, 2, [(2, 2), (14683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14683
  · decide +kernel

theorem prime_66343 : Nat.Prime 66343 := by
  apply nodeValid_prime [2, 3, 11057] ⟨66343, 5, [(2, 1), (3, 1), (11057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11057
  · decide +kernel

theorem prime_68899 : Nat.Prime 68899 := by
  apply nodeValid_prime [2, 3, 11483] ⟨68899, 2, [(2, 1), (3, 1), (11483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11483
  · decide +kernel

theorem prime_75941 : Nat.Prime 75941 := by
  apply nodeValid_prime [2, 5, 3797] ⟨75941, 2, [(2, 2), (5, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3797
  · decide +kernel

theorem prime_85691 : Nat.Prime 85691 := by
  apply nodeValid_prime [2, 5, 11, 19, 41] ⟨85691, 2, [(2, 1), (5, 1), (11, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_93239 : Nat.Prime 93239 := by
  apply nodeValid_prime [2, 46619] ⟨93239, 11, [(2, 1), (46619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46619
  · decide +kernel

theorem prime_106181 : Nat.Prime 106181 := by
  apply nodeValid_prime [2, 5, 5309] ⟨106181, 2, [(2, 2), (5, 1), (5309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5309
  · decide +kernel

theorem prime_120091 : Nat.Prime 120091 := by
  apply nodeValid_prime [2, 3, 5, 4003] ⟨120091, 3, [(2, 1), (3, 1), (5, 1), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4003
  · decide +kernel

theorem prime_125197 : Nat.Prime 125197 := by
  apply nodeValid_prime [2, 3, 10433] ⟨125197, 2, [(2, 2), (3, 1), (10433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10433
  · decide +kernel

theorem prime_133121 : Nat.Prime 133121 := by
  apply nodeValid_prime [2, 5, 13] ⟨133121, 3, [(2, 11), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_141773 : Nat.Prime 141773 := by
  apply nodeValid_prime [2, 23, 67] ⟨141773, 2, [(2, 2), (23, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_151883 : Nat.Prime 151883 := by
  apply nodeValid_prime [2, 75941] ⟨151883, 2, [(2, 1), (75941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_75941
  · decide +kernel

theorem prime_157991 : Nat.Prime 157991 := by
  apply nodeValid_prime [2, 5, 7, 37, 61] ⟨157991, 11, [(2, 1), (5, 1), (7, 1), (37, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_61
  · decide +kernel

theorem prime_193541 : Nat.Prime 193541 := by
  apply nodeValid_prime [2, 5, 9677] ⟨193541, 2, [(2, 2), (5, 1), (9677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9677
  · decide +kernel

theorem prime_202757 : Nat.Prime 202757 := by
  apply nodeValid_prime [2, 173, 293] ⟨202757, 2, [(2, 2), (173, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_293
  · decide +kernel

theorem prime_205759 : Nat.Prime 205759 := by
  apply nodeValid_prime [2, 3, 7, 23, 71] ⟨205759, 11, [(2, 1), (3, 2), (7, 1), (23, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_71
  · decide +kernel

theorem prime_209353 : Nat.Prime 209353 := by
  apply nodeValid_prime [2, 3, 11, 13, 61] ⟨209353, 30, [(2, 3), (3, 1), (11, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_236713 : Nat.Prime 236713 := by
  apply nodeValid_prime [2, 3, 7, 1409] ⟨236713, 5, [(2, 3), (3, 1), (7, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1409
  · decide +kernel

theorem prime_303767 : Nat.Prime 303767 := by
  apply nodeValid_prime [2, 151883] ⟨303767, 5, [(2, 1), (151883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_151883
  · decide +kernel

theorem prime_309713 : Nat.Prime 309713 := by
  apply nodeValid_prime [2, 13, 1489] ⟨309713, 3, [(2, 4), (13, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1489
  · decide +kernel

theorem prime_577909 : Nat.Prime 577909 := by
  apply nodeValid_prime [2, 3, 5351] ⟨577909, 2, [(2, 2), (3, 3), (5351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5351
  · decide +kernel

theorem prime_671093 : Nat.Prime 671093 := by
  apply nodeValid_prime [2, 17, 71, 139] ⟨671093, 3, [(2, 2), (17, 1), (71, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_139
  · decide +kernel

theorem prime_704797 : Nat.Prime 704797 := by
  apply nodeValid_prime [2, 3, 58733] ⟨704797, 2, [(2, 2), (3, 1), (58733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58733
  · decide +kernel

theorem prime_795149 : Nat.Prime 795149 := by
  apply nodeValid_prime [2, 137, 1451] ⟨795149, 2, [(2, 2), (137, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_1451
  · decide +kernel

theorem prime_799859 : Nat.Prime 799859 := by
  apply nodeValid_prime [2, 439, 911] ⟨799859, 2, [(2, 1), (439, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_439
    · exact prime_911
  · decide +kernel

theorem prime_808363 : Nat.Prime 808363 := by
  apply nodeValid_prime [2, 3, 44909] ⟨808363, 2, [(2, 1), (3, 2), (44909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44909
  · decide +kernel

theorem prime_853091 : Nat.Prime 853091 := by
  apply nodeValid_prime [2, 5, 7, 1741] ⟨853091, 2, [(2, 1), (5, 1), (7, 2), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1741
  · decide +kernel

theorem prime_1060091 : Nat.Prime 1060091 := by
  apply nodeValid_prime [2, 5, 227, 467] ⟨1060091, 2, [(2, 1), (5, 1), (227, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
    · exact prime_467
  · decide +kernel

theorem prime_1084103 : Nat.Prime 1084103 := by
  apply nodeValid_prime [2, 19, 47, 607] ⟨1084103, 10, [(2, 1), (19, 1), (47, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_607
  · decide +kernel

theorem prime_1118869 : Nat.Prime 1118869 := by
  apply nodeValid_prime [2, 3, 93239] ⟨1118869, 6, [(2, 2), (3, 1), (93239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_93239
  · decide +kernel

theorem prime_1286269 : Nat.Prime 1286269 := by
  apply nodeValid_prime [2, 3, 37, 2897] ⟨1286269, 2, [(2, 2), (3, 1), (37, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2897
  · decide +kernel

theorem prime_1511047 : Nat.Prime 1511047 := by
  apply nodeValid_prime [2, 3, 127, 661] ⟨1511047, 3, [(2, 1), (3, 2), (127, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_661
  · decide +kernel

theorem prime_1858279 : Nat.Prime 1858279 := by
  apply nodeValid_prime [2, 3, 309713] ⟨1858279, 3, [(2, 1), (3, 1), (309713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_309713
  · decide +kernel

theorem prime_1921457 : Nat.Prime 1921457 := by
  apply nodeValid_prime [2, 120091] ⟨1921457, 3, [(2, 4), (120091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120091
  · decide +kernel

theorem prime_2240629 : Nat.Prime 2240629 := by
  apply nodeValid_prime [2, 3, 13, 53, 271] ⟨2240629, 2, [(2, 2), (3, 1), (13, 1), (53, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_271
  · decide +kernel

theorem prime_2806283 : Nat.Prime 2806283 := by
  apply nodeValid_prime [2, 131, 10711] ⟨2806283, 2, [(2, 1), (131, 1), (10711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_10711
  · decide +kernel

theorem prime_3020119 : Nat.Prime 3020119 := by
  apply nodeValid_prime [2, 3, 17, 29, 1021] ⟨3020119, 3, [(2, 1), (3, 1), (17, 1), (29, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_1021
  · decide +kernel

theorem prime_3585443 : Nat.Prime 3585443 := by
  apply nodeValid_prime [2, 7, 47, 5449] ⟨3585443, 5, [(2, 1), (7, 1), (47, 1), (5449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_5449
  · decide +kernel

theorem prime_3798877 : Nat.Prime 3798877 := by
  apply nodeValid_prime [2, 3, 89, 3557] ⟨3798877, 2, [(2, 2), (3, 1), (89, 1), (3557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_3557
  · decide +kernel

theorem prime_4438151 : Nat.Prime 4438151 := by
  apply nodeValid_prime [2, 5, 37, 2399] ⟨4438151, 7, [(2, 1), (5, 2), (37, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_2399
  · decide +kernel

theorem prime_4840949 : Nat.Prime 4840949 := by
  apply nodeValid_prime [2, 7, 23, 7517] ⟨4840949, 2, [(2, 2), (7, 1), (23, 1), (7517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_7517
  · decide +kernel

theorem prime_5216797 : Nat.Prime 5216797 := by
  apply nodeValid_prime [2, 3, 13, 71, 157] ⟨5216797, 2, [(2, 2), (3, 2), (13, 1), (71, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_157
  · decide +kernel

theorem prime_5284171 : Nat.Prime 5284171 := by
  apply nodeValid_prime [2, 3, 5, 19571] ⟨5284171, 15, [(2, 1), (3, 3), (5, 1), (19571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19571
  · decide +kernel

theorem prime_5374123 : Nat.Prime 5374123 := by
  apply nodeValid_prime [2, 3, 13, 68899] ⟨5374123, 2, [(2, 1), (3, 1), (13, 1), (68899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_68899
  · decide +kernel

theorem prime_6044189 : Nat.Prime 6044189 := by
  apply nodeValid_prime [2, 1511047] ⟨6044189, 2, [(2, 2), (1511047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1511047
  · decide +kernel

theorem prime_7170887 : Nat.Prime 7170887 := by
  apply nodeValid_prime [2, 3585443] ⟨7170887, 5, [(2, 1), (3585443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3585443
  · decide +kernel

theorem prime_9114197 : Nat.Prime 9114197 := by
  apply nodeValid_prime [2, 7, 13, 73] ⟨9114197, 2, [(2, 2), (7, 4), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_11908933 : Nat.Prime 11908933 := by
  apply nodeValid_prime [2, 3, 7, 141773] ⟨11908933, 5, [(2, 2), (3, 1), (7, 1), (141773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_141773
  · decide +kernel

theorem prime_12062513 : Nat.Prime 12062513 := by
  apply nodeValid_prime [2, 7, 11, 9791] ⟨12062513, 6, [(2, 4), (7, 1), (11, 1), (9791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_9791
  · decide +kernel

theorem prime_12088379 : Nat.Prime 12088379 := by
  apply nodeValid_prime [2, 6044189] ⟨12088379, 2, [(2, 1), (6044189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6044189
  · decide +kernel

theorem prime_14282311 : Nat.Prime 14282311 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 2957] ⟨14282311, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_2957
  · decide +kernel

theorem prime_15883291 : Nat.Prime 15883291 := by
  apply nodeValid_prime [2, 3, 5, 19609] ⟨15883291, 3, [(2, 1), (3, 4), (5, 1), (19609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19609
  · decide +kernel

theorem prime_20450263 : Nat.Prime 20450263 := by
  apply nodeValid_prime [2, 3, 7, 53, 9187] ⟨20450263, 5, [(2, 1), (3, 1), (7, 1), (53, 1), (9187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_9187
  · decide +kernel

theorem prime_22406291 : Nat.Prime 22406291 := by
  apply nodeValid_prime [2, 5, 2240629] ⟨22406291, 2, [(2, 1), (5, 1), (2240629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2240629
  · decide +kernel

theorem prime_27219791 : Nat.Prime 27219791 := by
  apply nodeValid_prime [2, 5, 13, 37, 5659] ⟨27219791, 11, [(2, 1), (5, 1), (13, 1), (37, 1), (5659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_5659
  · decide +kernel

theorem prime_30050297 : Nat.Prime 30050297 := by
  apply nodeValid_prime [2, 47, 229, 349] ⟨30050297, 3, [(2, 3), (47, 1), (229, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_229
    · exact prime_349
  · decide +kernel

theorem prime_39373699 : Nat.Prime 39373699 := by
  apply nodeValid_prime [2, 3, 7, 13, 37, 1949] ⟨39373699, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (37, 1), (1949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_1949
  · decide +kernel

theorem prime_44789473 : Nat.Prime 44789473 := by
  apply nodeValid_prime [2, 3, 7, 13, 1709] ⟨44789473, 5, [(2, 5), (3, 2), (7, 1), (13, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1709
  · decide +kernel

theorem prime_47635733 : Nat.Prime 47635733 := by
  apply nodeValid_prime [2, 11908933] ⟨47635733, 2, [(2, 2), (11908933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11908933
  · decide +kernel

theorem prime_57643711 : Nat.Prime 57643711 := by
  apply nodeValid_prime [2, 3, 5, 1921457] ⟨57643711, 13, [(2, 1), (3, 1), (5, 1), (1921457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1921457
  · decide +kernel

theorem prime_64720301 : Nat.Prime 64720301 := by
  apply nodeValid_prime [2, 5, 499, 1297] ⟨64720301, 2, [(2, 2), (5, 2), (499, 1), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_499
    · exact prime_1297
  · decide +kernel

theorem prime_92611369 : Nat.Prime 92611369 := by
  apply nodeValid_prime [2, 3, 1286269] ⟨92611369, 13, [(2, 3), (3, 2), (1286269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1286269
  · decide +kernel

theorem prime_103662497 : Nat.Prime 103662497 := by
  apply nodeValid_prime [2, 7, 103, 4493] ⟨103662497, 3, [(2, 5), (7, 1), (103, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_103
    · exact prime_4493
  · decide +kernel

theorem prime_148550081 : Nat.Prime 148550081 := by
  apply nodeValid_prime [2, 5, 7, 17, 47, 83] ⟨148550081, 3, [(2, 6), (5, 1), (7, 1), (17, 1), (47, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_47
    · exact prime_83
  · decide +kernel

theorem prime_166437793 : Nat.Prime 166437793 := by
  apply nodeValid_prime [2, 3, 577909] ⟨166437793, 5, [(2, 5), (3, 2), (577909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577909
  · decide +kernel

theorem prime_171931021 : Nat.Prime 171931021 := by
  apply nodeValid_prime [2, 3, 5, 523, 5479] ⟨171931021, 7, [(2, 2), (3, 1), (5, 1), (523, 1), (5479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_523
    · exact prime_5479
  · decide +kernel

theorem prime_255518831 : Nat.Prime 255518831 := by
  apply nodeValid_prime [2, 5, 7, 53, 9839] ⟨255518831, 7, [(2, 1), (5, 1), (7, 2), (53, 1), (9839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_9839
  · decide +kernel

theorem prime_257312641 : Nat.Prime 257312641 := by
  apply nodeValid_prime [2, 3, 5, 13, 61] ⟨257312641, 7, [(2, 7), (3, 1), (5, 1), (13, 3), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_283229059 : Nat.Prime 283229059 := by
  apply nodeValid_prime [2, 3, 7, 2377, 2837] ⟨283229059, 2, [(2, 1), (3, 1), (7, 1), (2377, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2377
    · exact prime_2837
  · decide +kernel

theorem prime_406068731 : Nat.Prime 406068731 := by
  apply nodeValid_prime [2, 5, 29, 89, 15733] ⟨406068731, 6, [(2, 1), (5, 1), (29, 1), (89, 1), (15733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_89
    · exact prime_15733
  · decide +kernel

theorem prime_445313503 : Nat.Prime 445313503 := by
  apply nodeValid_prime [2, 3, 29, 853091] ⟨445313503, 5, [(2, 1), (3, 2), (29, 1), (853091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_853091
  · decide +kernel

theorem prime_483141317 : Nat.Prime 483141317 := by
  apply nodeValid_prime [2, 7, 673, 25639] ⟨483141317, 2, [(2, 2), (7, 1), (673, 1), (25639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_673
    · exact prime_25639
  · decide +kernel

theorem prime_563414077 : Nat.Prime 563414077 := by
  apply nodeValid_prime [2, 3, 5216797] ⟨563414077, 5, [(2, 2), (3, 3), (5216797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5216797
  · decide +kernel

theorem prime_834976157 : Nat.Prime 834976157 := by
  apply nodeValid_prime [2, 7, 839, 35543] ⟨834976157, 2, [(2, 2), (7, 1), (839, 1), (35543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_839
    · exact prime_35543
  · decide +kernel

theorem prime_1298730569 : Nat.Prime 1298730569 := by
  apply nodeValid_prime [2, 2447, 66343] ⟨1298730569, 3, [(2, 3), (2447, 1), (66343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2447
    · exact prime_66343
  · decide +kernel

theorem prime_1450245557 : Nat.Prime 1450245557 := by
  apply nodeValid_prime [2, 163, 443, 5021] ⟨1450245557, 2, [(2, 2), (163, 1), (443, 1), (5021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_443
    · exact prime_5021
  · decide +kernel

theorem prime_3356182463 : Nat.Prime 3356182463 := by
  apply nodeValid_prime [2, 25849, 64919] ⟨3356182463, 5, [(2, 1), (25849, 1), (64919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_25849
    · exact prime_64919
  · decide +kernel

theorem prime_3480932177 : Nat.Prime 3480932177 := by
  apply nodeValid_prime [2, 29, 37, 202757] ⟨3480932177, 3, [(2, 4), (29, 1), (37, 1), (202757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_202757
  · decide +kernel

theorem prime_5880857803 : Nat.Prime 5880857803 := by
  apply nodeValid_prime [2, 3, 79, 331, 37483] ⟨5880857803, 2, [(2, 1), (3, 1), (79, 1), (331, 1), (37483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_331
    · exact prime_37483
  · decide +kernel

theorem prime_6670982221 : Nat.Prime 6670982221 := by
  apply nodeValid_prime [2, 3, 5, 7, 15883291] ⟨6670982221, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (15883291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_15883291
  · decide +kernel

theorem prime_6712364927 : Nat.Prime 6712364927 := by
  apply nodeValid_prime [2, 3356182463] ⟨6712364927, 5, [(2, 1), (3356182463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3356182463
  · decide +kernel

theorem prime_8171521913 : Nat.Prime 8171521913 := by
  apply nodeValid_prime [2, 211, 4840949] ⟨8171521913, 3, [(2, 3), (211, 1), (4840949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_4840949
  · decide +kernel

theorem prime_17189375543 : Nat.Prime 17189375543 := by
  apply nodeValid_prime [2, 23, 41, 9114197] ⟨17189375543, 5, [(2, 1), (23, 1), (41, 1), (9114197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_41
    · exact prime_9114197
  · decide +kernel

theorem prime_20303436551 : Nat.Prime 20303436551 := by
  apply nodeValid_prime [2, 5, 406068731] ⟨20303436551, 13, [(2, 1), (5, 2), (406068731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_406068731
  · decide +kernel

theorem prime_39532408117 : Nat.Prime 39532408117 := by
  apply nodeValid_prime [2, 3, 41, 1483, 54181] ⟨39532408117, 2, [(2, 2), (3, 1), (41, 1), (1483, 1), (54181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1483
    · exact prime_54181
  · decide +kernel

theorem prime_40108543367 : Nat.Prime 40108543367 := by
  apply nodeValid_prime [2, 5279, 3798877] ⟨40108543367, 5, [(2, 1), (5279, 1), (3798877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5279
    · exact prime_3798877
  · decide +kernel

theorem prime_40274189563 : Nat.Prime 40274189563 := by
  apply nodeValid_prime [2, 3, 6712364927] ⟨40274189563, 2, [(2, 1), (3, 1), (6712364927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6712364927
  · decide +kernel

theorem prime_40606873103 : Nat.Prime 40606873103 := by
  apply nodeValid_prime [2, 20303436551] ⟨40606873103, 5, [(2, 1), (20303436551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20303436551
  · decide +kernel

theorem prime_117617156099 : Nat.Prime 117617156099 := by
  apply nodeValid_prime [2, 13, 101, 44789473] ⟨117617156099, 2, [(2, 1), (13, 1), (101, 1), (44789473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_101
    · exact prime_44789473
  · decide +kernel

theorem prime_117861660461 : Nat.Prime 117861660461 := by
  apply nodeValid_prime [2, 5, 23, 229, 1118869] ⟨117861660461, 3, [(2, 2), (5, 1), (23, 1), (229, 1), (1118869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_229
    · exact prime_1118869
  · decide +kernel

theorem prime_118106517233 : Nat.Prime 118106517233 := by
  apply nodeValid_prime [2, 11, 619, 1084103] ⟨118106517233, 3, [(2, 4), (11, 1), (619, 1), (1084103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_619
    · exact prime_1084103
  · decide +kernel

theorem prime_121320900881 : Nat.Prime 121320900881 := by
  apply nodeValid_prime [2, 5, 12113, 125197] ⟨121320900881, 3, [(2, 4), (5, 1), (12113, 1), (125197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12113
    · exact prime_125197
  · decide +kernel

theorem prime_122321751833 : Nat.Prime 122321751833 := by
  apply nodeValid_prime [2, 7, 653, 1367, 2447] ⟨122321751833, 3, [(2, 3), (7, 1), (653, 1), (1367, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_653
    · exact prime_1367
    · exact prime_2447
  · decide +kernel

theorem prime_233771496727 : Nat.Prime 233771496727 := by
  apply nodeValid_prime [2, 3, 29, 4871, 9511] ⟨233771496727, 5, [(2, 1), (3, 1), (29, 2), (4871, 1), (9511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_4871
    · exact prime_9511
  · decide +kernel

theorem prime_233771501941 : Nat.Prime 233771501941 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 12062513] ⟨233771501941, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (19, 1), (12062513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_12062513
  · decide +kernel

theorem prime_233771502421 : Nat.Prime 233771502421 := by
  apply nodeValid_prime [2, 3, 5, 1298730569] ⟨233771502421, 6, [(2, 2), (3, 2), (5, 1), (1298730569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1298730569
  · decide +kernel

theorem prime_234258423577 : Nat.Prime 234258423577 := by
  apply nodeValid_prime [2, 3, 643, 1019, 14897] ⟨234258423577, 7, [(2, 3), (3, 1), (643, 1), (1019, 1), (14897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_643
    · exact prime_1019
    · exact prime_14897
  · decide +kernel

theorem prime_234258433459 : Nat.Prime 234258433459 := by
  apply nodeValid_prime [2, 3, 7, 52529, 106181] ⟨234258433459, 3, [(2, 1), (3, 1), (7, 1), (52529, 1), (106181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_52529
    · exact prime_106181
  · decide +kernel

theorem prime_234258433511 : Nat.Prime 234258433511 := by
  apply nodeValid_prime [2, 5, 67, 521, 671093] ⟨234258433511, 7, [(2, 1), (5, 1), (67, 1), (521, 1), (671093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_521
    · exact prime_671093
  · decide +kernel

theorem prime_234745993439 : Nat.Prime 234745993439 := by
  apply nodeValid_prime [2, 11, 271, 39373699] ⟨234745993439, 17, [(2, 1), (11, 1), (271, 1), (39373699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_271
    · exact prime_39373699
  · decide +kernel

theorem prime_234745995377 : Nat.Prime 234745995377 := by
  apply nodeValid_prime [2, 97, 101, 797, 1879] ⟨234745995377, 3, [(2, 4), (97, 1), (101, 1), (797, 1), (1879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_101
    · exact prime_797
    · exact prime_1879
  · decide +kernel

theorem prime_234746032747 : Nat.Prime 234746032747 := by
  apply nodeValid_prime [2, 3, 101, 7309, 52999] ⟨234746032747, 2, [(2, 1), (3, 1), (101, 1), (7309, 1), (52999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_7309
    · exact prime_52999
  · decide +kernel

theorem prime_235234312121 : Nat.Prime 235234312121 := by
  apply nodeValid_prime [2, 5, 5880857803] ⟨235234312121, 3, [(2, 3), (5, 1), (5880857803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5880857803
  · decide +kernel

theorem prime_235234312199 : Nat.Prime 235234312199 := by
  apply nodeValid_prime [2, 117617156099] ⟨235234312199, 17, [(2, 1), (117617156099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117617156099
  · decide +kernel

theorem prime_235234328921 : Nat.Prime 235234328921 := by
  apply nodeValid_prime [2, 5, 24071, 244313] ⟨235234328921, 6, [(2, 3), (5, 1), (24071, 1), (244313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_24071
    · exact prime_244313
  · decide +kernel

theorem prime_235723320923 : Nat.Prime 235723320923 := by
  apply nodeValid_prime [2, 117861660461] ⟨235723320923, 2, [(2, 1), (117861660461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117861660461
  · decide +kernel

theorem prime_235723390061 : Nat.Prime 235723390061 := by
  apply nodeValid_prime [2, 5, 433, 27219791] ⟨235723390061, 2, [(2, 2), (5, 1), (433, 1), (27219791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_433
    · exact prime_27219791
  · decide +kernel

theorem prime_235723390501 : Nat.Prime 235723390501 := by
  apply nodeValid_prime [2, 3, 5, 13, 12088379] ⟨235723390501, 6, [(2, 2), (3, 1), (5, 3), (13, 1), (12088379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_12088379
  · decide +kernel

theorem prime_236213004439 : Nat.Prime 236213004439 := by
  apply nodeValid_prime [2, 3, 17, 257312641] ⟨236213004439, 6, [(2, 1), (3, 3), (17, 1), (257312641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_257312641
  · decide +kernel

theorem prime_236213034467 : Nat.Prime 236213034467 := by
  apply nodeValid_prime [2, 118106517233] ⟨236213034467, 2, [(2, 1), (118106517233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_118106517233
  · decide +kernel

theorem prime_236213035207 : Nat.Prime 236213035207 := by
  apply nodeValid_prime [2, 3, 139, 283229059] ⟨236213035207, 3, [(2, 1), (3, 1), (139, 1), (283229059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_283229059
  · decide +kernel

theorem prime_236703380129 : Nat.Prime 236703380129 := by
  apply nodeValid_prime [2, 46819, 157991] ⟨236703380129, 3, [(2, 5), (46819, 1), (157991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_46819
    · exact prime_157991
  · decide +kernel

theorem prime_236703386417 : Nat.Prime 236703386417 := by
  apply nodeValid_prime [2, 7, 45667, 46279] ⟨236703386417, 5, [(2, 4), (7, 1), (45667, 1), (46279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_45667
    · exact prime_46279
  · decide +kernel

theorem prime_236703388037 : Nat.Prime 236703388037 := by
  apply nodeValid_prime [2, 17, 3480932177] ⟨236703388037, 2, [(2, 2), (17, 1), (3480932177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3480932177
  · decide +kernel

theorem prime_237194448119 : Nat.Prime 237194448119 := by
  apply nodeValid_prime [2, 19, 3359, 1858279] ⟨237194448119, 13, [(2, 1), (19, 1), (3359, 1), (1858279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3359
    · exact prime_1858279
  · decide +kernel

theorem prime_237194448503 : Nat.Prime 237194448503 := by
  apply nodeValid_prime [2, 11, 61, 859, 205759] ⟨237194448503, 5, [(2, 1), (11, 1), (61, 1), (859, 1), (205759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_859
    · exact prime_205759
  · decide +kernel

theorem prime_237194448703 : Nat.Prime 237194448703 := by
  apply nodeValid_prime [2, 3, 39532408117] ⟨237194448703, 11, [(2, 1), (3, 1), (39532408117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39532408117
  · decide +kernel

theorem prime_237686206343 : Nat.Prime 237686206343 := by
  apply nodeValid_prime [2, 13, 43, 263, 808363] ⟨237686206343, 5, [(2, 1), (13, 1), (43, 1), (263, 1), (808363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_263
    · exact prime_808363
  · decide +kernel

theorem prime_237686219663 : Nat.Prime 237686219663 := by
  apply nodeValid_prime [2, 53, 157, 14282311] ⟨237686219663, 5, [(2, 1), (53, 1), (157, 1), (14282311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_157
    · exact prime_14282311
  · decide +kernel

theorem prime_237686220503 : Nat.Prime 237686220503 := by
  apply nodeValid_prime [2, 16573, 7170887] ⟨237686220503, 5, [(2, 1), (16573, 1), (7170887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16573
    · exact prime_7170887
  · decide +kernel

theorem prime_238178654023 : Nat.Prime 238178654023 := by
  apply nodeValid_prime [2, 3, 1321, 30050297] ⟨238178654023, 3, [(2, 1), (3, 1), (1321, 1), (30050297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1321
    · exact prime_30050297
  · decide +kernel

theorem prime_238178664817 : Nat.Prime 238178664817 := by
  apply nodeValid_prime [2, 3, 31, 53, 3020119] ⟨238178664817, 10, [(2, 4), (3, 1), (31, 1), (53, 1), (3020119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
    · exact prime_3020119
  · decide +kernel

theorem prime_238178665001 : Nat.Prime 238178665001 := by
  apply nodeValid_prime [2, 5, 47635733] ⟨238178665001, 3, [(2, 3), (5, 4), (47635733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47635733
  · decide +kernel

theorem prime_238671795163 : Nat.Prime 238671795163 := by
  apply nodeValid_prime [2, 3, 239, 166437793] ⟨238671795163, 3, [(2, 1), (3, 1), (239, 1), (166437793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_166437793
  · decide +kernel

theorem prime_238671810599 : Nat.Prime 238671810599 := by
  apply nodeValid_prime [2, 13, 19, 483141317] ⟨238671810599, 19, [(2, 1), (13, 1), (19, 1), (483141317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_483141317
  · decide +kernel

theorem prime_238671811733 : Nat.Prime 238671811733 := by
  apply nodeValid_prime [2, 2663, 22406291] ⟨238671811733, 2, [(2, 2), (2663, 1), (22406291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2663
    · exact prime_22406291
  · decide +kernel

theorem prime_239165625817 : Nat.Prime 239165625817 := by
  apply nodeValid_prime [2, 3, 13, 255518831] ⟨239165625817, 5, [(2, 3), (3, 2), (13, 1), (255518831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_255518831
  · decide +kernel

theorem prime_239165630227 : Nat.Prime 239165630227 := by
  apply nodeValid_prime [2, 3, 23, 113, 1231, 4153] ⟨239165630227, 14, [(2, 1), (3, 2), (23, 1), (113, 1), (1231, 1), (4153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_113
    · exact prime_1231
    · exact prime_4153
  · decide +kernel

theorem prime_239165630411 : Nat.Prime 239165630411 := by
  apply nodeValid_prime [2, 5, 7, 23, 148550081] ⟨239165630411, 6, [(2, 1), (5, 1), (7, 1), (23, 1), (148550081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_148550081
  · decide +kernel

theorem prime_239660149369 : Nat.Prime 239660149369 := by
  apply nodeValid_prime [2, 3, 19, 16267, 32309] ⟨239660149369, 23, [(2, 3), (3, 1), (19, 1), (16267, 1), (32309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_16267
    · exact prime_32309
  · decide +kernel

theorem prime_239660152453 : Nat.Prime 239660152453 := by
  apply nodeValid_prime [2, 3, 7, 29, 41, 799859] ⟨239660152453, 5, [(2, 2), (3, 2), (7, 1), (29, 1), (41, 1), (799859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_41
    · exact prime_799859
  · decide +kernel

theorem prime_239660154001 : Nat.Prime 239660154001 := by
  apply nodeValid_prime [2, 3, 5, 4438151] ⟨239660154001, 13, [(2, 4), (3, 3), (5, 3), (4438151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4438151
  · decide +kernel

theorem prime_240155347613 : Nat.Prime 240155347613 := by
  apply nodeValid_prime [2, 43, 27527, 50723] ⟨240155347613, 3, [(2, 2), (43, 1), (27527, 1), (50723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_27527
    · exact prime_50723
  · decide +kernel

theorem prime_240155349851 : Nat.Prime 240155349851 := by
  apply nodeValid_prime [2, 5, 13, 23, 83, 193541] ⟨240155349851, 2, [(2, 1), (5, 2), (13, 1), (23, 1), (83, 1), (193541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_83
    · exact prime_193541
  · decide +kernel

theorem prime_240155359957 : Nat.Prime 240155359957 := by
  apply nodeValid_prime [2, 3, 6670982221] ⟨240155359957, 5, [(2, 2), (3, 2), (6670982221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6670982221
  · decide +kernel

theorem prime_240651257603 : Nat.Prime 240651257603 := by
  apply nodeValid_prime [2, 7, 17189375543] ⟨240651257603, 2, [(2, 1), (7, 1), (17189375543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17189375543
  · decide +kernel

theorem prime_240651257911 : Nat.Prime 240651257911 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 47, 1060091] ⟨240651257911, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (47, 1), (1060091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_47
    · exact prime_1060091
  · decide +kernel

theorem prime_240651260203 : Nat.Prime 240651260203 := by
  apply nodeValid_prime [2, 3, 40108543367] ⟨240651260203, 3, [(2, 1), (3, 1), (40108543367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40108543367
  · decide +kernel

theorem prime_241147841527 : Nat.Prime 241147841527 := by
  apply nodeValid_prime [2, 3, 23, 64720301] ⟨241147841527, 3, [(2, 1), (3, 4), (23, 1), (64720301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_64720301
  · decide +kernel

theorem prime_241147841797 : Nat.Prime 241147841797 := by
  apply nodeValid_prime [2, 3, 71, 367, 85691] ⟨241147841797, 2, [(2, 2), (3, 3), (71, 1), (367, 1), (85691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_367
    · exact prime_85691
  · decide +kernel

theorem prime_241147849963 : Nat.Prime 241147849963 := by
  apply nodeValid_prime [2, 3, 31, 43, 61, 281, 1759] ⟨241147849963, 2, [(2, 1), (3, 1), (31, 1), (43, 1), (61, 1), (281, 1), (1759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
    · exact prime_61
    · exact prime_281
    · exact prime_1759
  · decide +kernel

theorem prime_241645137379 : Nat.Prime 241645137379 := by
  apply nodeValid_prime [2, 3, 40274189563] ⟨241645137379, 3, [(2, 1), (3, 1), (40274189563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40274189563
  · decide +kernel

theorem prime_241645137551 : Nat.Prime 241645137551 := by
  apply nodeValid_prime [2, 5, 29, 3019, 55201] ⟨241645137551, 11, [(2, 1), (5, 2), (29, 1), (3019, 1), (55201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3019
    · exact prime_55201
  · decide +kernel

theorem prime_241645139831 : Nat.Prime 241645139831 := by
  apply nodeValid_prime [2, 5, 17, 269, 5284171] ⟨241645139831, 7, [(2, 1), (5, 1), (17, 1), (269, 1), (5284171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_269
    · exact prime_5284171
  · decide +kernel

theorem prime_242143085531 : Nat.Prime 242143085531 := by
  apply nodeValid_prime [2, 5, 29, 834976157] ⟨242143085531, 2, [(2, 1), (5, 1), (29, 1), (834976157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_834976157
  · decide +kernel

theorem prime_242143122979 : Nat.Prime 242143122979 := by
  apply nodeValid_prime [2, 3, 21419, 209353] ⟨242143122979, 2, [(2, 1), (3, 3), (21419, 1), (209353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21419
    · exact prime_209353
  · decide +kernel

theorem prime_242641786781 : Nat.Prime 242641786781 := by
  apply nodeValid_prime [2, 5, 131, 92611369] ⟨242641786781, 2, [(2, 2), (5, 1), (131, 1), (92611369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_92611369
  · decide +kernel

theorem prime_242641789193 : Nat.Prime 242641789193 := by
  apply nodeValid_prime [2, 11, 29, 313, 303767] ⟨242641789193, 3, [(2, 3), (11, 1), (29, 1), (313, 1), (303767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_313
    · exact prime_303767
  · decide +kernel

theorem prime_242641801763 : Nat.Prime 242641801763 := by
  apply nodeValid_prime [2, 121320900881] ⟨242641801763, 2, [(2, 1), (121320900881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_121320900881
  · decide +kernel

theorem prime_243141172639 : Nat.Prime 243141172639 := by
  apply nodeValid_prime [2, 3, 7, 13, 445313503] ⟨243141172639, 12, [(2, 1), (3, 1), (7, 1), (13, 1), (445313503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_445313503
  · decide +kernel

theorem prime_243141172999 : Nat.Prime 243141172999 := by
  apply nodeValid_prime [2, 3, 19, 37, 57643711] ⟨243141172999, 3, [(2, 1), (3, 1), (19, 1), (37, 1), (57643711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_57643711
  · decide +kernel

theorem prime_243141178229 : Nat.Prime 243141178229 := by
  apply nodeValid_prime [2, 13, 19753, 236713] ⟨243141178229, 2, [(2, 2), (13, 1), (19753, 1), (236713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19753
    · exact prime_236713
  · decide +kernel

theorem prime_243641238619 : Nat.Prime 243641238619 := by
  apply nodeValid_prime [2, 3, 40606873103] ⟨243641238619, 2, [(2, 1), (3, 1), (40606873103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40606873103
  · decide +kernel

theorem prime_243641240329 : Nat.Prime 243641240329 := by
  apply nodeValid_prime [2, 3, 1889, 5374123] ⟨243641240329, 13, [(2, 3), (3, 1), (1889, 1), (5374123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1889
    · exact prime_5374123
  · decide +kernel

theorem prime_243641253577 : Nat.Prime 243641253577 := by
  apply nodeValid_prime [2, 3, 7, 1450245557] ⟨243641253577, 5, [(2, 3), (3, 1), (7, 1), (1450245557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1450245557
  · decide +kernel

theorem prime_244142028257 : Nat.Prime 244142028257 := by
  apply nodeValid_prime [2, 7, 41, 2011, 13219] ⟨244142028257, 3, [(2, 5), (7, 1), (41, 1), (2011, 1), (13219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_2011
    · exact prime_13219
  · decide +kernel

theorem prime_244142049821 : Nat.Prime 244142049821 := by
  apply nodeValid_prime [2, 5, 71, 171931021] ⟨244142049821, 2, [(2, 2), (5, 1), (71, 1), (171931021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_171931021
  · decide +kernel

theorem prime_244142050307 : Nat.Prime 244142050307 := by
  apply nodeValid_prime [2, 7, 11, 11909, 133121] ⟨244142050307, 2, [(2, 1), (7, 1), (11, 1), (11909, 1), (133121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_11909
    · exact prime_133121
  · decide +kernel

theorem prime_244643492831 : Nat.Prime 244643492831 := by
  apply nodeValid_prime [2, 5, 11, 2797, 795149] ⟨244643492831, 11, [(2, 1), (5, 1), (11, 1), (2797, 1), (795149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2797
    · exact prime_795149
  · decide +kernel

theorem prime_244643492921 : Nat.Prime 244643492921 := by
  apply nodeValid_prime [2, 5, 59, 103662497] ⟨244643492921, 6, [(2, 3), (5, 1), (59, 1), (103662497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_103662497
  · decide +kernel

theorem prime_244643503667 : Nat.Prime 244643503667 := by
  apply nodeValid_prime [2, 122321751833] ⟨244643503667, 2, [(2, 1), (122321751833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_122321751833
  · decide +kernel

theorem prime_245145657391 : Nat.Prime 245145657391 := by
  apply nodeValid_prime [2, 3, 5, 8171521913] ⟨245145657391, 3, [(2, 1), (3, 1), (5, 1), (8171521913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8171521913
  · decide +kernel

theorem prime_245145657749 : Nat.Prime 245145657749 := by
  apply nodeValid_prime [2, 21839, 2806283] ⟨245145657749, 2, [(2, 2), (21839, 1), (2806283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21839
    · exact prime_2806283
  · decide +kernel

theorem prime_245145682489 : Nat.Prime 245145682489 := by
  apply nodeValid_prime [2, 3, 7, 17, 1609, 7621] ⟨245145682489, 19, [(2, 3), (3, 1), (7, 2), (17, 1), (1609, 1), (7621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_1609
    · exact prime_7621
  · decide +kernel

theorem prime_245648536787 : Nat.Prime 245648536787 := by
  apply nodeValid_prime [2, 229, 761, 704797] ⟨245648536787, 2, [(2, 1), (229, 1), (761, 1), (704797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_761
    · exact prime_704797
  · decide +kernel

theorem prime_245648537573 : Nat.Prime 245648537573 := by
  apply nodeValid_prime [2, 109, 563414077] ⟨245648537573, 2, [(2, 2), (109, 1), (563414077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_563414077
  · decide +kernel

theorem prime_245648559157 : Nat.Prime 245648559157 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 20450263] ⟨245648559157, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (20450263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_20450263
  · decide +kernel

end Sude.Lucas.Generated
