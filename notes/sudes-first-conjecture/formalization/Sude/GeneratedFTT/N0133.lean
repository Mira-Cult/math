import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0129

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_16661 : Nat.Prime 16661 := by
  apply nodeValid_prime [2, 5, 7, 17] ⟨16661, 10, [(2, 2), (5, 1), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_21521 : Nat.Prime 21521 := by
  apply nodeValid_prime [2, 5, 269] ⟨21521, 3, [(2, 4), (5, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
  · decide +kernel

theorem prime_22469 : Nat.Prime 22469 := by
  apply nodeValid_prime [2, 41, 137] ⟨22469, 2, [(2, 2), (41, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_137
  · decide +kernel

theorem prime_23321 : Nat.Prime 23321 := by
  apply nodeValid_prime [2, 5, 11, 53] ⟨23321, 3, [(2, 3), (5, 1), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_40897 : Nat.Prime 40897 := by
  apply nodeValid_prime [2, 3, 71] ⟨40897, 5, [(2, 6), (3, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_44563 : Nat.Prime 44563 := by
  apply nodeValid_prime [2, 3, 7, 1061] ⟨44563, 3, [(2, 1), (3, 1), (7, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1061
  · decide +kernel

theorem prime_44939 : Nat.Prime 44939 := by
  apply nodeValid_prime [2, 22469] ⟨44939, 2, [(2, 1), (22469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22469
  · decide +kernel

theorem prime_50411 : Nat.Prime 50411 := by
  apply nodeValid_prime [2, 5, 71] ⟨50411, 2, [(2, 1), (5, 1), (71, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_60727 : Nat.Prime 60727 := by
  apply nodeValid_prime [2, 3, 29, 349] ⟨60727, 5, [(2, 1), (3, 1), (29, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_349
  · decide +kernel

theorem prime_71713 : Nat.Prime 71713 := by
  apply nodeValid_prime [2, 3, 83] ⟨71713, 5, [(2, 5), (3, 3), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_73421 : Nat.Prime 73421 := by
  apply nodeValid_prime [2, 5, 3671] ⟨73421, 2, [(2, 2), (5, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3671
  · decide +kernel

theorem prime_81371 : Nat.Prime 81371 := by
  apply nodeValid_prime [2, 5, 79, 103] ⟨81371, 2, [(2, 1), (5, 1), (79, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_103
  · decide +kernel

theorem prime_95063 : Nat.Prime 95063 := by
  apply nodeValid_prime [2, 11, 29, 149] ⟨95063, 5, [(2, 1), (11, 1), (29, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_149
  · decide +kernel

theorem prime_100519 : Nat.Prime 100519 := by
  apply nodeValid_prime [2, 3, 11, 1523] ⟨100519, 6, [(2, 1), (3, 1), (11, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1523
  · decide +kernel

theorem prime_101323 : Nat.Prime 101323 := by
  apply nodeValid_prime [2, 3, 13, 433] ⟨101323, 2, [(2, 1), (3, 2), (13, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_433
  · decide +kernel

theorem prime_104917 : Nat.Prime 104917 := by
  apply nodeValid_prime [2, 3, 7, 1249] ⟨104917, 2, [(2, 2), (3, 1), (7, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1249
  · decide +kernel

theorem prime_108739 : Nat.Prime 108739 := by
  apply nodeValid_prime [2, 3, 7, 863] ⟨108739, 2, [(2, 1), (3, 2), (7, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_863
  · decide +kernel

theorem prime_109063 : Nat.Prime 109063 := by
  apply nodeValid_prime [2, 3, 73, 83] ⟨109063, 6, [(2, 1), (3, 2), (73, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_83
  · decide +kernel

theorem prime_109849 : Nat.Prime 109849 := by
  apply nodeValid_prime [2, 3, 23, 199] ⟨109849, 7, [(2, 3), (3, 1), (23, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_199
  · decide +kernel

theorem prime_114343 : Nat.Prime 114343 := by
  apply nodeValid_prime [2, 3, 17, 19, 59] ⟨114343, 5, [(2, 1), (3, 1), (17, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_127601 : Nat.Prime 127601 := by
  apply nodeValid_prime [2, 5, 11, 29] ⟨127601, 6, [(2, 4), (5, 2), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_129401 : Nat.Prime 129401 := by
  apply nodeValid_prime [2, 5, 647] ⟨129401, 3, [(2, 3), (5, 2), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_647
  · decide +kernel

theorem prime_139367 : Nat.Prime 139367 := by
  apply nodeValid_prime [2, 17, 4099] ⟨139367, 5, [(2, 1), (17, 1), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4099
  · decide +kernel

theorem prime_143137 : Nat.Prime 143137 := by
  apply nodeValid_prime [2, 3, 7, 71] ⟨143137, 5, [(2, 5), (3, 2), (7, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_146843 : Nat.Prime 146843 := by
  apply nodeValid_prime [2, 73421] ⟨146843, 2, [(2, 1), (73421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73421
  · decide +kernel

theorem prime_199933 : Nat.Prime 199933 := by
  apply nodeValid_prime [2, 3, 16661] ⟨199933, 2, [(2, 2), (3, 1), (16661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16661
  · decide +kernel

theorem prime_224309 : Nat.Prime 224309 := by
  apply nodeValid_prime [2, 7, 8011] ⟨224309, 2, [(2, 2), (7, 1), (8011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8011
  · decide +kernel

theorem prime_232103 : Nat.Prime 232103 := by
  apply nodeValid_prime [2, 13, 79, 113] ⟨232103, 5, [(2, 1), (13, 1), (79, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_113
  · decide +kernel

theorem prime_258803 : Nat.Prime 258803 := by
  apply nodeValid_prime [2, 129401] ⟨258803, 2, [(2, 1), (129401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_129401
  · decide +kernel

theorem prime_259639 : Nat.Prime 259639 := by
  apply nodeValid_prime [2, 3, 109, 397] ⟨259639, 6, [(2, 1), (3, 1), (109, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_397
  · decide +kernel

theorem prime_261167 : Nat.Prime 261167 := by
  apply nodeValid_prime [2, 67, 1949] ⟨261167, 5, [(2, 1), (67, 1), (1949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_1949
  · decide +kernel

theorem prime_303703 : Nat.Prime 303703 := by
  apply nodeValid_prime [2, 3, 7, 1033] ⟨303703, 5, [(2, 1), (3, 1), (7, 2), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1033
  · decide +kernel

theorem prime_324179 : Nat.Prime 324179 := by
  apply nodeValid_prime [2, 19, 449] ⟨324179, 6, [(2, 1), (19, 2), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_449
  · decide +kernel

theorem prime_338753 : Nat.Prime 338753 := by
  apply nodeValid_prime [2, 67, 79] ⟨338753, 3, [(2, 6), (67, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_79
  · decide +kernel

theorem prime_370631 : Nat.Prime 370631 := by
  apply nodeValid_prime [2, 5, 13, 2851] ⟨370631, 7, [(2, 1), (5, 1), (13, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2851
  · decide +kernel

theorem prime_380563 : Nat.Prime 380563 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 41] ⟨380563, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_383941 : Nat.Prime 383941 := by
  apply nodeValid_prime [2, 3, 5, 79] ⟨383941, 2, [(2, 2), (3, 5), (5, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_399793 : Nat.Prime 399793 := by
  apply nodeValid_prime [2, 3, 8329] ⟨399793, 5, [(2, 4), (3, 1), (8329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8329
  · decide +kernel

theorem prime_410561 : Nat.Prime 410561 := by
  apply nodeValid_prime [2, 5, 1283] ⟨410561, 3, [(2, 6), (5, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1283
  · decide +kernel

theorem prime_436253 : Nat.Prime 436253 := by
  apply nodeValid_prime [2, 109063] ⟨436253, 2, [(2, 2), (109063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_109063
  · decide +kernel

theorem prime_501601 : Nat.Prime 501601 := by
  apply nodeValid_prime [2, 3, 5, 11, 19] ⟨501601, 31, [(2, 5), (3, 1), (5, 2), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_507431 : Nat.Prime 507431 := by
  apply nodeValid_prime [2, 5, 7, 11, 659] ⟨507431, 13, [(2, 1), (5, 1), (7, 1), (11, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_659
  · decide +kernel

theorem prime_546253 : Nat.Prime 546253 := by
  apply nodeValid_prime [2, 3, 7, 929] ⟨546253, 2, [(2, 2), (3, 1), (7, 2), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_929
  · decide +kernel

theorem prime_616841 : Nat.Prime 616841 := by
  apply nodeValid_prime [2, 5, 7, 2203] ⟨616841, 6, [(2, 3), (5, 1), (7, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2203
  · decide +kernel

theorem prime_636107 : Nat.Prime 636107 := by
  apply nodeValid_prime [2, 17, 53, 353] ⟨636107, 2, [(2, 1), (17, 1), (53, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_53
    · exact prime_353
  · decide +kernel

theorem prime_690553 : Nat.Prime 690553 := by
  apply nodeValid_prime [2, 3, 23, 139] ⟨690553, 5, [(2, 3), (3, 3), (23, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_139
  · decide +kernel

theorem prime_716731 : Nat.Prime 716731 := by
  apply nodeValid_prime [2, 3, 5, 7, 3413] ⟨716731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (3413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3413
  · decide +kernel

theorem prime_785017 : Nat.Prime 785017 := by
  apply nodeValid_prime [2, 3, 10903] ⟨785017, 5, [(2, 3), (3, 2), (10903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10903
  · decide +kernel

theorem prime_1007429 : Nat.Prime 1007429 := by
  apply nodeValid_prime [2, 251857] ⟨1007429, 2, [(2, 2), (251857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_251857
  · decide +kernel

theorem prime_1049171 : Nat.Prime 1049171 := by
  apply nodeValid_prime [2, 5, 104917] ⟨1049171, 2, [(2, 1), (5, 1), (104917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_104917
  · decide +kernel

theorem prime_1114937 : Nat.Prime 1114937 := by
  apply nodeValid_prime [2, 139367] ⟨1114937, 3, [(2, 3), (139367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_139367
  · decide +kernel

theorem prime_1567003 : Nat.Prime 1567003 := by
  apply nodeValid_prime [2, 3, 261167] ⟨1567003, 7, [(2, 1), (3, 1), (261167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_261167
  · decide +kernel

theorem prime_1696951 : Nat.Prime 1696951 := by
  apply nodeValid_prime [2, 3, 5, 419] ⟨1696951, 6, [(2, 1), (3, 4), (5, 2), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_419
  · decide +kernel

theorem prime_2208439 : Nat.Prime 2208439 := by
  apply nodeValid_prime [2, 3, 40897] ⟨2208439, 7, [(2, 1), (3, 3), (40897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40897
  · decide +kernel

theorem prime_2463367 : Nat.Prime 2463367 := by
  apply nodeValid_prime [2, 3, 410561] ⟨2463367, 7, [(2, 1), (3, 1), (410561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_410561
  · decide +kernel

theorem prime_2551793 : Nat.Prime 2551793 := by
  apply nodeValid_prime [2, 43, 3709] ⟨2551793, 3, [(2, 4), (43, 1), (3709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_3709
  · decide +kernel

theorem prime_2762213 : Nat.Prime 2762213 := by
  apply nodeValid_prime [2, 690553] ⟨2762213, 2, [(2, 2), (690553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_690553
  · decide +kernel

theorem prime_2800309 : Nat.Prime 2800309 := by
  apply nodeValid_prime [2, 3, 7, 17, 37, 53] ⟨2800309, 6, [(2, 2), (3, 1), (7, 1), (17, 1), (37, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_37
    · exact prime_53
  · decide +kernel

theorem prime_3281783 : Nat.Prime 3281783 := by
  apply nodeValid_prime [2, 7, 17, 13789] ⟨3281783, 5, [(2, 1), (7, 1), (17, 1), (13789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_13789
  · decide +kernel

theorem prime_3524233 : Nat.Prime 3524233 := by
  apply nodeValid_prime [2, 3, 146843] ⟨3524233, 5, [(2, 3), (3, 1), (146843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_146843
  · decide +kernel

theorem prime_4710103 : Nat.Prime 4710103 := by
  apply nodeValid_prime [2, 3, 785017] ⟨4710103, 13, [(2, 1), (3, 1), (785017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_785017
  · decide +kernel

theorem prime_6054739 : Nat.Prime 6054739 := by
  apply nodeValid_prime [2, 3, 61, 71, 233] ⟨6054739, 3, [(2, 1), (3, 1), (61, 1), (71, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_71
    · exact prime_233
  · decide +kernel

theorem prime_7549753 : Nat.Prime 7549753 := by
  apply nodeValid_prime [2, 3, 7, 44939] ⟨7549753, 10, [(2, 3), (3, 1), (7, 1), (44939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_44939
  · decide +kernel

theorem prime_7747561 : Nat.Prime 7747561 := by
  apply nodeValid_prime [2, 3, 5, 21521] ⟨7747561, 7, [(2, 3), (3, 2), (5, 1), (21521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21521
  · decide +kernel

theorem prime_8179211 : Nat.Prime 8179211 := by
  apply nodeValid_prime [2, 5, 13, 17, 3701] ⟨8179211, 2, [(2, 1), (5, 1), (13, 1), (17, 1), (3701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_3701
  · decide +kernel

theorem prime_8833757 : Nat.Prime 8833757 := by
  apply nodeValid_prime [2, 2208439] ⟨8833757, 2, [(2, 2), (2208439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2208439
  · decide +kernel

theorem prime_12618689 : Nat.Prime 12618689 := by
  apply nodeValid_prime [2, 71, 2777] ⟨12618689, 3, [(2, 6), (71, 1), (2777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2777
  · decide +kernel

theorem prime_13960097 : Nat.Prime 13960097 := by
  apply nodeValid_prime [2, 436253] ⟨13960097, 3, [(2, 5), (436253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_436253
  · decide +kernel

theorem prime_14486027 : Nat.Prime 14486027 := by
  apply nodeValid_prime [2, 101, 71713] ⟨14486027, 2, [(2, 1), (101, 1), (71713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_71713
  · decide +kernel

theorem prime_19450741 : Nat.Prime 19450741 := by
  apply nodeValid_prime [2, 3, 5, 324179] ⟨19450741, 6, [(2, 2), (3, 1), (5, 1), (324179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_324179
  · decide +kernel

theorem prime_21184277 : Nat.Prime 21184277 := by
  apply nodeValid_prime [2, 37, 143137] ⟨21184277, 2, [(2, 2), (37, 1), (143137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_143137
  · decide +kernel

theorem prime_31438301 : Nat.Prime 31438301 := by
  apply nodeValid_prime [2, 5, 47, 6689] ⟨31438301, 3, [(2, 2), (5, 2), (47, 1), (6689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_6689
  · decide +kernel

theorem prime_34600147 : Nat.Prime 34600147 := by
  apply nodeValid_prime [2, 3, 7, 41, 71, 283] ⟨34600147, 2, [(2, 1), (3, 1), (7, 1), (41, 1), (71, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_71
    · exact prime_283
  · decide +kernel

theorem prime_34786693 : Nat.Prime 34786693 := by
  apply nodeValid_prime [2, 3, 17, 18947] ⟨34786693, 5, [(2, 2), (3, 3), (17, 1), (18947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_18947
  · decide +kernel

theorem prime_35251583 : Nat.Prime 35251583 := by
  apply nodeValid_prime [2, 307, 57413] ⟨35251583, 5, [(2, 1), (307, 1), (57413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_57413
  · decide +kernel

theorem prime_36180631 : Nat.Prime 36180631 := by
  apply nodeValid_prime [2, 3, 5, 43, 9349] ⟨36180631, 3, [(2, 1), (3, 2), (5, 1), (43, 1), (9349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_9349
  · decide +kernel

theorem prime_36891427 : Nat.Prime 36891427 := by
  apply nodeValid_prime [2, 3, 11, 13, 19, 31, 73] ⟨36891427, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (19, 1), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_37403393 : Nat.Prime 37403393 := by
  apply nodeValid_prime [2, 13, 11239] ⟨37403393, 3, [(2, 8), (13, 1), (11239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_11239
  · decide +kernel

theorem prime_39721373 : Nat.Prime 39721373 := by
  apply nodeValid_prime [2, 3083, 3221] ⟨39721373, 2, [(2, 2), (3083, 1), (3221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3083
    · exact prime_3221
  · decide +kernel

theorem prime_44877211 : Nat.Prime 44877211 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 7369] ⟨44877211, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (7369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_7369
  · decide +kernel

theorem prime_46485367 : Nat.Prime 46485367 := by
  apply nodeValid_prime [2, 3, 7747561] ⟨46485367, 5, [(2, 1), (3, 1), (7747561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7747561
  · decide +kernel

theorem prime_60000793 : Nat.Prime 60000793 := by
  apply nodeValid_prime [2, 3, 587, 4259] ⟨60000793, 5, [(2, 3), (3, 1), (587, 1), (4259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_587
    · exact prime_4259
  · decide +kernel

theorem prime_63117337 : Nat.Prime 63117337 := by
  apply nodeValid_prime [2, 3, 23, 114343] ⟨63117337, 5, [(2, 3), (3, 1), (23, 1), (114343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_114343
  · decide +kernel

theorem prime_72656869 : Nat.Prime 72656869 := by
  apply nodeValid_prime [2, 3, 6054739] ⟨72656869, 6, [(2, 2), (3, 1), (6054739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6054739
  · decide +kernel

theorem prime_75497531 : Nat.Prime 75497531 := by
  apply nodeValid_prime [2, 5, 7549753] ⟨75497531, 6, [(2, 1), (5, 1), (7549753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7549753
  · decide +kernel

theorem prime_79570187 : Nat.Prime 79570187 := by
  apply nodeValid_prime [2, 131, 303703] ⟨79570187, 2, [(2, 1), (131, 1), (303703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_303703
  · decide +kernel

theorem prime_101731411 : Nat.Prime 101731411 := by
  apply nodeValid_prime [2, 3, 5, 11, 34253] ⟨101731411, 11, [(2, 1), (3, 3), (5, 1), (11, 1), (34253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_34253
  · decide +kernel

theorem prime_124427393 : Nat.Prime 124427393 := by
  apply nodeValid_prime [2, 421, 2309] ⟨124427393, 3, [(2, 7), (421, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_421
    · exact prime_2309
  · decide +kernel

theorem prime_140688937 : Nat.Prime 140688937 := by
  apply nodeValid_prime [2, 3, 61, 103, 311] ⟨140688937, 5, [(2, 3), (3, 2), (61, 1), (103, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_103
    · exact prime_311
  · decide +kernel

theorem prime_142900409 : Nat.Prime 142900409 := by
  apply nodeValid_prime [2, 7, 2551793] ⟨142900409, 13, [(2, 3), (7, 1), (2551793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2551793
  · decide +kernel

theorem prime_196298281 : Nat.Prime 196298281 := by
  apply nodeValid_prime [2, 3, 5, 293, 1861] ⟨196298281, 17, [(2, 3), (3, 2), (5, 1), (293, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_1861
  · decide +kernel

theorem prime_214326793 : Nat.Prime 214326793 := by
  apply nodeValid_prime [2, 3, 37, 43, 1871] ⟨214326793, 10, [(2, 3), (3, 2), (37, 1), (43, 1), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_43
    · exact prime_1871
  · decide +kernel

theorem prime_218126231 : Nat.Prime 218126231 := by
  apply nodeValid_prime [2, 5, 7, 31, 100519] ⟨218126231, 7, [(2, 1), (5, 1), (7, 1), (31, 1), (100519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_100519
  · decide +kernel

theorem prime_240003173 : Nat.Prime 240003173 := by
  apply nodeValid_prime [2, 60000793] ⟨240003173, 2, [(2, 2), (60000793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60000793
  · decide +kernel

theorem prime_278912203 : Nat.Prime 278912203 := by
  apply nodeValid_prime [2, 3, 46485367] ⟨278912203, 2, [(2, 1), (3, 1), (46485367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_46485367
  · decide +kernel

theorem prime_287729341 : Nat.Prime 287729341 := by
  apply nodeValid_prime [2, 3, 5, 43, 229, 487] ⟨287729341, 2, [(2, 2), (3, 1), (5, 1), (43, 1), (229, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_229
    · exact prime_487
  · decide +kernel

theorem prime_424380251 : Nat.Prime 424380251 := by
  apply nodeValid_prime [2, 5, 7, 281, 863] ⟨424380251, 2, [(2, 1), (5, 3), (7, 1), (281, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_281
    · exact prime_863
  · decide +kernel

theorem prime_435406313 : Nat.Prime 435406313 := by
  apply nodeValid_prime [2, 11, 17, 59, 4933] ⟨435406313, 3, [(2, 3), (11, 1), (17, 1), (59, 1), (4933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_59
    · exact prime_4933
  · decide +kernel

theorem prime_518146441 : Nat.Prime 518146441 := by
  apply nodeValid_prime [2, 3, 5, 7, 616841] ⟨518146441, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (616841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_616841
  · decide +kernel

theorem prime_538526533 : Nat.Prime 538526533 := by
  apply nodeValid_prime [2, 3, 44877211] ⟨538526533, 6, [(2, 2), (3, 1), (44877211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44877211
  · decide +kernel

theorem prime_745214153 : Nat.Prime 745214153 := by
  apply nodeValid_prime [2, 233, 399793] ⟨745214153, 3, [(2, 3), (233, 1), (399793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_399793
  · decide +kernel

theorem prime_1112366513 : Nat.Prime 1112366513 := by
  apply nodeValid_prime [2, 97, 716731] ⟨1112366513, 3, [(2, 4), (97, 1), (716731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_716731
  · decide +kernel

theorem prime_1193055719 : Nat.Prime 1193055719 := by
  apply nodeValid_prime [2, 23321, 25579] ⟨1193055719, 7, [(2, 1), (23321, 1), (25579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23321
    · exact prime_25579
  · decide +kernel

theorem prime_1525233817 : Nat.Prime 1525233817 := by
  apply nodeValid_prime [2, 3, 19, 1114937] ⟨1525233817, 5, [(2, 3), (3, 2), (19, 1), (1114937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1114937
  · decide +kernel

theorem prime_1557801019 : Nat.Prime 1557801019 := by
  apply nodeValid_prime [2, 3, 17, 1696951] ⟨1557801019, 2, [(2, 1), (3, 3), (17, 1), (1696951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1696951
  · decide +kernel

theorem prime_2953441817 : Nat.Prime 2953441817 := by
  apply nodeValid_prime [2, 13, 349, 81371] ⟨2953441817, 3, [(2, 3), (13, 1), (349, 1), (81371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_349
    · exact prime_81371
  · decide +kernel

theorem prime_3216737701 : Nat.Prime 3216737701 := by
  apply nodeValid_prime [2, 3, 5, 11, 73, 4451] ⟨3216737701, 2, [(2, 2), (3, 2), (5, 2), (11, 1), (73, 1), (4451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_73
    · exact prime_4451
  · decide +kernel

theorem prime_7710338711 : Nat.Prime 7710338711 := by
  apply nodeValid_prime [2, 5, 313, 2463367] ⟨7710338711, 11, [(2, 1), (5, 1), (313, 1), (2463367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_313
    · exact prime_2463367
  · decide +kernel

theorem prime_13059565159 : Nat.Prime 13059565159 := by
  apply nodeValid_prime [2, 3, 59, 36891427] ⟨13059565159, 3, [(2, 1), (3, 1), (59, 1), (36891427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_36891427
  · decide +kernel

theorem prime_13288516727 : Nat.Prime 13288516727 := by
  apply nodeValid_prime [2, 191, 34786693] ⟨13288516727, 5, [(2, 1), (191, 1), (34786693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_34786693
  · decide +kernel

theorem prime_15395410777 : Nat.Prime 15395410777 := by
  apply nodeValid_prime [2, 3, 11173, 57413] ⟨15395410777, 7, [(2, 3), (3, 1), (11173, 1), (57413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11173
    · exact prime_57413
  · decide +kernel

theorem prime_16587816433 : Nat.Prime 16587816433 := by
  apply nodeValid_prime [2, 3, 11, 259639] ⟨16587816433, 7, [(2, 4), (3, 1), (11, 3), (259639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_259639
  · decide +kernel

theorem prime_17434420657 : Nat.Prime 17434420657 := by
  apply nodeValid_prime [2, 3, 571, 636107] ⟨17434420657, 5, [(2, 4), (3, 1), (571, 1), (636107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
    · exact prime_636107
  · decide +kernel

theorem prime_36312775957 : Nat.Prime 36312775957 := by
  apply nodeValid_prime [2, 3, 3499, 3559] ⟨36312775957, 2, [(2, 2), (3, 6), (3499, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3499
    · exact prime_3559
  · decide +kernel

theorem prime_45761182153 : Nat.Prime 45761182153 := by
  apply nodeValid_prime [2, 3, 7, 83, 3281783] ⟨45761182153, 10, [(2, 3), (3, 1), (7, 1), (83, 1), (3281783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_3281783
  · decide +kernel

theorem prime_52691387891 : Nat.Prime 52691387891 := by
  apply nodeValid_prime [2, 5, 29, 31, 53, 110587] ⟨52691387891, 2, [(2, 1), (5, 1), (29, 1), (31, 1), (53, 1), (110587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_31
    · exact prime_53
    · exact prime_110587
  · decide +kernel

theorem prime_130595651591 : Nat.Prime 130595651591 := by
  apply nodeValid_prime [2, 5, 13059565159] ⟨130595651591, 11, [(2, 1), (5, 1), (13059565159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13059565159
  · decide +kernel

theorem prime_149682888919 : Nat.Prime 149682888919 := by
  apply nodeValid_prime [2, 3, 659, 12618689] ⟨149682888919, 7, [(2, 1), (3, 2), (659, 1), (12618689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_659
    · exact prime_12618689
  · decide +kernel

theorem prime_261191303183 : Nat.Prime 261191303183 := by
  apply nodeValid_prime [2, 130595651591] ⟨261191303183, 5, [(2, 1), (130595651591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_130595651591
  · decide +kernel

theorem prime_312752352239 : Nat.Prime 312752352239 := by
  apply nodeValid_prime [2, 97, 4759, 338753] ⟨312752352239, 13, [(2, 1), (97, 1), (4759, 1), (338753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_4759
    · exact prime_338753
  · decide +kernel

theorem prime_781880886719 : Nat.Prime 781880886719 := by
  apply nodeValid_prime [2, 101, 199, 19450741] ⟨781880886719, 7, [(2, 1), (101, 1), (199, 1), (19450741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_199
    · exact prime_19450741
  · decide +kernel

theorem prime_789802885979 : Nat.Prime 789802885979 := by
  apply nodeValid_prime [2, 331, 1193055719] ⟨789802885979, 2, [(2, 1), (331, 1), (1193055719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_1193055719
  · decide +kernel

theorem prime_3156940958051 : Nat.Prime 3156940958051 := by
  apply nodeValid_prime [2, 5, 11, 79, 72656869] ⟨3156940958051, 2, [(2, 1), (5, 2), (11, 1), (79, 1), (72656869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_79
    · exact prime_72656869
  · decide +kernel

theorem prime_6214533001021 : Nat.Prime 6214533001021 := by
  apply nodeValid_prime [2, 3, 5, 547, 63117337] ⟨6214533001021, 2, [(2, 2), (3, 2), (5, 1), (547, 1), (63117337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_547
    · exact prime_63117337
  · decide +kernel

theorem prime_6214533001067 : Nat.Prime 6214533001067 := by
  apply nodeValid_prime [2, 13, 31, 7710338711] ⟨6214533001067, 2, [(2, 1), (13, 1), (31, 1), (7710338711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_7710338711
  · decide +kernel

theorem prime_6214533019969 : Nat.Prime 6214533019969 := by
  apply nodeValid_prime [2, 3, 7, 13, 3271, 108739] ⟨6214533019969, 22, [(2, 6), (3, 1), (7, 1), (13, 1), (3271, 1), (108739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_3271
    · exact prime_108739
  · decide +kernel

theorem prime_6219025799681 : Nat.Prime 6219025799681 := by
  apply nodeValid_prime [2, 5, 17, 142900409] ⟨6219025799681, 6, [(2, 9), (5, 1), (17, 1), (142900409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_142900409
  · decide +kernel

theorem prime_6219025828237 : Nat.Prime 6219025828237 := by
  apply nodeValid_prime [2, 3, 13, 13288516727] ⟨6219025828237, 2, [(2, 2), (3, 2), (13, 1), (13288516727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_13288516727
  · decide +kernel

theorem prime_6219025830337 : Nat.Prime 6219025830337 := by
  apply nodeValid_prime [2, 3, 11, 139, 21184277] ⟨6219025830337, 5, [(2, 6), (3, 1), (11, 1), (139, 1), (21184277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
    · exact prime_21184277
  · decide +kernel

theorem prime_6223520772809 : Nat.Prime 6223520772809 := by
  apply nodeValid_prime [2, 17, 45761182153] ⟨6223520772809, 3, [(2, 3), (17, 1), (45761182153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_45761182153
  · decide +kernel

theorem prime_6223520799337 : Nat.Prime 6223520799337 := by
  apply nodeValid_prime [2, 3, 2549, 101731411] ⟨6223520799337, 5, [(2, 3), (3, 1), (2549, 1), (101731411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2549
    · exact prime_101731411
  · decide +kernel

theorem prime_6223520799667 : Nat.Prime 6223520799667 := by
  apply nodeValid_prime [2, 3, 109849, 1049171] ⟨6223520799667, 2, [(2, 1), (3, 3), (109849, 1), (1049171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109849
    · exact prime_1049171
  · decide +kernel

theorem prime_6228017863117 : Nat.Prime 6228017863117 := by
  apply nodeValid_prime [2, 3, 7, 17, 31, 140688937] ⟨6228017863117, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (31, 1), (140688937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_140688937
  · decide +kernel

theorem prime_6228017863373 : Nat.Prime 6228017863373 := by
  apply nodeValid_prime [2, 23, 29, 239, 271, 1567] ⟨6228017863373, 3, [(2, 2), (23, 2), (29, 1), (239, 1), (271, 1), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_239
    · exact prime_271
    · exact prime_1567
  · decide +kernel

theorem prime_6228017942177 : Nat.Prime 6228017942177 := by
  apply nodeValid_prime [2, 37, 131, 173, 232103] ⟨6228017942177, 3, [(2, 5), (37, 1), (131, 1), (173, 1), (232103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_131
    · exact prime_173
    · exact prime_232103
  · decide +kernel

theorem prime_6232517303741 : Nat.Prime 6232517303741 := by
  apply nodeValid_prime [2, 5, 7, 13, 6269, 546253] ⟨6232517303741, 2, [(2, 2), (5, 1), (7, 1), (13, 1), (6269, 1), (546253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_6269
    · exact prime_546253
  · decide +kernel

theorem prime_6232517420047 : Nat.Prime 6232517420047 := by
  apply nodeValid_prime [2, 3, 19, 37, 47, 31438301] ⟨6232517420047, 6, [(2, 1), (3, 1), (19, 1), (37, 1), (47, 1), (31438301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_47
    · exact prime_31438301
  · decide +kernel

theorem prime_6232517420881 : Nat.Prime 6232517420881 := by
  apply nodeValid_prime [2, 3, 5, 719, 743, 48611] ⟨6232517420881, 7, [(2, 4), (3, 1), (5, 1), (719, 1), (743, 1), (48611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_719
    · exact prime_743
    · exact prime_48611
  · decide +kernel

theorem prime_6237018852667 : Nat.Prime 6237018852667 := by
  apply nodeValid_prime [2, 3, 7, 43, 11071, 44563] ⟨6237018852667, 7, [(2, 1), (3, 1), (7, 2), (43, 1), (11071, 1), (44563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_11071
    · exact prime_44563
  · decide +kernel

theorem prime_6237018978809 : Nat.Prime 6237018978809 := by
  apply nodeValid_prime [2, 47, 16587816433] ⟨6237018978809, 3, [(2, 3), (47, 1), (16587816433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_16587816433
  · decide +kernel

theorem prime_6237018979007 : Nat.Prime 6237018979007 := by
  apply nodeValid_prime [2, 601, 797, 6510499] ⟨6237018979007, 5, [(2, 1), (601, 1), (797, 1), (6510499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_797
    · exact prime_6510499
  · decide +kernel

theorem prime_6241522517039 : Nat.Prime 6241522517039 := by
  apply nodeValid_prime [2, 13003, 240003173] ⟨6241522517039, 19, [(2, 1), (13003, 1), (240003173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13003
    · exact prime_240003173
  · decide +kernel

theorem prime_6241522517471 : Nat.Prime 6241522517471 := by
  apply nodeValid_prime [2, 5, 19, 61, 538526533] ⟨6241522517471, 13, [(2, 1), (5, 1), (19, 1), (61, 1), (538526533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_61
    · exact prime_538526533
  · decide +kernel

theorem prime_6241522595207 : Nat.Prime 6241522595207 := by
  apply nodeValid_prime [2, 179, 17434420657] ⟨6241522595207, 5, [(2, 1), (179, 1), (17434420657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_17434420657
  · decide +kernel

theorem prime_6246028534219 : Nat.Prime 6246028534219 := by
  apply nodeValid_prime [2, 3, 11, 223, 424380251] ⟨6246028534219, 2, [(2, 1), (3, 1), (11, 1), (223, 1), (424380251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_223
    · exact prime_424380251
  · decide +kernel

theorem prime_6246028534429 : Nat.Prime 6246028534429 := by
  apply nodeValid_prime [2, 3, 67, 287729341] ⟨6246028534429, 2, [(2, 2), (3, 4), (67, 1), (287729341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_287729341
  · decide +kernel

theorem prime_6246028535759 : Nat.Prime 6246028535759 := by
  apply nodeValid_prime [2, 11, 71, 10789, 370631] ⟨6246028535759, 11, [(2, 1), (11, 1), (71, 1), (10789, 1), (370631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_10789
    · exact prime_370631
  · decide +kernel

theorem prime_6250536687779 : Nat.Prime 6250536687779 := by
  apply nodeValid_prime [2, 23, 37, 449, 8179211] ⟨6250536687779, 2, [(2, 1), (23, 1), (37, 1), (449, 1), (8179211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_449
    · exact prime_8179211
  · decide +kernel

theorem prime_6250536775463 : Nat.Prime 6250536775463 := by
  apply nodeValid_prime [2, 7, 29, 15395410777] ⟨6250536775463, 7, [(2, 1), (7, 1), (29, 1), (15395410777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_15395410777
  · decide +kernel

theorem prime_6250536775519 : Nat.Prime 6250536775519 := by
  apply nodeValid_prime [2, 3, 7, 17, 991, 8833757] ⟨6250536775519, 7, [(2, 1), (3, 1), (7, 1), (17, 1), (991, 1), (8833757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_991
    · exact prime_8833757
  · decide +kernel

theorem prime_6255047044781 : Nat.Prime 6255047044781 := by
  apply nodeValid_prime [2, 5, 312752352239] ⟨6255047044781, 2, [(2, 2), (5, 1), (312752352239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_312752352239
  · decide +kernel

theorem prime_6255047092559 : Nat.Prime 6255047092559 := by
  apply nodeValid_prime [2, 11, 653, 435406313] ⟨6255047092559, 11, [(2, 1), (11, 1), (653, 1), (435406313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_653
    · exact prime_435406313
  · decide +kernel

theorem prime_6255047093753 : Nat.Prime 6255047093753 := by
  apply nodeValid_prime [2, 781880886719] ⟨6255047093753, 3, [(2, 3), (781880886719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_781880886719
  · decide +kernel

theorem prime_6259559584529 : Nat.Prime 6259559584529 := by
  apply nodeValid_prime [2, 1993, 196298281] ⟨6259559584529, 3, [(2, 4), (1993, 1), (196298281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1993
    · exact prime_196298281
  · decide +kernel

theorem prime_6259559584969 : Nat.Prime 6259559584969 := by
  apply nodeValid_prime [2, 3, 19, 1525233817] ⟨6259559584969, 7, [(2, 3), (3, 3), (19, 1), (1525233817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1525233817
  · decide +kernel

theorem prime_6259559585819 : Nat.Prime 6259559585819 := by
  apply nodeValid_prime [2, 7, 11, 25939, 1567003] ⟨6259559585819, 2, [(2, 1), (7, 1), (11, 1), (25939, 1), (1567003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_25939
    · exact prime_1567003
  · decide +kernel

theorem prime_6264074202439 : Nat.Prime 6264074202439 := by
  apply nodeValid_prime [2, 3, 13, 971, 8389, 9859] ⟨6264074202439, 17, [(2, 1), (3, 1), (13, 1), (971, 1), (8389, 1), (9859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_971
    · exact prime_8389
    · exact prime_9859
  · decide +kernel

theorem prime_6264074203201 : Nat.Prime 6264074203201 := by
  apply nodeValid_prime [2, 3, 5, 11, 103, 383941] ⟨6264074203201, 21, [(2, 6), (3, 2), (5, 2), (11, 1), (103, 1), (383941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_103
    · exact prime_383941
  · decide +kernel

theorem prime_6264074331943 : Nat.Prime 6264074331943 := by
  apply nodeValid_prime [2, 3, 7, 251, 1171, 507431] ⟨6264074331943, 3, [(2, 1), (3, 1), (7, 1), (251, 1), (1171, 1), (507431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_251
    · exact prime_1171
    · exact prime_507431
  · decide +kernel

theorem prime_6268591276393 : Nat.Prime 6268591276393 := by
  apply nodeValid_prime [2, 3, 261191303183] ⟨6268591276393, 5, [(2, 3), (3, 1), (261191303183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_261191303183
  · decide +kernel

theorem prime_6268591300457 : Nat.Prime 6268591300457 := by
  apply nodeValid_prime [2, 503, 1557801019] ⟨6268591300457, 3, [(2, 3), (503, 1), (1557801019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_503
    · exact prime_1557801019
  · decide +kernel

theorem prime_6268591300847 : Nat.Prime 6268591300847 := by
  apply nodeValid_prime [2, 7, 95063, 4710103] ⟨6268591300847, 5, [(2, 1), (7, 1), (95063, 1), (4710103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_95063
    · exact prime_4710103
  · decide +kernel

theorem prime_6273110387777 : Nat.Prime 6273110387777 := by
  apply nodeValid_prime [2, 263, 743, 501601] ⟨6273110387777, 3, [(2, 6), (263, 1), (743, 1), (501601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_743
    · exact prime_501601
  · decide +kernel

theorem prime_6273110388821 : Nat.Prime 6273110388821 := by
  apply nodeValid_prime [2, 5, 11, 17, 6481, 258803] ⟨6273110388821, 7, [(2, 2), (5, 1), (11, 1), (17, 1), (6481, 1), (258803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_6481
    · exact prime_258803
  · decide +kernel

theorem prime_6273110419309 : Nat.Prime 6273110419309 := by
  apply nodeValid_prime [2, 3, 59, 2953441817] ⟨6273110419309, 2, [(2, 2), (3, 2), (59, 1), (2953441817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2953441817
  · decide +kernel

theorem prime_6277631765267 : Nat.Prime 6277631765267 := by
  apply nodeValid_prime [2, 233, 4877, 2762213] ⟨6277631765267, 2, [(2, 1), (233, 1), (4877, 1), (2762213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_4877
    · exact prime_2762213
  · decide +kernel

theorem prime_6277631766971 : Nat.Prime 6277631766971 := by
  apply nodeValid_prime [2, 5, 29, 101, 214326793] ⟨6277631766971, 6, [(2, 1), (5, 1), (29, 1), (101, 1), (214326793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_101
    · exact prime_214326793
  · decide +kernel

theorem prime_6277631767573 : Nat.Prime 6277631767573 := by
  apply nodeValid_prime [2, 3, 11, 17, 7351, 380563] ⟨6277631767573, 7, [(2, 2), (3, 1), (11, 1), (17, 1), (7351, 1), (380563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_7351
    · exact prime_380563
  · decide +kernel

theorem prime_6282155309791 : Nat.Prime 6282155309791 := by
  apply nodeValid_prime [2, 3, 5, 281, 745214153] ⟨6282155309791, 6, [(2, 1), (3, 1), (5, 1), (281, 1), (745214153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_281
    · exact prime_745214153
  · decide +kernel

theorem prime_6282155329091 : Nat.Prime 6282155329091 := by
  apply nodeValid_prime [2, 5, 17, 2551, 14486027] ⟨6282155329091, 2, [(2, 1), (5, 1), (17, 1), (2551, 1), (14486027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2551
    · exact prime_14486027
  · decide +kernel

theorem prime_6282155330777 : Nat.Prime 6282155330777 := by
  apply nodeValid_prime [2, 13, 4327, 13960097] ⟨6282155330777, 3, [(2, 3), (13, 1), (4327, 1), (13960097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4327
    · exact prime_13960097
  · decide +kernel

theorem prime_6286681055621 : Nat.Prime 6286681055621 := by
  apply nodeValid_prime [2, 5, 7, 23, 278912203] ⟨6286681055621, 2, [(2, 2), (5, 1), (7, 2), (23, 1), (278912203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_278912203
  · decide +kernel

theorem prime_6286681334497 : Nat.Prime 6286681334497 := by
  apply nodeValid_prime [2, 3, 823, 79570187] ⟨6286681334497, 13, [(2, 5), (3, 1), (823, 1), (79570187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_823
    · exact prime_79570187
  · decide +kernel

theorem prime_6286681334599 : Nat.Prime 6286681334599 := by
  apply nodeValid_prime [2, 3, 7, 149682888919] ⟨6286681334599, 3, [(2, 1), (3, 1), (7, 1), (149682888919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149682888919
  · decide +kernel

theorem prime_6291209011679 : Nat.Prime 6291209011679 := by
  apply nodeValid_prime [2, 17, 29, 181, 35251583] ⟨6291209011679, 7, [(2, 1), (17, 1), (29, 1), (181, 1), (35251583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_181
    · exact prime_35251583
  · decide +kernel

theorem prime_6291209105941 : Nat.Prime 6291209105941 := by
  apply nodeValid_prime [2, 3, 5, 11, 60727, 156967] ⟨6291209105941, 10, [(2, 2), (3, 1), (5, 1), (11, 1), (60727, 1), (156967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_60727
    · exact prime_156967
  · decide +kernel

theorem prime_6291209106137 : Nat.Prime 6291209106137 := by
  apply nodeValid_prime [2, 19, 101323, 408491] ⟨6291209106137, 3, [(2, 3), (19, 1), (101323, 1), (408491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_101323
    · exact prime_408491
  · decide +kernel

theorem prime_6295739109761 : Nat.Prime 6295739109761 := by
  apply nodeValid_prime [2, 5, 263, 37403393] ⟨6295739109761, 3, [(2, 7), (5, 1), (263, 1), (37403393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
    · exact prime_37403393
  · decide +kernel

theorem prime_6295739110091 : Nat.Prime 6295739110091 := by
  apply nodeValid_prime [2, 5, 31, 269, 75497531] ⟨6295739110091, 6, [(2, 1), (5, 1), (31, 1), (269, 1), (75497531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_269
    · exact prime_75497531
  · decide +kernel

theorem prime_6295739170463 : Nat.Prime 6295739170463 := by
  apply nodeValid_prime [2, 7, 127601, 3524233] ⟨6295739170463, 5, [(2, 1), (7, 1), (127601, 1), (3524233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_127601
    · exact prime_3524233
  · decide +kernel

theorem prime_6300271532501 : Nat.Prime 6300271532501 := by
  apply nodeValid_prime [2, 5, 11, 29, 1297, 6091] ⟨6300271532501, 13, [(2, 2), (5, 4), (11, 1), (29, 1), (1297, 1), (6091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_1297
    · exact prime_6091
  · decide +kernel

theorem prime_6300271566937 : Nat.Prime 6300271566937 := by
  apply nodeValid_prime [2, 3, 281, 34600147] ⟨6300271566937, 5, [(2, 3), (3, 4), (281, 1), (34600147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_34600147
  · decide +kernel

theorem prime_6300271569349 : Nat.Prime 6300271569349 := by
  apply nodeValid_prime [2, 3, 19, 41, 223, 1007429] ⟨6300271569349, 2, [(2, 2), (3, 2), (19, 1), (41, 1), (223, 1), (1007429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_223
    · exact prime_1007429
  · decide +kernel

theorem prime_6304805893961 : Nat.Prime 6304805893961 := by
  apply nodeValid_prime [2, 5, 7, 3216737701] ⟨6304805893961, 3, [(2, 3), (5, 1), (7, 2), (3216737701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3216737701
  · decide +kernel

theorem prime_6304805894089 : Nat.Prime 6304805894089 := by
  apply nodeValid_prime [2, 3, 13, 518146441] ⟨6304805894089, 11, [(2, 3), (3, 2), (13, 2), (518146441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_518146441
  · decide +kernel

theorem prime_6304806103613 : Nat.Prime 6304806103613 := by
  apply nodeValid_prime [2, 31, 67, 271, 2800309] ⟨6304806103613, 2, [(2, 2), (31, 1), (67, 1), (271, 1), (2800309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_67
    · exact prime_271
    · exact prime_2800309
  · decide +kernel

theorem prime_6309342861737 : Nat.Prime 6309342861737 := by
  apply nodeValid_prime [2, 709, 1112366513] ⟨6309342861737, 3, [(2, 3), (709, 1), (1112366513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_709
    · exact prime_1112366513
  · decide +kernel

theorem prime_6309342861839 : Nat.Prime 6309342861839 := by
  apply nodeValid_prime [2, 313, 50411, 199933] ⟨6309342861839, 17, [(2, 1), (313, 1), (50411, 1), (199933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_50411
    · exact prime_199933
  · decide +kernel

theorem prime_6309342887321 : Nat.Prime 6309342887321 := by
  apply nodeValid_prime [2, 5, 11, 19, 39721373] ⟨6309342887321, 3, [(2, 3), (5, 1), (11, 1), (19, 2), (39721373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_39721373
  · decide +kernel

theorem prime_6313881882527 : Nat.Prime 6313881882527 := by
  apply nodeValid_prime [2, 41, 353, 218126231] ⟨6313881882527, 5, [(2, 1), (41, 1), (353, 1), (218126231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_353
    · exact prime_218126231
  · decide +kernel

theorem prime_6313881915811 : Nat.Prime 6313881915811 := by
  apply nodeValid_prime [2, 3, 5, 7, 277, 36180631] ⟨6313881915811, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (277, 1), (36180631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_277
    · exact prime_36180631
  · decide +kernel

theorem prime_6313881916103 : Nat.Prime 6313881916103 := by
  apply nodeValid_prime [2, 3156940958051] ⟨6313881916103, 5, [(2, 1), (3156940958051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3156940958051
  · decide +kernel

theorem prime_6318423016519 : Nat.Prime 6318423016519 := by
  apply nodeValid_prime [2, 3, 29, 36312775957] ⟨6318423016519, 6, [(2, 1), (3, 1), (29, 1), (36312775957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_36312775957
  · decide +kernel

theorem prime_6318423016541 : Nat.Prime 6318423016541 := by
  apply nodeValid_prime [2, 5, 2539, 124427393] ⟨6318423016541, 2, [(2, 2), (5, 1), (2539, 1), (124427393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2539
    · exact prime_124427393
  · decide +kernel

theorem prime_6318423087833 : Nat.Prime 6318423087833 := by
  apply nodeValid_prime [2, 789802885979] ⟨6318423087833, 3, [(2, 3), (789802885979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_789802885979
  · decide +kernel

theorem prime_6322966508281 : Nat.Prime 6322966508281 := by
  apply nodeValid_prime [2, 3, 5, 401, 11443, 11483] ⟨6322966508281, 13, [(2, 3), (3, 1), (5, 1), (401, 1), (11443, 1), (11483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_401
    · exact prime_11443
    · exact prime_11483
  · decide +kernel

theorem prime_6322966546921 : Nat.Prime 6322966546921 := by
  apply nodeValid_prime [2, 3, 5, 52691387891] ⟨6322966546921, 7, [(2, 3), (3, 1), (5, 1), (52691387891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_52691387891
  · decide +kernel

theorem prime_6322966546997 : Nat.Prime 6322966546997 := by
  apply nodeValid_prime [2, 11, 139, 419, 224309] ⟨6322966546997, 2, [(2, 2), (11, 2), (139, 1), (419, 1), (224309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_139
    · exact prime_419
    · exact prime_224309
  · decide +kernel

end Sude.Lucas.Generated
