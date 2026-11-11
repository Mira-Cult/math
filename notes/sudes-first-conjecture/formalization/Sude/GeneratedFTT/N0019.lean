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
import Sude.GeneratedFTT.N0018

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2269 : Nat.Prime 2269 := by
  apply nodeValid_prime [2, 3, 7] ⟨2269, 2, [(2, 2), (3, 4), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_2423 : Nat.Prime 2423 := by
  apply nodeValid_prime [2, 7, 173] ⟨2423, 5, [(2, 1), (7, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_173
  · decide +kernel

theorem prime_3527 : Nat.Prime 3527 := by
  apply nodeValid_prime [2, 41, 43] ⟨3527, 5, [(2, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_4013 : Nat.Prime 4013 := by
  apply nodeValid_prime [2, 17, 59] ⟨4013, 2, [(2, 2), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_4129 : Nat.Prime 4129 := by
  apply nodeValid_prime [2, 3, 43] ⟨4129, 13, [(2, 5), (3, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_4159 : Nat.Prime 4159 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨4159, 3, [(2, 1), (3, 3), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_4789 : Nat.Prime 4789 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨4789, 2, [(2, 2), (3, 2), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_5507 : Nat.Prime 5507 := by
  apply nodeValid_prime [2, 2753] ⟨5507, 2, [(2, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2753
  · decide +kernel

theorem prime_5749 : Nat.Prime 5749 := by
  apply nodeValid_prime [2, 3, 479] ⟨5749, 2, [(2, 2), (3, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
  · decide +kernel

theorem prime_6449 : Nat.Prime 6449 := by
  apply nodeValid_prime [2, 13, 31] ⟨6449, 3, [(2, 4), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_6569 : Nat.Prime 6569 := by
  apply nodeValid_prime [2, 821] ⟨6569, 3, [(2, 3), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_821
  · decide +kernel

theorem prime_7297 : Nat.Prime 7297 := by
  apply nodeValid_prime [2, 3, 19] ⟨7297, 5, [(2, 7), (3, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_8059 : Nat.Prime 8059 := by
  apply nodeValid_prime [2, 3, 17, 79] ⟨8059, 3, [(2, 1), (3, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_8329 : Nat.Prime 8329 := by
  apply nodeValid_prime [2, 3, 347] ⟨8329, 7, [(2, 3), (3, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
  · decide +kernel

theorem prime_9433 : Nat.Prime 9433 := by
  apply nodeValid_prime [2, 3, 131] ⟨9433, 5, [(2, 3), (3, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_9679 : Nat.Prime 9679 := by
  apply nodeValid_prime [2, 3, 1613] ⟨9679, 3, [(2, 1), (3, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1613
  · decide +kernel

theorem prime_10169 : Nat.Prime 10169 := by
  apply nodeValid_prime [2, 31, 41] ⟨10169, 3, [(2, 3), (31, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41
  · decide +kernel

theorem prime_11489 : Nat.Prime 11489 := by
  apply nodeValid_prime [2, 359] ⟨11489, 3, [(2, 5), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_359
  · decide +kernel

theorem prime_12457 : Nat.Prime 12457 := by
  apply nodeValid_prime [2, 3, 173] ⟨12457, 10, [(2, 3), (3, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
  · decide +kernel

theorem prime_13327 : Nat.Prime 13327 := by
  apply nodeValid_prime [2, 3, 2221] ⟨13327, 3, [(2, 1), (3, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2221
  · decide +kernel

theorem prime_13469 : Nat.Prime 13469 := by
  apply nodeValid_prime [2, 7, 13, 37] ⟨13469, 2, [(2, 2), (7, 1), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_13859 : Nat.Prime 13859 := by
  apply nodeValid_prime [2, 13, 41] ⟨13859, 2, [(2, 1), (13, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_14561 : Nat.Prime 14561 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨14561, 6, [(2, 5), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_15241 : Nat.Prime 15241 := by
  apply nodeValid_prime [2, 3, 5, 127] ⟨15241, 11, [(2, 3), (3, 1), (5, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_15329 : Nat.Prime 15329 := by
  apply nodeValid_prime [2, 479] ⟨15329, 3, [(2, 5), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_479
  · decide +kernel

theorem prime_15733 : Nat.Prime 15733 := by
  apply nodeValid_prime [2, 3, 19, 23] ⟨15733, 6, [(2, 2), (3, 2), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_17599 : Nat.Prime 17599 := by
  apply nodeValid_prime [2, 3, 7, 419] ⟨17599, 6, [(2, 1), (3, 1), (7, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_419
  · decide +kernel

theorem prime_18353 : Nat.Prime 18353 := by
  apply nodeValid_prime [2, 31, 37] ⟨18353, 3, [(2, 4), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_19541 : Nat.Prime 19541 := by
  apply nodeValid_prime [2, 5, 977] ⟨19541, 2, [(2, 2), (5, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_977
  · decide +kernel

theorem prime_20939 : Nat.Prime 20939 := by
  apply nodeValid_prime [2, 19, 29] ⟨20939, 2, [(2, 1), (19, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_21673 : Nat.Prime 21673 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨21673, 10, [(2, 3), (3, 2), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_23957 : Nat.Prime 23957 := by
  apply nodeValid_prime [2, 53, 113] ⟨23957, 2, [(2, 2), (53, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_113
  · decide +kernel

theorem prime_24793 : Nat.Prime 24793 := by
  apply nodeValid_prime [2, 3, 1033] ⟨24793, 5, [(2, 3), (3, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
  · decide +kernel

theorem prime_28307 : Nat.Prime 28307 := by
  apply nodeValid_prime [2, 14153] ⟨28307, 2, [(2, 1), (14153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14153
  · decide +kernel

theorem prime_29803 : Nat.Prime 29803 := by
  apply nodeValid_prime [2, 3, 4967] ⟨29803, 7, [(2, 1), (3, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4967
  · decide +kernel

theorem prime_31469 : Nat.Prime 31469 := by
  apply nodeValid_prime [2, 7867] ⟨31469, 2, [(2, 2), (7867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7867
  · decide +kernel

theorem prime_31667 : Nat.Prime 31667 := by
  apply nodeValid_prime [2, 71, 223] ⟨31667, 2, [(2, 1), (71, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_223
  · decide +kernel

theorem prime_33359 : Nat.Prime 33359 := by
  apply nodeValid_prime [2, 13, 1283] ⟨33359, 7, [(2, 1), (13, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1283
  · decide +kernel

theorem prime_34649 : Nat.Prime 34649 := by
  apply nodeValid_prime [2, 61, 71] ⟨34649, 3, [(2, 3), (61, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_71
  · decide +kernel

theorem prime_38713 : Nat.Prime 38713 := by
  apply nodeValid_prime [2, 3, 1613] ⟨38713, 5, [(2, 3), (3, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1613
  · decide +kernel

theorem prime_41879 : Nat.Prime 41879 := by
  apply nodeValid_prime [2, 20939] ⟨41879, 13, [(2, 1), (20939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20939
  · decide +kernel

theorem prime_48259 : Nat.Prime 48259 := by
  apply nodeValid_prime [2, 3, 7, 383] ⟨48259, 2, [(2, 1), (3, 2), (7, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
  · decide +kernel

theorem prime_60901 : Nat.Prime 60901 := by
  apply nodeValid_prime [2, 3, 5, 7, 29] ⟨60901, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_61561 : Nat.Prime 61561 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨61561, 7, [(2, 3), (3, 4), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_64919 : Nat.Prime 64919 := by
  apply nodeValid_prime [2, 7, 4637] ⟨64919, 7, [(2, 1), (7, 1), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4637
  · decide +kernel

theorem prime_80279 : Nat.Prime 80279 := by
  apply nodeValid_prime [2, 11, 41, 89] ⟨80279, 11, [(2, 1), (11, 1), (41, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_89
  · decide +kernel

theorem prime_86693 : Nat.Prime 86693 := by
  apply nodeValid_prime [2, 21673] ⟨86693, 2, [(2, 2), (21673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21673
  · decide +kernel

theorem prime_99173 : Nat.Prime 99173 := by
  apply nodeValid_prime [2, 24793] ⟨99173, 2, [(2, 2), (24793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24793
  · decide +kernel

theorem prime_101581 : Nat.Prime 101581 := by
  apply nodeValid_prime [2, 3, 5, 1693] ⟨101581, 2, [(2, 2), (3, 1), (5, 1), (1693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1693
  · decide +kernel

theorem prime_113357 : Nat.Prime 113357 := by
  apply nodeValid_prime [2, 17, 1667] ⟨113357, 2, [(2, 2), (17, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1667
  · decide +kernel

theorem prime_115361 : Nat.Prime 115361 := by
  apply nodeValid_prime [2, 5, 7, 103] ⟨115361, 6, [(2, 5), (5, 1), (7, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_156329 : Nat.Prime 156329 := by
  apply nodeValid_prime [2, 19541] ⟨156329, 3, [(2, 3), (19541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19541
  · decide +kernel

theorem prime_255133 : Nat.Prime 255133 := by
  apply nodeValid_prime [2, 3, 19, 373] ⟨255133, 6, [(2, 2), (3, 2), (19, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_373
  · decide +kernel

theorem prime_261427 : Nat.Prime 261427 := by
  apply nodeValid_prime [2, 3, 11, 17, 233] ⟨261427, 2, [(2, 1), (3, 1), (11, 1), (17, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_233
  · decide +kernel

theorem prime_275923 : Nat.Prime 275923 := by
  apply nodeValid_prime [2, 3, 15329] ⟨275923, 2, [(2, 1), (3, 2), (15329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15329
  · decide +kernel

theorem prime_288317 : Nat.Prime 288317 := by
  apply nodeValid_prime [2, 7, 1471] ⟨288317, 2, [(2, 2), (7, 2), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1471
  · decide +kernel

theorem prime_288803 : Nat.Prime 288803 := by
  apply nodeValid_prime [2, 197, 733] ⟨288803, 2, [(2, 1), (197, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_733
  · decide +kernel

theorem prime_343379 : Nat.Prime 343379 := by
  apply nodeValid_prime [2, 7, 24527] ⟨343379, 2, [(2, 1), (7, 1), (24527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_24527
  · decide +kernel

theorem prime_346831 : Nat.Prime 346831 := by
  apply nodeValid_prime [2, 3, 5, 11, 1051] ⟨346831, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1051
  · decide +kernel

theorem prime_371281 : Nat.Prime 371281 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 17] ⟨371281, 19, [(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_381529 : Nat.Prime 381529 := by
  apply nodeValid_prime [2, 3, 7, 757] ⟨381529, 13, [(2, 3), (3, 2), (7, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_757
  · decide +kernel

theorem prime_396299 : Nat.Prime 396299 := by
  apply nodeValid_prime [2, 7, 28307] ⟨396299, 2, [(2, 1), (7, 1), (28307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_28307
  · decide +kernel

theorem prime_430741 : Nat.Prime 430741 := by
  apply nodeValid_prime [2, 3, 5, 2393] ⟨430741, 2, [(2, 2), (3, 2), (5, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2393
  · decide +kernel

theorem prime_435997 : Nat.Prime 435997 := by
  apply nodeValid_prime [2, 3, 11, 367] ⟨435997, 2, [(2, 2), (3, 3), (11, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_367
  · decide +kernel

theorem prime_482509 : Nat.Prime 482509 := by
  apply nodeValid_prime [2, 3, 13, 1031] ⟨482509, 7, [(2, 2), (3, 2), (13, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1031
  · decide +kernel

theorem prime_502549 : Nat.Prime 502549 := by
  apply nodeValid_prime [2, 3, 41879] ⟨502549, 6, [(2, 2), (3, 1), (41879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41879
  · decide +kernel

theorem prime_524857 : Nat.Prime 524857 := by
  apply nodeValid_prime [2, 3, 19, 1151] ⟨524857, 5, [(2, 3), (3, 1), (19, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1151
  · decide +kernel

theorem prime_595039 : Nat.Prime 595039 := by
  apply nodeValid_prime [2, 3, 99173] ⟨595039, 3, [(2, 1), (3, 1), (99173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_99173
  · decide +kernel

theorem prime_609487 : Nat.Prime 609487 := by
  apply nodeValid_prime [2, 3, 101581] ⟨609487, 3, [(2, 1), (3, 1), (101581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101581
  · decide +kernel

theorem prime_639151 : Nat.Prime 639151 := by
  apply nodeValid_prime [2, 3, 5, 4261] ⟨639151, 3, [(2, 1), (3, 1), (5, 2), (4261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4261
  · decide +kernel

theorem prime_688087 : Nat.Prime 688087 := by
  apply nodeValid_prime [2, 3, 7, 43, 127] ⟨688087, 5, [(2, 1), (3, 2), (7, 1), (43, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_127
  · decide +kernel

theorem prime_713021 : Nat.Prime 713021 := by
  apply nodeValid_prime [2, 5, 7, 11, 463] ⟨713021, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_463
  · decide +kernel

theorem prime_731923 : Nat.Prime 731923 := by
  apply nodeValid_prime [2, 3, 199, 613] ⟨731923, 3, [(2, 1), (3, 1), (199, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_613
  · decide +kernel

theorem prime_761833 : Nat.Prime 761833 := by
  apply nodeValid_prime [2, 3, 3527] ⟨761833, 10, [(2, 3), (3, 3), (3527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3527
  · decide +kernel

theorem prime_765041 : Nat.Prime 765041 := by
  apply nodeValid_prime [2, 5, 73, 131] ⟨765041, 3, [(2, 4), (5, 1), (73, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_131
  · decide +kernel

theorem prime_868663 : Nat.Prime 868663 := by
  apply nodeValid_prime [2, 3, 48259] ⟨868663, 6, [(2, 1), (3, 2), (48259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48259
  · decide +kernel

theorem prime_946733 : Nat.Prime 946733 := by
  apply nodeValid_prime [2, 19, 12457] ⟨946733, 2, [(2, 2), (19, 1), (12457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_12457
  · decide +kernel

theorem prime_1314673 : Nat.Prime 1314673 := by
  apply nodeValid_prime [2, 3, 61, 449] ⟨1314673, 7, [(2, 4), (3, 1), (61, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_449
  · decide +kernel

theorem prime_1454081 : Nat.Prime 1454081 := by
  apply nodeValid_prime [2, 5, 71] ⟨1454081, 3, [(2, 12), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_1812301 : Nat.Prime 1812301 := by
  apply nodeValid_prime [2, 3, 5, 7, 863] ⟨1812301, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_863
  · decide +kernel

theorem prime_1862033 : Nat.Prime 1862033 := by
  apply nodeValid_prime [2, 29, 4013] ⟨1862033, 3, [(2, 4), (29, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_4013
  · decide +kernel

theorem prime_1893467 : Nat.Prime 1893467 := by
  apply nodeValid_prime [2, 946733] ⟨1893467, 2, [(2, 1), (946733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_946733
  · decide +kernel

theorem prime_3170393 : Nat.Prime 3170393 := by
  apply nodeValid_prime [2, 396299] ⟨3170393, 3, [(2, 3), (396299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_396299
  · decide +kernel

theorem prime_5259473 : Nat.Prime 5259473 := by
  apply nodeValid_prime [2, 113, 2909] ⟨5259473, 3, [(2, 4), (113, 1), (2909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_2909
  · decide +kernel

theorem prime_5795971 : Nat.Prime 5795971 := by
  apply nodeValid_prime [2, 3, 5, 43, 4493] ⟨5795971, 10, [(2, 1), (3, 1), (5, 1), (43, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_4493
  · decide +kernel

theorem prime_6235601 : Nat.Prime 6235601 := by
  apply nodeValid_prime [2, 5, 7, 17, 131] ⟨6235601, 6, [(2, 4), (5, 2), (7, 1), (17, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_131
  · decide +kernel

theorem prime_6340787 : Nat.Prime 6340787 := by
  apply nodeValid_prime [2, 3170393] ⟨6340787, 2, [(2, 1), (3170393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3170393
  · decide +kernel

theorem prime_6683059 : Nat.Prime 6683059 := by
  apply nodeValid_prime [2, 3, 371281] ⟨6683059, 2, [(2, 1), (3, 2), (371281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_371281
  · decide +kernel

theorem prime_8783077 : Nat.Prime 8783077 := by
  apply nodeValid_prime [2, 3, 731923] ⟨8783077, 2, [(2, 2), (3, 1), (731923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_731923
  · decide +kernel

theorem prime_9108679 : Nat.Prime 9108679 := by
  apply nodeValid_prime [2, 3, 317, 4789] ⟨9108679, 3, [(2, 1), (3, 1), (317, 1), (4789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
    · exact prime_4789
  · decide +kernel

theorem prime_9246473 : Nat.Prime 9246473 := by
  apply nodeValid_prime [2, 71, 73, 223] ⟨9246473, 3, [(2, 3), (71, 1), (73, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_73
    · exact prime_223
  · decide +kernel

theorem prime_13386809 : Nat.Prime 13386809 := by
  apply nodeValid_prime [2, 191, 8761] ⟨13386809, 3, [(2, 3), (191, 1), (8761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_8761
  · decide +kernel

theorem prime_14269781 : Nat.Prime 14269781 := by
  apply nodeValid_prime [2, 5, 7, 14561] ⟨14269781, 2, [(2, 2), (5, 1), (7, 2), (14561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_14561
  · decide +kernel

theorem prime_15882739 : Nat.Prime 15882739 := by
  apply nodeValid_prime [2, 3, 43, 61561] ⟨15882739, 13, [(2, 1), (3, 1), (43, 1), (61561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_61561
  · decide +kernel

theorem prime_16353481 : Nat.Prime 16353481 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 953] ⟨16353481, 19, [(2, 3), (3, 1), (5, 1), (11, 1), (13, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_953
  · decide +kernel

theorem prime_21747613 : Nat.Prime 21747613 := by
  apply nodeValid_prime [2, 3, 1812301] ⟨21747613, 2, [(2, 2), (3, 1), (1812301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1812301
  · decide +kernel

theorem prime_28814771 : Nat.Prime 28814771 := by
  apply nodeValid_prime [2, 5, 1511, 1907] ⟨28814771, 2, [(2, 1), (5, 1), (1511, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1511
    · exact prime_1907
  · decide +kernel

theorem prime_38093593 : Nat.Prime 38093593 := by
  apply nodeValid_prime [2, 3, 41, 38713] ⟨38093593, 7, [(2, 3), (3, 1), (41, 1), (38713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_38713
  · decide +kernel

theorem prime_42599429 : Nat.Prime 42599429 := by
  apply nodeValid_prime [2, 1129, 9433] ⟨42599429, 2, [(2, 2), (1129, 1), (9433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1129
    · exact prime_9433
  · decide +kernel

theorem prime_69627037 : Nat.Prime 69627037 := by
  apply nodeValid_prime [2, 3, 17, 1181] ⟨69627037, 5, [(2, 2), (3, 1), (17, 3), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1181
  · decide +kernel

theorem prime_123581473 : Nat.Prime 123581473 := by
  apply nodeValid_prime [2, 3, 7, 19, 9679] ⟨123581473, 13, [(2, 5), (3, 1), (7, 1), (19, 1), (9679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_9679
  · decide +kernel

theorem prime_126551899 : Nat.Prime 126551899 := by
  apply nodeValid_prime [2, 3, 11, 639151] ⟨126551899, 2, [(2, 1), (3, 2), (11, 1), (639151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_639151
  · decide +kernel

theorem prime_168864877 : Nat.Prime 168864877 := by
  apply nodeValid_prime [2, 3, 17, 275923] ⟨168864877, 2, [(2, 2), (3, 2), (17, 1), (275923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_275923
  · decide +kernel

theorem prime_275518063 : Nat.Prime 275518063 := by
  apply nodeValid_prime [2, 3, 53, 288803] ⟨275518063, 3, [(2, 1), (3, 2), (53, 1), (288803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_288803
  · decide +kernel

theorem prime_322243393 : Nat.Prime 322243393 := by
  apply nodeValid_prime [2, 3, 53, 31667] ⟨322243393, 5, [(2, 6), (3, 1), (53, 1), (31667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_31667
  · decide +kernel

theorem prime_405587233 : Nat.Prime 405587233 := by
  apply nodeValid_prime [2, 3, 1408289] ⟨405587233, 10, [(2, 5), (3, 2), (1408289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1408289
  · decide +kernel

theorem prime_436060237 : Nat.Prime 436060237 := by
  apply nodeValid_prime [2, 3, 139, 261427] ⟨436060237, 2, [(2, 2), (3, 1), (139, 1), (261427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_261427
  · decide +kernel

theorem prime_465146813 : Nat.Prime 465146813 := by
  apply nodeValid_prime [2, 13, 688087] ⟨465146813, 2, [(2, 2), (13, 2), (688087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_688087
  · decide +kernel

theorem prime_560383553 : Nat.Prime 560383553 := by
  apply nodeValid_prime [2, 101, 86693] ⟨560383553, 3, [(2, 6), (101, 1), (86693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_86693
  · decide +kernel

theorem prime_675459509 : Nat.Prime 675459509 := by
  apply nodeValid_prime [2, 168864877] ⟨675459509, 2, [(2, 2), (168864877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_168864877
  · decide +kernel

theorem prime_1039584619 : Nat.Prime 1039584619 := by
  apply nodeValid_prime [2, 3, 713021] ⟨1039584619, 2, [(2, 1), (3, 6), (713021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_713021
  · decide +kernel

theorem prime_1084504051 : Nat.Prime 1084504051 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 14969] ⟨1084504051, 2, [(2, 1), (3, 2), (5, 2), (7, 1), (23, 1), (14969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_14969
  · decide +kernel

theorem prime_1102072253 : Nat.Prime 1102072253 := by
  apply nodeValid_prime [2, 275518063] ⟨1102072253, 2, [(2, 2), (275518063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_275518063
  · decide +kernel

theorem prime_1852115257 : Nat.Prime 1852115257 := by
  apply nodeValid_prime [2, 3, 59, 435997] ⟨1852115257, 7, [(2, 3), (3, 2), (59, 1), (435997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_435997
  · decide +kernel

theorem prime_3844854311 : Nat.Prime 3844854311 := by
  apply nodeValid_prime [2, 5, 11, 137, 255133] ⟨3844854311, 7, [(2, 1), (5, 1), (11, 1), (137, 1), (255133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_137
    · exact prime_255133
  · decide +kernel

theorem prime_3902654797 : Nat.Prime 3902654797 := by
  apply nodeValid_prime [2, 3, 19, 151, 113357] ⟨3902654797, 2, [(2, 2), (3, 1), (19, 1), (151, 1), (113357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_151
    · exact prime_113357
  · decide +kernel

theorem prime_11809044127 : Nat.Prime 11809044127 := by
  apply nodeValid_prime [2, 3, 11, 47, 115361] ⟨11809044127, 3, [(2, 1), (3, 2), (11, 2), (47, 1), (115361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_115361
  · decide +kernel

theorem prime_15215663963 : Nat.Prime 15215663963 := by
  apply nodeValid_prime [2, 479, 15882739] ⟨15215663963, 2, [(2, 1), (479, 1), (15882739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_15882739
  · decide +kernel

theorem prime_15810779147 : Nat.Prime 15810779147 := by
  apply nodeValid_prime [2, 18353, 430741] ⟨15810779147, 2, [(2, 1), (18353, 1), (430741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18353
    · exact prime_430741
  · decide +kernel

theorem prime_21439284931 : Nat.Prime 21439284931 := by
  apply nodeValid_prime [2, 3, 5, 7, 53, 7927] ⟨21439284931, 3, [(2, 1), (3, 6), (5, 1), (7, 1), (53, 1), (7927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_7927
  · decide +kernel

theorem prime_21994722907 : Nat.Prime 21994722907 := by
  apply nodeValid_prime [2, 3, 13, 79, 107, 33359] ⟨21994722907, 3, [(2, 1), (3, 1), (13, 1), (79, 1), (107, 1), (33359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_79
    · exact prime_107
    · exact prime_33359
  · decide +kernel

theorem prime_27086933399 : Nat.Prime 27086933399 := by
  apply nodeValid_prime [2, 7, 29803, 64919] ⟨27086933399, 7, [(2, 1), (7, 1), (29803, 1), (64919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29803
    · exact prime_64919
  · decide +kernel

theorem prime_35199535067 : Nat.Prime 35199535067 := by
  apply nodeValid_prime [2, 47, 89, 1019, 4129] ⟨35199535067, 2, [(2, 1), (47, 1), (89, 1), (1019, 1), (4129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_89
    · exact prime_1019
    · exact prime_4129
  · decide +kernel

theorem prime_36813724751 : Nat.Prime 36813724751 := by
  apply nodeValid_prime [2, 5, 11, 13386809] ⟨36813724751, 11, [(2, 1), (5, 3), (11, 1), (13386809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13386809
  · decide +kernel

theorem prime_53254822963 : Nat.Prime 53254822963 := by
  apply nodeValid_prime [2, 3, 11, 59, 1697, 8059] ⟨53254822963, 2, [(2, 1), (3, 1), (11, 1), (59, 1), (1697, 1), (8059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_1697
    · exact prime_8059
  · decide +kernel

theorem prime_109042531583 : Nat.Prime 109042531583 := by
  apply nodeValid_prime [2, 23, 109, 21747613] ⟨109042531583, 5, [(2, 1), (23, 1), (109, 1), (21747613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_109
    · exact prime_21747613
  · decide +kernel

theorem prime_210290159839 : Nat.Prime 210290159839 := by
  apply nodeValid_prime [2, 3, 11, 29, 167, 307, 2143] ⟨210290159839, 3, [(2, 1), (3, 1), (11, 1), (29, 1), (167, 1), (307, 1), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_167
    · exact prime_307
    · exact prime_2143
  · decide +kernel

theorem prime_210290198269 : Nat.Prime 210290198269 := by
  apply nodeValid_prime [2, 3, 19, 11489, 80279] ⟨210290198269, 2, [(2, 2), (3, 1), (19, 1), (11489, 1), (80279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11489
    · exact prime_80279
  · decide +kernel

theorem prime_210290198759 : Nat.Prime 210290198759 := by
  apply nodeValid_prime [2, 41, 89, 28814771] ⟨210290198759, 7, [(2, 1), (41, 1), (89, 1), (28814771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_89
    · exact prime_28814771
  · decide +kernel

theorem prime_210743359039 : Nat.Prime 210743359039 := by
  apply nodeValid_prime [2, 3, 3902654797] ⟨210743359039, 3, [(2, 1), (3, 3), (3902654797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3902654797
  · decide +kernel

theorem prime_210743366809 : Nat.Prime 210743366809 := by
  apply nodeValid_prime [2, 3, 13, 675459509] ⟨210743366809, 7, [(2, 3), (3, 1), (13, 1), (675459509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_675459509
  · decide +kernel

theorem prime_210743367187 : Nat.Prime 210743367187 := by
  apply nodeValid_prime [2, 3, 11, 17, 547, 343379] ⟨210743367187, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (547, 1), (343379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_547
    · exact prime_343379
  · decide +kernel

theorem prime_211197208231 : Nat.Prime 211197208231 := by
  apply nodeValid_prime [2, 3, 5, 17, 263, 524857] ⟨211197208231, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (263, 1), (524857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_263
    · exact prime_524857
  · decide +kernel

theorem prime_211197210403 : Nat.Prime 211197210403 := by
  apply nodeValid_prime [2, 3, 35199535067] ⟨211197210403, 2, [(2, 1), (3, 1), (35199535067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35199535067
  · decide +kernel

theorem prime_211197218461 : Nat.Prime 211197218461 := by
  apply nodeValid_prime [2, 3, 5, 43, 107, 765041] ⟨211197218461, 2, [(2, 2), (3, 1), (5, 1), (43, 1), (107, 1), (765041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_107
    · exact prime_765041
  · decide +kernel

theorem prime_211651741261 : Nat.Prime 211651741261 := by
  apply nodeValid_prime [2, 3, 5, 23, 1893467] ⟨211651741261, 2, [(2, 2), (3, 5), (5, 1), (23, 1), (1893467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1893467
  · decide +kernel

theorem prime_211651766971 : Nat.Prime 211651766971 := by
  apply nodeValid_prime [2, 3, 5, 7, 109, 9246473] ⟨211651766971, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (109, 1), (9246473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_109
    · exact prime_9246473
  · decide +kernel

theorem prime_211651767001 : Nat.Prime 211651767001 := by
  apply nodeValid_prime [2, 3, 5, 1543, 15241] ⟨211651767001, 7, [(2, 3), (3, 2), (5, 3), (1543, 1), (15241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1543
    · exact prime_15241
  · decide +kernel

theorem prime_212106926543 : Nat.Prime 212106926543 := by
  apply nodeValid_prime [2, 7, 2267, 6683059] ⟨212106926543, 5, [(2, 1), (7, 1), (2267, 1), (6683059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2267
    · exact prime_6683059
  · decide +kernel

theorem prime_212106945917 : Nat.Prime 212106945917 := by
  apply nodeValid_prime [2, 1847, 2269, 12653] ⟨212106945917, 2, [(2, 2), (1847, 1), (2269, 1), (12653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1847
    · exact prime_2269
    · exact prime_12653
  · decide +kernel

theorem prime_212106946729 : Nat.Prime 212106946729 := by
  apply nodeValid_prime [2, 3, 19, 465146813] ⟨212106946729, 13, [(2, 3), (3, 1), (19, 1), (465146813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_465146813
  · decide +kernel

theorem prime_212562777887 : Nat.Prime 212562777887 := by
  apply nodeValid_prime [2, 163, 1709, 381529] ⟨212562777887, 5, [(2, 1), (163, 1), (1709, 1), (381529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_1709
    · exact prime_381529
  · decide +kernel

theorem prime_212562793997 : Nat.Prime 212562793997 := by
  apply nodeValid_prime [2, 7, 1084504051] ⟨212562793997, 2, [(2, 2), (7, 2), (1084504051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1084504051
  · decide +kernel

theorem prime_212562794287 : Nat.Prime 212562794287 := by
  apply nodeValid_prime [2, 3, 11809044127] ⟨212562794287, 3, [(2, 1), (3, 2), (11809044127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11809044127
  · decide +kernel

theorem prime_213019290769 : Nat.Prime 213019290769 := by
  apply nodeValid_prime [2, 3, 311, 14269781] ⟨213019290769, 11, [(2, 4), (3, 1), (311, 1), (14269781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_14269781
  · decide +kernel

theorem prime_213019291853 : Nat.Prime 213019291853 := by
  apply nodeValid_prime [2, 53254822963] ⟨213019291853, 2, [(2, 2), (53254822963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53254822963
  · decide +kernel

theorem prime_213019295483 : Nat.Prime 213019295483 := by
  apply nodeValid_prime [2, 7, 15215663963] ⟨213019295483, 2, [(2, 1), (7, 1), (15215663963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15215663963
  · decide +kernel

theorem prime_213476478673 : Nat.Prime 213476478673 := by
  apply nodeValid_prime [2, 3, 7297, 609487] ⟨213476478673, 5, [(2, 4), (3, 1), (7297, 1), (609487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7297
    · exact prime_609487
  · decide +kernel

theorem prime_213476495173 : Nat.Prime 213476495173 := by
  apply nodeValid_prime [2, 3, 467, 38093593] ⟨213476495173, 2, [(2, 2), (3, 1), (467, 1), (38093593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_38093593
  · decide +kernel

theorem prime_213476495443 : Nat.Prime 213476495443 := by
  apply nodeValid_prime [2, 3, 7, 73, 69627037] ⟨213476495443, 2, [(2, 1), (3, 1), (7, 1), (73, 1), (69627037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_69627037
  · decide +kernel

theorem prime_213934323641 : Nat.Prime 213934323641 := by
  apply nodeValid_prime [2, 5, 47, 131, 868663] ⟨213934323641, 3, [(2, 3), (5, 1), (47, 1), (131, 1), (868663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_131
    · exact prime_868663
  · decide +kernel

theorem prime_213934323749 : Nat.Prime 213934323749 := by
  apply nodeValid_prime [2, 10169, 5259473] ⟨213934323749, 2, [(2, 2), (10169, 1), (5259473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10169
    · exact prime_5259473
  · decide +kernel

theorem prime_213934332439 : Nat.Prime 213934332439 := by
  apply nodeValid_prime [2, 3, 31, 42599429] ⟨213934332439, 6, [(2, 1), (3, 4), (31, 1), (42599429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_42599429
  · decide +kernel

theorem prime_214392835739 : Nat.Prime 214392835739 := by
  apply nodeValid_prime [2, 673, 4597, 34649] ⟨214392835739, 2, [(2, 1), (673, 1), (4597, 1), (34649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_673
    · exact prime_4597
    · exact prime_34649
  · decide +kernel

theorem prime_214392835817 : Nat.Prime 214392835817 := by
  apply nodeValid_prime [2, 19, 37, 2423, 15733] ⟨214392835817, 3, [(2, 3), (19, 1), (37, 1), (2423, 1), (15733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_2423
    · exact prime_15733
  · decide +kernel

theorem prime_214392849311 : Nat.Prime 214392849311 := by
  apply nodeValid_prime [2, 5, 21439284931] ⟨214392849311, 11, [(2, 1), (5, 1), (21439284931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_21439284931
  · decide +kernel

theorem prime_214852018543 : Nat.Prime 214852018543 := by
  apply nodeValid_prime [2, 3, 7, 193, 4159, 6373] ⟨214852018543, 5, [(2, 1), (3, 1), (7, 1), (193, 1), (4159, 1), (6373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_193
    · exact prime_4159
    · exact prime_6373
  · decide +kernel

theorem prime_214852019639 : Nat.Prime 214852019639 := by
  apply nodeValid_prime [2, 1583, 2689, 25237] ⟨214852019639, 11, [(2, 1), (1583, 1), (2689, 1), (25237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1583
    · exact prime_2689
    · exact prime_25237
  · decide +kernel

theorem prime_214852033379 : Nat.Prime 214852033379 := by
  apply nodeValid_prime [2, 6569, 16353481] ⟨214852033379, 2, [(2, 1), (6569, 1), (16353481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6569
    · exact prime_16353481
  · decide +kernel

theorem prime_215311841417 : Nat.Prime 215311841417 := by
  apply nodeValid_prime [2, 7, 3844854311] ⟨215311841417, 3, [(2, 3), (7, 1), (3844854311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3844854311
  · decide +kernel

theorem prime_215311842071 : Nat.Prime 215311842071 := by
  apply nodeValid_prime [2, 5, 13, 31469, 52631] ⟨215311842071, 7, [(2, 1), (5, 1), (13, 1), (31469, 1), (52631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31469
    · exact prime_52631
  · decide +kernel

theorem prime_215311885249 : Nat.Prime 215311885249 := by
  apply nodeValid_prime [2, 3, 853, 1314673] ⟨215311885249, 7, [(2, 6), (3, 1), (853, 1), (1314673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853
    · exact prime_1314673
  · decide +kernel

theorem prime_215772406363 : Nat.Prime 215772406363 := by
  apply nodeValid_prime [2, 3, 13859, 288317] ⟨215772406363, 5, [(2, 1), (3, 3), (13859, 1), (288317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13859
    · exact prime_288317
  · decide +kernel

theorem prime_215772407957 : Nat.Prime 215772407957 := by
  apply nodeValid_prime [2, 7, 19, 405587233] ⟨215772407957, 2, [(2, 2), (7, 1), (19, 1), (405587233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_405587233
  · decide +kernel

theorem prime_215772408389 : Nat.Prime 215772408389 := by
  apply nodeValid_prime [2, 41, 227, 5795971] ⟨215772408389, 2, [(2, 2), (41, 1), (227, 1), (5795971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_227
    · exact prime_5795971
  · decide +kernel

theorem prime_216233600753 : Nat.Prime 216233600753 := by
  apply nodeValid_prime [2, 13, 1039584619] ⟨216233600753, 3, [(2, 4), (13, 1), (1039584619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1039584619
  · decide +kernel

theorem prime_216233602367 : Nat.Prime 216233602367 := by
  apply nodeValid_prime [2, 19, 73, 131, 595039] ⟨216233602367, 5, [(2, 1), (19, 1), (73, 1), (131, 1), (595039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
    · exact prime_131
    · exact prime_595039
  · decide +kernel

theorem prime_216233602813 : Nat.Prime 216233602813 := by
  apply nodeValid_prime [2, 3, 239, 433, 6449] ⟨216233602813, 2, [(2, 2), (3, 4), (239, 1), (433, 1), (6449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_433
    · exact prime_6449
  · decide +kernel

theorem prime_216695467193 : Nat.Prime 216695467193 := by
  apply nodeValid_prime [2, 27086933399] ⟨216695467193, 3, [(2, 3), (27086933399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27086933399
  · decide +kernel

theorem prime_216695473331 : Nat.Prime 216695473331 := by
  apply nodeValid_prime [2, 5, 7, 503, 607, 10139] ⟨216695473331, 2, [(2, 1), (5, 1), (7, 1), (503, 1), (607, 1), (10139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_503
    · exact prime_607
    · exact prime_10139
  · decide +kernel

theorem prime_216695473411 : Nat.Prime 216695473411 := by
  apply nodeValid_prime [2, 3, 5, 13, 61, 9108679] ⟨216695473411, 19, [(2, 1), (3, 1), (5, 1), (13, 1), (61, 1), (9108679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_61
    · exact prime_9108679
  · decide +kernel

theorem prime_217157998027 : Nat.Prime 217157998027 := by
  apply nodeValid_prime [2, 3, 83, 436060237] ⟨217157998027, 11, [(2, 1), (3, 1), (83, 1), (436060237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_436060237
  · decide +kernel

theorem prime_217157999291 : Nat.Prime 217157999291 := by
  apply nodeValid_prime [2, 5, 43, 157, 1429, 2251] ⟨217157999291, 2, [(2, 1), (5, 1), (43, 1), (157, 1), (1429, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_157
    · exact prime_1429
    · exact prime_2251
  · decide +kernel

theorem prime_217158000541 : Nat.Prime 217158000541 := by
  apply nodeValid_prime [2, 3, 5, 13, 577, 482509] ⟨217158000541, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (577, 1), (482509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_577
    · exact prime_482509
  · decide +kernel

theorem prime_217621191937 : Nat.Prime 217621191937 := by
  apply nodeValid_prime [2, 3, 19, 43, 346831] ⟨217621191937, 5, [(2, 8), (3, 1), (19, 1), (43, 1), (346831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_43
    · exact prime_346831
  · decide +kernel

theorem prime_217621192111 : Nat.Prime 217621192111 := by
  apply nodeValid_prime [2, 3, 5, 7, 47, 1637, 13469] ⟨217621192111, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (47, 1), (1637, 1), (13469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_1637
    · exact prime_13469
  · decide +kernel

theorem prime_217621197361 : Nat.Prime 217621197361 := by
  apply nodeValid_prime [2, 3, 5, 7, 709, 60901] ⟨217621197361, 11, [(2, 4), (3, 2), (5, 1), (7, 1), (709, 1), (60901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_709
    · exact prime_60901
  · decide +kernel

theorem prime_218085028079 : Nat.Prime 218085028079 := by
  apply nodeValid_prime [2, 29, 593, 6340787] ⟨218085028079, 7, [(2, 1), (29, 1), (593, 1), (6340787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_593
    · exact prime_6340787
  · decide +kernel

theorem prime_218085029027 : Nat.Prime 218085029027 := by
  apply nodeValid_prime [2, 157, 373, 1862033] ⟨218085029027, 2, [(2, 1), (157, 1), (373, 1), (1862033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_373
    · exact prime_1862033
  · decide +kernel

theorem prime_218085063167 : Nat.Prime 218085063167 := by
  apply nodeValid_prime [2, 109042531583] ⟨218085063167, 5, [(2, 1), (109042531583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_109042531583
  · decide +kernel

theorem prime_218549585647 : Nat.Prime 218549585647 := by
  apply nodeValid_prime [2, 3, 7, 37, 1301, 12011] ⟨218549585647, 3, [(2, 1), (3, 3), (7, 1), (37, 1), (1301, 1), (12011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_1301
    · exact prime_12011
  · decide +kernel

theorem prime_218549585671 : Nat.Prime 218549585671 := by
  apply nodeValid_prime [2, 3, 5, 13, 560383553] ⟨218549585671, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (560383553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_560383553
  · decide +kernel

theorem prime_218549600327 : Nat.Prime 218549600327 := by
  apply nodeValid_prime [2, 59, 1852115257] ⟨218549600327, 5, [(2, 1), (59, 1), (1852115257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_1852115257
  · decide +kernel

theorem prime_219014798173 : Nat.Prime 219014798173 := by
  apply nodeValid_prime [2, 3, 23957, 761833] ⟨219014798173, 2, [(2, 2), (3, 1), (23957, 1), (761833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23957
    · exact prime_761833
  · decide +kernel

theorem prime_219014798533 : Nat.Prime 219014798533 := by
  apply nodeValid_prime [2, 3, 107, 12799, 13327] ⟨219014798533, 5, [(2, 2), (3, 1), (107, 1), (12799, 1), (13327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_12799
    · exact prime_13327
  · decide +kernel

theorem prime_219014808073 : Nat.Prime 219014808073 := by
  apply nodeValid_prime [2, 3, 1039, 8783077] ⟨219014808073, 5, [(2, 3), (3, 1), (1039, 1), (8783077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1039
    · exact prime_8783077
  · decide +kernel

theorem prime_219480683999 : Nat.Prime 219480683999 := by
  apply nodeValid_prime [2, 17599, 6235601] ⟨219480683999, 11, [(2, 1), (17599, 1), (6235601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17599
    · exact prime_6235601
  · decide +kernel

theorem prime_219480696049 : Nat.Prime 219480696049 := by
  apply nodeValid_prime [2, 3, 37, 123581473] ⟨219480696049, 11, [(2, 4), (3, 1), (37, 1), (123581473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_123581473
  · decide +kernel

theorem prime_219480696163 : Nat.Prime 219480696163 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 47, 67, 2503] ⟨219480696163, 5, [(2, 1), (3, 2), (7, 1), (13, 1), (17, 1), (47, 1), (67, 1), (2503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_47
    · exact prime_67
    · exact prime_2503
  · decide +kernel

theorem prime_219947200223 : Nat.Prime 219947200223 := by
  apply nodeValid_prime [2, 53, 1427, 1454081] ⟨219947200223, 5, [(2, 1), (53, 1), (1427, 1), (1454081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1427
    · exact prime_1454081
  · decide +kernel

theorem prime_219947200463 : Nat.Prime 219947200463 := by
  apply nodeValid_prime [2, 11, 79, 126551899] ⟨219947200463, 5, [(2, 1), (11, 1), (79, 1), (126551899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79
    · exact prime_126551899
  · decide +kernel

theorem prime_219947229071 : Nat.Prime 219947229071 := by
  apply nodeValid_prime [2, 5, 21994722907] ⟨219947229071, 11, [(2, 1), (5, 1), (21994722907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_21994722907
  · decide +kernel

theorem prime_220414450601 : Nat.Prime 220414450601 := by
  apply nodeValid_prime [2, 5, 1102072253] ⟨220414450601, 3, [(2, 3), (5, 2), (1102072253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1102072253
  · decide +kernel

theorem prime_220414480813 : Nat.Prime 220414480813 := by
  apply nodeValid_prime [2, 3, 19, 322243393] ⟨220414480813, 2, [(2, 2), (3, 2), (19, 1), (322243393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_322243393
  · decide +kernel

theorem prime_220882344647 : Nat.Prime 220882344647 := by
  apply nodeValid_prime [2, 23, 29, 107, 281, 5507] ⟨220882344647, 5, [(2, 1), (23, 1), (29, 1), (107, 1), (281, 1), (5507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_107
    · exact prime_281
    · exact prime_5507
  · decide +kernel

theorem prime_220882346677 : Nat.Prime 220882346677 := by
  apply nodeValid_prime [2, 3, 29, 421, 502549] ⟨220882346677, 7, [(2, 2), (3, 2), (29, 1), (421, 1), (502549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_421
    · exact prime_502549
  · decide +kernel

theorem prime_220882348507 : Nat.Prime 220882348507 := by
  apply nodeValid_prime [2, 3, 36813724751] ⟨220882348507, 2, [(2, 1), (3, 1), (36813724751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36813724751
  · decide +kernel

theorem prime_221350908059 : Nat.Prime 221350908059 := by
  apply nodeValid_prime [2, 7, 15810779147] ⟨221350908059, 2, [(2, 1), (7, 1), (15810779147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15810779147
  · decide +kernel

theorem prime_221350918493 : Nat.Prime 221350918493 := by
  apply nodeValid_prime [2, 11, 269, 3253, 5749] ⟨221350918493, 2, [(2, 2), (11, 1), (269, 1), (3253, 1), (5749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_269
    · exact prime_3253
    · exact prime_5749
  · decide +kernel

theorem prime_221350920971 : Nat.Prime 221350920971 := by
  apply nodeValid_prime [2, 5, 17, 8329, 156329] ⟨221350920971, 2, [(2, 1), (5, 1), (17, 1), (8329, 1), (156329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_8329
    · exact prime_156329
  · decide +kernel

end Sude.Lucas.Generated
