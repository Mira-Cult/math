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
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3259 : Nat.Prime 3259 := by
  apply nodeValid_prime [2, 3, 181] ⟨3259, 3, [(2, 1), (3, 2), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel

theorem prime_4783 : Nat.Prime 4783 := by
  apply nodeValid_prime [2, 3, 797] ⟨4783, 6, [(2, 1), (3, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_797
  · decide +kernel

theorem prime_4799 : Nat.Prime 4799 := by
  apply nodeValid_prime [2, 2399] ⟨4799, 7, [(2, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2399
  · decide +kernel

theorem prime_4937 : Nat.Prime 4937 := by
  apply nodeValid_prime [2, 617] ⟨4937, 3, [(2, 3), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_617
  · decide +kernel

theorem prime_4957 : Nat.Prime 4957 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨4957, 2, [(2, 2), (3, 1), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_4993 : Nat.Prime 4993 := by
  apply nodeValid_prime [2, 3, 13] ⟨4993, 5, [(2, 7), (3, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_5099 : Nat.Prime 5099 := by
  apply nodeValid_prime [2, 2549] ⟨5099, 2, [(2, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2549
  · decide +kernel

theorem prime_5231 : Nat.Prime 5231 := by
  apply nodeValid_prime [2, 5, 523] ⟨5231, 7, [(2, 1), (5, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_523
  · decide +kernel

theorem prime_5861 : Nat.Prime 5861 := by
  apply nodeValid_prime [2, 5, 293] ⟨5861, 3, [(2, 2), (5, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_293
  · decide +kernel

theorem prime_6067 : Nat.Prime 6067 := by
  apply nodeValid_prime [2, 3, 337] ⟨6067, 2, [(2, 1), (3, 2), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
  · decide +kernel

theorem prime_6173 : Nat.Prime 6173 := by
  apply nodeValid_prime [2, 1543] ⟨6173, 2, [(2, 2), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1543
  · decide +kernel

theorem prime_10253 : Nat.Prime 10253 := by
  apply nodeValid_prime [2, 11, 233] ⟨10253, 2, [(2, 2), (11, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_233
  · decide +kernel

theorem prime_12829 : Nat.Prime 12829 := by
  apply nodeValid_prime [2, 3, 1069] ⟨12829, 2, [(2, 2), (3, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
  · decide +kernel

theorem prime_13931 : Nat.Prime 13931 := by
  apply nodeValid_prime [2, 5, 7, 199] ⟨13931, 2, [(2, 1), (5, 1), (7, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_199
  · decide +kernel

theorem prime_14321 : Nat.Prime 14321 := by
  apply nodeValid_prime [2, 5, 179] ⟨14321, 3, [(2, 4), (5, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
  · decide +kernel

theorem prime_14327 : Nat.Prime 14327 := by
  apply nodeValid_prime [2, 13, 19, 29] ⟨14327, 5, [(2, 1), (13, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_14831 : Nat.Prime 14831 := by
  apply nodeValid_prime [2, 5, 1483] ⟨14831, 11, [(2, 1), (5, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1483
  · decide +kernel

theorem prime_16007 : Nat.Prime 16007 := by
  apply nodeValid_prime [2, 53, 151] ⟨16007, 5, [(2, 1), (53, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_151
  · decide +kernel

theorem prime_16993 : Nat.Prime 16993 := by
  apply nodeValid_prime [2, 3, 59] ⟨16993, 10, [(2, 5), (3, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_17351 : Nat.Prime 17351 := by
  apply nodeValid_prime [2, 5, 347] ⟨17351, 11, [(2, 1), (5, 2), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_347
  · decide +kernel

theorem prime_20753 : Nat.Prime 20753 := by
  apply nodeValid_prime [2, 1297] ⟨20753, 3, [(2, 4), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1297
  · decide +kernel

theorem prime_21881 : Nat.Prime 21881 := by
  apply nodeValid_prime [2, 5, 547] ⟨21881, 3, [(2, 3), (5, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_547
  · decide +kernel

theorem prime_23669 : Nat.Prime 23669 := by
  apply nodeValid_prime [2, 61, 97] ⟨23669, 2, [(2, 2), (61, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_97
  · decide +kernel

theorem prime_24097 : Nat.Prime 24097 := by
  apply nodeValid_prime [2, 3, 251] ⟨24097, 5, [(2, 5), (3, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
  · decide +kernel

theorem prime_24413 : Nat.Prime 24413 := by
  apply nodeValid_prime [2, 17, 359] ⟨24413, 2, [(2, 2), (17, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_359
  · decide +kernel

theorem prime_25391 : Nat.Prime 25391 := by
  apply nodeValid_prime [2, 5, 2539] ⟨25391, 7, [(2, 1), (5, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2539
  · decide +kernel

theorem prime_29527 : Nat.Prime 29527 := by
  apply nodeValid_prime [2, 3, 7, 19, 37] ⟨29527, 3, [(2, 1), (3, 1), (7, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_29663 : Nat.Prime 29663 := by
  apply nodeValid_prime [2, 14831] ⟨29663, 5, [(2, 1), (14831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14831
  · decide +kernel

theorem prime_32693 : Nat.Prime 32693 := by
  apply nodeValid_prime [2, 11, 743] ⟨32693, 2, [(2, 2), (11, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_743
  · decide +kernel

theorem prime_33211 : Nat.Prime 33211 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨33211, 2, [(2, 1), (3, 4), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_37831 : Nat.Prime 37831 := by
  apply nodeValid_prime [2, 3, 5, 13, 97] ⟨37831, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_38791 : Nat.Prime 38791 := by
  apply nodeValid_prime [2, 3, 5, 431] ⟨38791, 6, [(2, 1), (3, 2), (5, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_431
  · decide +kernel

theorem prime_38933 : Nat.Prime 38933 := by
  apply nodeValid_prime [2, 9733] ⟨38933, 2, [(2, 2), (9733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9733
  · decide +kernel

theorem prime_39499 : Nat.Prime 39499 := by
  apply nodeValid_prime [2, 3, 29, 227] ⟨39499, 2, [(2, 1), (3, 1), (29, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_227
  · decide +kernel

theorem prime_41507 : Nat.Prime 41507 := by
  apply nodeValid_prime [2, 20753] ⟨41507, 2, [(2, 1), (20753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20753
  · decide +kernel

theorem prime_43691 : Nat.Prime 43691 := by
  apply nodeValid_prime [2, 5, 17, 257] ⟨43691, 6, [(2, 1), (5, 1), (17, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_257
  · decide +kernel

theorem prime_47501 : Nat.Prime 47501 := by
  apply nodeValid_prime [2, 5, 19] ⟨47501, 3, [(2, 2), (5, 4), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_49549 : Nat.Prime 49549 := by
  apply nodeValid_prime [2, 3, 4129] ⟨49549, 6, [(2, 2), (3, 1), (4129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4129
  · decide +kernel

theorem prime_61519 : Nat.Prime 61519 := by
  apply nodeValid_prime [2, 3, 10253] ⟨61519, 3, [(2, 1), (3, 1), (10253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10253
  · decide +kernel

theorem prime_67021 : Nat.Prime 67021 := by
  apply nodeValid_prime [2, 3, 5, 1117] ⟨67021, 7, [(2, 2), (3, 1), (5, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1117
  · decide +kernel

theorem prime_67531 : Nat.Prime 67531 := by
  apply nodeValid_prime [2, 3, 5, 2251] ⟨67531, 10, [(2, 1), (3, 1), (5, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2251
  · decide +kernel

theorem prime_73309 : Nat.Prime 73309 := by
  apply nodeValid_prime [2, 3, 41, 149] ⟨73309, 2, [(2, 2), (3, 1), (41, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_149
  · decide +kernel

theorem prime_76991 : Nat.Prime 76991 := by
  apply nodeValid_prime [2, 5, 7699] ⟨76991, 13, [(2, 1), (5, 1), (7699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7699
  · decide +kernel

theorem prime_78713 : Nat.Prime 78713 := by
  apply nodeValid_prime [2, 9839] ⟨78713, 3, [(2, 3), (9839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9839
  · decide +kernel

theorem prime_79613 : Nat.Prime 79613 := by
  apply nodeValid_prime [2, 13, 1531] ⟨79613, 2, [(2, 2), (13, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1531
  · decide +kernel

theorem prime_102677 : Nat.Prime 102677 := by
  apply nodeValid_prime [2, 7, 19, 193] ⟨102677, 3, [(2, 2), (7, 1), (19, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_193
  · decide +kernel

theorem prime_111509 : Nat.Prime 111509 := by
  apply nodeValid_prime [2, 61, 457] ⟨111509, 2, [(2, 2), (61, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_457
  · decide +kernel

theorem prime_112121 : Nat.Prime 112121 := by
  apply nodeValid_prime [2, 5, 2803] ⟨112121, 3, [(2, 3), (5, 1), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2803
  · decide +kernel

theorem prime_112327 : Nat.Prime 112327 := by
  apply nodeValid_prime [2, 3, 97, 193] ⟨112327, 5, [(2, 1), (3, 1), (97, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_193
  · decide +kernel

theorem prime_113497 : Nat.Prime 113497 := by
  apply nodeValid_prime [2, 3, 4729] ⟨113497, 5, [(2, 3), (3, 1), (4729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4729
  · decide +kernel

theorem prime_121867 : Nat.Prime 121867 := by
  apply nodeValid_prime [2, 3, 19, 1069] ⟨121867, 3, [(2, 1), (3, 1), (19, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1069
  · decide +kernel

theorem prime_127643 : Nat.Prime 127643 := by
  apply nodeValid_prime [2, 19, 3359] ⟨127643, 2, [(2, 1), (19, 1), (3359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3359
  · decide +kernel

theorem prime_136949 : Nat.Prime 136949 := by
  apply nodeValid_prime [2, 7, 67, 73] ⟨136949, 3, [(2, 2), (7, 1), (67, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_73
  · decide +kernel

theorem prime_144583 : Nat.Prime 144583 := by
  apply nodeValid_prime [2, 3, 24097] ⟨144583, 3, [(2, 1), (3, 1), (24097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24097
  · decide +kernel

theorem prime_157427 : Nat.Prime 157427 := by
  apply nodeValid_prime [2, 78713] ⟨157427, 2, [(2, 1), (78713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_78713
  · decide +kernel

theorem prime_168943 : Nat.Prime 168943 := by
  apply nodeValid_prime [2, 3, 37, 761] ⟨168943, 5, [(2, 1), (3, 1), (37, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_761
  · decide +kernel

theorem prime_174799 : Nat.Prime 174799 := by
  apply nodeValid_prime [2, 3, 13, 83] ⟨174799, 6, [(2, 1), (3, 4), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_179749 : Nat.Prime 179749 := by
  apply nodeValid_prime [2, 3, 4993] ⟨179749, 2, [(2, 2), (3, 2), (4993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4993
  · decide +kernel

theorem prime_211661 : Nat.Prime 211661 := by
  apply nodeValid_prime [2, 5, 19, 557] ⟨211661, 2, [(2, 2), (5, 1), (19, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_557
  · decide +kernel

theorem prime_220217 : Nat.Prime 220217 := by
  apply nodeValid_prime [2, 27527] ⟨220217, 3, [(2, 3), (27527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27527
  · decide +kernel

theorem prime_223019 : Nat.Prime 223019 := by
  apply nodeValid_prime [2, 111509] ⟨223019, 2, [(2, 1), (111509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_111509
  · decide +kernel

theorem prime_235553 : Nat.Prime 235553 := by
  apply nodeValid_prime [2, 17, 433] ⟨235553, 3, [(2, 5), (17, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_433
  · decide +kernel

theorem prime_237971 : Nat.Prime 237971 := by
  apply nodeValid_prime [2, 5, 53, 449] ⟨237971, 6, [(2, 1), (5, 1), (53, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_449
  · decide +kernel

theorem prime_239137 : Nat.Prime 239137 := by
  apply nodeValid_prime [2, 3, 47, 53] ⟨239137, 5, [(2, 5), (3, 1), (47, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_53
  · decide +kernel

theorem prime_264619 : Nat.Prime 264619 := by
  apply nodeValid_prime [2, 3, 61, 241] ⟨264619, 3, [(2, 1), (3, 2), (61, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_241
  · decide +kernel

theorem prime_283093 : Nat.Prime 283093 := by
  apply nodeValid_prime [2, 3, 31, 761] ⟨283093, 5, [(2, 2), (3, 1), (31, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_761
  · decide +kernel

theorem prime_292021 : Nat.Prime 292021 := by
  apply nodeValid_prime [2, 3, 5, 31, 157] ⟨292021, 2, [(2, 2), (3, 1), (5, 1), (31, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_157
  · decide +kernel

theorem prime_323419 : Nat.Prime 323419 := by
  apply nodeValid_prime [2, 3, 19, 2837] ⟨323419, 3, [(2, 1), (3, 1), (19, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2837
  · decide +kernel

theorem prime_355427 : Nat.Prime 355427 := by
  apply nodeValid_prime [2, 71, 2503] ⟨355427, 2, [(2, 1), (71, 1), (2503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2503
  · decide +kernel

theorem prime_429529 : Nat.Prime 429529 := by
  apply nodeValid_prime [2, 3, 11, 1627] ⟨429529, 17, [(2, 3), (3, 1), (11, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1627
  · decide +kernel

theorem prime_433651 : Nat.Prime 433651 := by
  apply nodeValid_prime [2, 3, 5, 7, 59] ⟨433651, 2, [(2, 1), (3, 1), (5, 2), (7, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_626771 : Nat.Prime 626771 := by
  apply nodeValid_prime [2, 5, 233, 269] ⟨626771, 2, [(2, 1), (5, 1), (233, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
    · exact prime_269
  · decide +kernel

theorem prime_723259 : Nat.Prime 723259 := by
  apply nodeValid_prime [2, 3, 23, 1747] ⟨723259, 2, [(2, 1), (3, 2), (23, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1747
  · decide +kernel

theorem prime_729269 : Nat.Prime 729269 := by
  apply nodeValid_prime [2, 337, 541] ⟨729269, 2, [(2, 2), (337, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_541
  · decide +kernel

theorem prime_765859 : Nat.Prime 765859 := by
  apply nodeValid_prime [2, 3, 127643] ⟨765859, 2, [(2, 1), (3, 1), (127643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127643
  · decide +kernel

theorem prime_882481 : Nat.Prime 882481 := by
  apply nodeValid_prime [2, 3, 5, 3677] ⟨882481, 11, [(2, 4), (3, 1), (5, 1), (3677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3677
  · decide +kernel

theorem prime_952669 : Nat.Prime 952669 := by
  apply nodeValid_prime [2, 3, 8821] ⟨952669, 2, [(2, 2), (3, 3), (8821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8821
  · decide +kernel

theorem prime_1069129 : Nat.Prime 1069129 := by
  apply nodeValid_prime [2, 3, 31, 479] ⟨1069129, 7, [(2, 3), (3, 2), (31, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_479
  · decide +kernel

theorem prime_1199309 : Nat.Prime 1199309 := by
  apply nodeValid_prime [2, 11, 97, 281] ⟨1199309, 2, [(2, 2), (11, 1), (97, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_97
    · exact prime_281
  · decide +kernel

theorem prime_1282933 : Nat.Prime 1282933 := by
  apply nodeValid_prime [2, 3, 7, 1697] ⟨1282933, 2, [(2, 2), (3, 3), (7, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1697
  · decide +kernel

theorem prime_1351901 : Nat.Prime 1351901 := by
  apply nodeValid_prime [2, 5, 11, 1229] ⟨1351901, 2, [(2, 2), (5, 2), (11, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1229
  · decide +kernel

theorem prime_1376603 : Nat.Prime 1376603 := by
  apply nodeValid_prime [2, 43, 16007] ⟨1376603, 2, [(2, 1), (43, 1), (16007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_16007
  · decide +kernel

theorem prime_1583809 : Nat.Prime 1583809 := by
  apply nodeValid_prime [2, 3, 73, 113] ⟨1583809, 7, [(2, 6), (3, 1), (73, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_113
  · decide +kernel

theorem prime_1617349 : Nat.Prime 1617349 := by
  apply nodeValid_prime [2, 3, 53, 2543] ⟨1617349, 2, [(2, 2), (3, 1), (53, 1), (2543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_2543
  · decide +kernel

theorem prime_1638431 : Nat.Prime 1638431 := by
  apply nodeValid_prime [2, 5, 59, 2777] ⟨1638431, 7, [(2, 1), (5, 1), (59, 1), (2777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_2777
  · decide +kernel

theorem prime_2441729 : Nat.Prime 2441729 := by
  apply nodeValid_prime [2, 19, 251] ⟨2441729, 3, [(2, 9), (19, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_251
  · decide +kernel

theorem prime_2457349 : Nat.Prime 2457349 := by
  apply nodeValid_prime [2, 3, 47, 4357] ⟨2457349, 2, [(2, 2), (3, 1), (47, 1), (4357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_4357
  · decide +kernel

theorem prime_3086903 : Nat.Prime 3086903 := by
  apply nodeValid_prime [2, 7, 13, 2423] ⟨3086903, 5, [(2, 1), (7, 2), (13, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_2423
  · decide +kernel

theorem prime_3891247 : Nat.Prime 3891247 := by
  apply nodeValid_prime [2, 3, 199, 3259] ⟨3891247, 3, [(2, 1), (3, 1), (199, 1), (3259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_3259
  · decide +kernel

theorem prime_4005233 : Nat.Prime 4005233 := by
  apply nodeValid_prime [2, 7, 11, 3251] ⟨4005233, 3, [(2, 4), (7, 1), (11, 1), (3251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_3251
  · decide +kernel

theorem prime_5282831 : Nat.Prime 5282831 := by
  apply nodeValid_prime [2, 5, 7, 163, 463] ⟨5282831, 7, [(2, 1), (5, 1), (7, 1), (163, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_163
    · exact prime_463
  · decide +kernel

theorem prime_7658591 : Nat.Prime 7658591 := by
  apply nodeValid_prime [2, 5, 765859] ⟨7658591, 17, [(2, 1), (5, 1), (765859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_765859
  · decide +kernel

theorem prime_8203859 : Nat.Prime 8203859 := by
  apply nodeValid_prime [2, 13, 19, 16607] ⟨8203859, 2, [(2, 1), (13, 1), (19, 1), (16607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_16607
  · decide +kernel

theorem prime_8700079 : Nat.Prime 8700079 := by
  apply nodeValid_prime [2, 3, 239, 6067] ⟨8700079, 3, [(2, 1), (3, 1), (239, 1), (6067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_6067
  · decide +kernel

theorem prime_8710193 : Nat.Prime 8710193 := by
  apply nodeValid_prime [2, 23, 23669] ⟨8710193, 3, [(2, 4), (23, 1), (23669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_23669
  · decide +kernel

theorem prime_10565663 : Nat.Prime 10565663 := by
  apply nodeValid_prime [2, 5282831] ⟨10565663, 5, [(2, 1), (5282831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5282831
  · decide +kernel

theorem prime_10778741 : Nat.Prime 10778741 := by
  apply nodeValid_prime [2, 5, 7, 76991] ⟨10778741, 10, [(2, 2), (5, 1), (7, 1), (76991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_76991
  · decide +kernel

theorem prime_11985163 : Nat.Prime 11985163 := by
  apply nodeValid_prime [2, 3, 7, 19, 23, 653] ⟨11985163, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (23, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_653
  · decide +kernel

theorem prime_16127981 : Nat.Prime 16127981 := by
  apply nodeValid_prime [2, 5, 11, 73309] ⟨16127981, 2, [(2, 2), (5, 1), (11, 1), (73309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_73309
  · decide +kernel

theorem prime_16239719 : Nat.Prime 16239719 := by
  apply nodeValid_prime [2, 11, 19, 38851] ⟨16239719, 11, [(2, 1), (11, 1), (19, 1), (38851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_38851
  · decide +kernel

theorem prime_20382697 : Nat.Prime 20382697 := by
  apply nodeValid_prime [2, 3, 283093] ⟨20382697, 5, [(2, 3), (3, 2), (283093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283093
  · decide +kernel

theorem prime_22039781 : Nat.Prime 22039781 := by
  apply nodeValid_prime [2, 5, 7, 157427] ⟨22039781, 2, [(2, 2), (5, 1), (7, 1), (157427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_157427
  · decide +kernel

theorem prime_23169863 : Nat.Prime 23169863 := by
  apply nodeValid_prime [2, 43, 419, 643] ⟨23169863, 10, [(2, 1), (43, 1), (419, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_419
    · exact prime_643
  · decide +kernel

theorem prime_32460143 : Nat.Prime 32460143 := by
  apply nodeValid_prime [2, 11, 13, 113497] ⟨32460143, 5, [(2, 1), (11, 1), (13, 1), (113497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_113497
  · decide +kernel

theorem prime_41985791 : Nat.Prime 41985791 := by
  apply nodeValid_prime [2, 5, 7, 11, 4957] ⟨41985791, 7, [(2, 1), (5, 1), (7, 1), (11, 2), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_4957
  · decide +kernel

theorem prime_42019931 : Nat.Prime 42019931 := by
  apply nodeValid_prime [2, 5, 71, 59183] ⟨42019931, 7, [(2, 1), (5, 1), (71, 1), (59183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_59183
  · decide +kernel

theorem prime_47594201 : Nat.Prime 47594201 := by
  apply nodeValid_prime [2, 5, 237971] ⟨47594201, 3, [(2, 3), (5, 2), (237971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_237971
  · decide +kernel

theorem prime_82349923 : Nat.Prime 82349923 := by
  apply nodeValid_prime [2, 3, 47, 292021] ⟨82349923, 13, [(2, 1), (3, 1), (47, 1), (292021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_292021
  · decide +kernel

theorem prime_105200507 : Nat.Prime 105200507 := by
  apply nodeValid_prime [2, 41, 1282933] ⟨105200507, 2, [(2, 1), (41, 1), (1282933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1282933
  · decide +kernel

theorem prime_113353073 : Nat.Prime 113353073 := by
  apply nodeValid_prime [2, 7, 144583] ⟨113353073, 3, [(2, 4), (7, 2), (144583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_144583
  · decide +kernel

theorem prime_125544101 : Nat.Prime 125544101 := by
  apply nodeValid_prime [2, 5, 11, 61, 1871] ⟨125544101, 2, [(2, 2), (5, 2), (11, 1), (61, 1), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_61
    · exact prime_1871
  · decide +kernel

theorem prime_162960461 : Nat.Prime 162960461 := by
  apply nodeValid_prime [2, 5, 13, 626771] ⟨162960461, 7, [(2, 2), (5, 1), (13, 1), (626771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_626771
  · decide +kernel

theorem prime_227356067 : Nat.Prime 227356067 := by
  apply nodeValid_prime [2, 7, 16239719] ⟨227356067, 2, [(2, 1), (7, 1), (16239719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_16239719
  · decide +kernel

theorem prime_251088203 : Nat.Prime 251088203 := by
  apply nodeValid_prime [2, 125544101] ⟨251088203, 2, [(2, 1), (125544101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_125544101
  · decide +kernel

theorem prime_454915829 : Nat.Prime 454915829 := by
  apply nodeValid_prime [2, 41, 229, 12113] ⟨454915829, 2, [(2, 2), (41, 1), (229, 1), (12113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_229
    · exact prime_12113
  · decide +kernel

theorem prime_811170083 : Nat.Prime 811170083 := by
  apply nodeValid_prime [2, 127, 223, 14321] ⟨811170083, 2, [(2, 1), (127, 1), (223, 1), (14321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_223
    · exact prime_14321
  · decide +kernel

theorem prime_897203201 : Nat.Prime 897203201 := by
  apply nodeValid_prime [2, 5, 101, 347] ⟨897203201, 6, [(2, 10), (5, 2), (101, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_347
  · decide +kernel

theorem prime_903166937 : Nat.Prime 903166937 := by
  apply nodeValid_prime [2, 7, 16127981] ⟨903166937, 3, [(2, 3), (7, 1), (16127981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_16127981
  · decide +kernel

theorem prime_1357823947 : Nat.Prime 1357823947 := by
  apply nodeValid_prime [2, 3, 1259, 179749] ⟨1357823947, 2, [(2, 1), (3, 1), (1259, 1), (179749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1259
    · exact prime_179749
  · decide +kernel

theorem prime_1794406403 : Nat.Prime 1794406403 := by
  apply nodeValid_prime [2, 897203201] ⟨1794406403, 2, [(2, 1), (897203201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_897203201
  · decide +kernel

theorem prime_4145070491 : Nat.Prime 4145070491 := by
  apply nodeValid_prime [2, 5, 11, 367, 102677] ⟨4145070491, 6, [(2, 1), (5, 1), (11, 1), (367, 1), (102677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_367
    · exact prime_102677
  · decide +kernel

theorem prime_6766720031 : Nat.Prime 6766720031 := by
  apply nodeValid_prime [2, 5, 7, 59, 1638431] ⟨6766720031, 7, [(2, 1), (5, 1), (7, 1), (59, 1), (1638431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_1638431
  · decide +kernel

theorem prime_8106729329 : Nat.Prime 8106729329 := by
  apply nodeValid_prime [2, 59, 227, 37831] ⟨8106729329, 3, [(2, 4), (59, 1), (227, 1), (37831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_227
    · exact prime_37831
  · decide +kernel

theorem prime_10230185533 : Nat.Prime 10230185533 := by
  apply nodeValid_prime [2, 3, 7, 167, 729269] ⟨10230185533, 2, [(2, 2), (3, 1), (7, 1), (167, 1), (729269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_167
    · exact prime_729269
  · decide +kernel

theorem prime_13794896293 : Nat.Prime 13794896293 := by
  apply nodeValid_prime [2, 3, 29527, 38933] ⟨13794896293, 5, [(2, 2), (3, 1), (29527, 1), (38933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29527
    · exact prime_38933
  · decide +kernel

theorem prime_16107078619 : Nat.Prime 16107078619 := by
  apply nodeValid_prime [2, 3, 23, 347, 112121] ⟨16107078619, 2, [(2, 1), (3, 2), (23, 1), (347, 1), (112121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_347
    · exact prime_112121
  · decide +kernel

theorem prime_16213458659 : Nat.Prime 16213458659 := by
  apply nodeValid_prime [2, 8106729329] ⟨16213458659, 2, [(2, 1), (8106729329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8106729329
  · decide +kernel

theorem prime_21676006489 : Nat.Prime 21676006489 := by
  apply nodeValid_prime [2, 3, 903166937] ⟨21676006489, 23, [(2, 3), (3, 1), (903166937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_903166937
  · decide +kernel

theorem prime_23725459309 : Nat.Prime 23725459309 := by
  apply nodeValid_prime [2, 3, 97, 20382697] ⟨23725459309, 6, [(2, 2), (3, 1), (97, 1), (20382697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_20382697
  · decide +kernel

theorem prime_29362941991 : Nat.Prime 29362941991 := by
  apply nodeValid_prime [2, 3, 5, 79, 1376603] ⟨29362941991, 3, [(2, 1), (3, 3), (5, 1), (79, 1), (1376603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_1376603
  · decide +kernel

theorem prime_120803101057 : Nat.Prime 120803101057 := by
  apply nodeValid_prime [2, 3, 11, 17, 16993] ⟨120803101057, 5, [(2, 7), (3, 3), (11, 2), (17, 1), (16993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_16993
  · decide +kernel

theorem prime_234513236333 : Nat.Prime 234513236333 := by
  apply nodeValid_prime [2, 53, 127, 8710193] ⟨234513236333, 2, [(2, 2), (53, 1), (127, 1), (8710193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_127
    · exact prime_8710193
  · decide +kernel

theorem prime_237254588201 : Nat.Prime 237254588201 := by
  apply nodeValid_prime [2, 5, 7, 107, 1583809] ⟨237254588201, 13, [(2, 3), (5, 2), (7, 1), (107, 1), (1583809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_107
    · exact prime_1583809
  · decide +kernel

theorem prime_237254593091 : Nat.Prime 237254593091 := by
  apply nodeValid_prime [2, 5, 23725459309] ⟨237254593091, 6, [(2, 1), (5, 1), (23725459309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23725459309
  · decide +kernel

theorem prime_240811014011 : Nat.Prime 240811014011 := by
  apply nodeValid_prime [2, 5, 7, 6173, 79613] ⟨240811014011, 7, [(2, 1), (5, 1), (7, 2), (6173, 1), (79613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6173
    · exact prime_79613
  · decide +kernel

theorem prime_469026469823 : Nat.Prime 469026469823 := by
  apply nodeValid_prime [2, 5581, 42019931] ⟨469026469823, 5, [(2, 1), (5581, 1), (42019931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5581
    · exact prime_42019931
  · decide +kernel

theorem prime_469026472667 : Nat.Prime 469026472667 := by
  apply nodeValid_prime [2, 234513236333] ⟨469026472667, 2, [(2, 1), (234513236333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_234513236333
  · decide +kernel

theorem prime_469026473963 : Nat.Prime 469026473963 := by
  apply nodeValid_prime [2, 17, 13794896293] ⟨469026473963, 2, [(2, 1), (17, 1), (13794896293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_13794896293
  · decide +kernel

theorem prime_469807071857 : Nat.Prime 469807071857 := by
  apply nodeValid_prime [2, 29362941991] ⟨469807071857, 3, [(2, 4), (29362941991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29362941991
  · decide +kernel

theorem prime_469807085663 : Nat.Prime 469807085663 := by
  apply nodeValid_prime [2, 173, 1357823947] ⟨469807085663, 5, [(2, 1), (173, 1), (1357823947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_1357823947
  · decide +kernel

theorem prime_469807085777 : Nat.Prime 469807085777 := by
  apply nodeValid_prime [2, 7, 17, 569, 433651] ⟨469807085777, 3, [(2, 4), (7, 1), (17, 1), (569, 1), (433651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_569
    · exact prime_433651
  · decide +kernel

theorem prime_470588534519 : Nat.Prime 470588534519 := by
  apply nodeValid_prime [2, 23, 10230185533] ⟨470588534519, 11, [(2, 1), (23, 1), (10230185533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_10230185533
  · decide +kernel

theorem prime_470588536169 : Nat.Prime 470588536169 := by
  apply nodeValid_prime [2, 136949, 429529] ⟨470588536169, 3, [(2, 3), (136949, 1), (429529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_136949
    · exact prime_429529
  · decide +kernel

theorem prime_470588553601 : Nat.Prime 470588553601 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 241] ⟨470588553601, 7, [(2, 7), (3, 1), (5, 2), (11, 2), (41, 2), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_241
  · decide +kernel

theorem prime_471370914809 : Nat.Prime 471370914809 := by
  apply nodeValid_prime [2, 607, 3823, 25391] ⟨471370914809, 3, [(2, 3), (607, 1), (3823, 1), (25391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_607
    · exact prime_3823
    · exact prime_25391
  · decide +kernel

theorem prime_471370958869 : Nat.Prime 471370958869 := by
  apply nodeValid_prime [2, 3, 23, 223, 7658591] ⟨471370958869, 2, [(2, 2), (3, 1), (23, 1), (223, 1), (7658591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_223
    · exact prime_7658591
  · decide +kernel

theorem prime_471370959253 : Nat.Prime 471370959253 := by
  apply nodeValid_prime [2, 3, 53, 82349923] ⟨471370959253, 5, [(2, 2), (3, 3), (53, 1), (82349923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_82349923
  · decide +kernel

theorem prime_472154157989 : Nat.Prime 472154157989 := by
  apply nodeValid_prime [2, 163, 24413, 29663] ⟨472154157989, 2, [(2, 2), (163, 1), (24413, 1), (29663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_24413
    · exact prime_29663
  · decide +kernel

theorem prime_472154160679 : Nat.Prime 472154160679 := by
  apply nodeValid_prime [2, 3, 1181, 4783, 13931] ⟨472154160679, 13, [(2, 1), (3, 1), (1181, 1), (4783, 1), (13931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1181
    · exact prime_4783
    · exact prime_13931
  · decide +kernel

theorem prime_472154161463 : Nat.Prime 472154161463 := by
  apply nodeValid_prime [2, 31, 2467, 3086903] ⟨472154161463, 5, [(2, 1), (31, 1), (2467, 1), (3086903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2467
    · exact prime_3086903
  · decide +kernel

theorem prime_472938274519 : Nat.Prime 472938274519 := by
  apply nodeValid_prime [2, 3, 71, 107, 2297, 4517] ⟨472938274519, 3, [(2, 1), (3, 1), (71, 1), (107, 1), (2297, 1), (4517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_107
    · exact prime_2297
    · exact prime_4517
  · decide +kernel

theorem prime_472938274741 : Nat.Prime 472938274741 := by
  apply nodeValid_prime [2, 3, 5, 67, 331, 355427] ⟨472938274741, 2, [(2, 2), (3, 1), (5, 1), (67, 1), (331, 1), (355427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_331
    · exact prime_355427
  · decide +kernel

theorem prime_472938281561 : Nat.Prime 472938281561 := by
  apply nodeValid_prime [2, 5, 877, 941, 14327] ⟨472938281561, 3, [(2, 3), (5, 1), (877, 1), (941, 1), (14327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_877
    · exact prime_941
    · exact prime_14327
  · decide +kernel

theorem prime_473723290393 : Nat.Prime 473723290393 := by
  apply nodeValid_prime [2, 3, 11, 1794406403] ⟨473723290393, 5, [(2, 3), (3, 1), (11, 1), (1794406403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1794406403
  · decide +kernel

theorem prime_473723326943 : Nat.Prime 473723326943 := by
  apply nodeValid_prime [2, 7297, 32460143] ⟨473723326943, 5, [(2, 1), (7297, 1), (32460143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7297
    · exact prime_32460143
  · decide +kernel

theorem prime_473723328473 : Nat.Prime 473723328473 := by
  apply nodeValid_prime [2, 73, 811170083] ⟨473723328473, 3, [(2, 3), (73, 1), (811170083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_811170083
  · decide +kernel

theorem prime_474509176403 : Nat.Prime 474509176403 := by
  apply nodeValid_prime [2, 237254588201] ⟨474509176403, 2, [(2, 1), (237254588201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_237254588201
  · decide +kernel

theorem prime_474509186183 : Nat.Prime 474509186183 := by
  apply nodeValid_prime [2, 237254593091] ⟨474509186183, 5, [(2, 1), (237254593091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_237254593091
  · decide +kernel

theorem prime_474509186197 : Nat.Prime 474509186197 := by
  apply nodeValid_prime [2, 3, 41507, 952669] ⟨474509186197, 2, [(2, 2), (3, 1), (41507, 1), (952669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41507
    · exact prime_952669
  · decide +kernel

theorem prime_475295945977 : Nat.Prime 475295945977 := by
  apply nodeValid_prime [2, 3, 19, 257, 1351901] ⟨475295945977, 5, [(2, 3), (3, 2), (19, 1), (257, 1), (1351901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_257
    · exact prime_1351901
  · decide +kernel

theorem prime_475295946089 : Nat.Prime 475295946089 := by
  apply nodeValid_prime [2, 17, 47, 281, 264619] ⟨475295946089, 3, [(2, 3), (17, 1), (47, 1), (281, 1), (264619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_281
    · exact prime_264619
  · decide +kernel

theorem prime_475295950583 : Nat.Prime 475295950583 := by
  apply nodeValid_prime [2, 313, 12829, 59183] ⟨475295950583, 5, [(2, 1), (313, 1), (12829, 1), (59183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_12829
    · exact prime_59183
  · decide +kernel

theorem prime_476083604299 : Nat.Prime 476083604299 := by
  apply nodeValid_prime [2, 3, 349, 227356067] ⟨476083604299, 2, [(2, 1), (3, 1), (349, 1), (227356067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_227356067
  · decide +kernel

theorem prime_476083608829 : Nat.Prime 476083608829 := by
  apply nodeValid_prime [2, 3, 257, 701, 220217] ⟨476083608829, 2, [(2, 2), (3, 1), (257, 1), (701, 1), (220217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_701
    · exact prime_220217
  · decide +kernel

theorem prime_476083612747 : Nat.Prime 476083612747 := by
  apply nodeValid_prime [2, 3, 7, 3203, 43691] ⟨476083612747, 5, [(2, 1), (3, 5), (7, 1), (3203, 1), (43691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3203
    · exact prime_43691
  · decide +kernel

theorem prime_476872142543 : Nat.Prime 476872142543 := by
  apply nodeValid_prime [2, 19, 17351, 723259] ⟨476872142543, 5, [(2, 1), (19, 1), (17351, 1), (723259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_17351
    · exact prime_723259
  · decide +kernel

theorem prime_476872142759 : Nat.Prime 476872142759 := by
  apply nodeValid_prime [2, 11, 21676006489] ⟨476872142759, 11, [(2, 1), (11, 1), (21676006489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_21676006489
  · decide +kernel

theorem prime_476872160903 : Nat.Prime 476872160903 := by
  apply nodeValid_prime [2, 223019, 1069129] ⟨476872160903, 5, [(2, 1), (223019, 1), (1069129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223019
    · exact prime_1069129
  · decide +kernel

theorem prime_477661592833 : Nat.Prime 477661592833 := by
  apply nodeValid_prime [2, 3, 29, 41, 109, 4799] ⟨477661592833, 7, [(2, 8), (3, 1), (29, 1), (41, 1), (109, 1), (4799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_41
    · exact prime_109
    · exact prime_4799
  · decide +kernel

theorem prime_477661619821 : Nat.Prime 477661619821 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 1531, 67531] ⟨477661619821, 14, [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (1531, 1), (67531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_1531
    · exact prime_67531
  · decide +kernel

theorem prime_477661620451 : Nat.Prime 477661620451 := by
  apply nodeValid_prime [2, 3, 5, 7, 454915829] ⟨477661620451, 7, [(2, 1), (3, 1), (5, 2), (7, 1), (454915829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_454915829
  · decide +kernel

theorem prime_478451905837 : Nat.Prime 478451905837 := by
  apply nodeValid_prime [2, 3, 379, 105200507] ⟨478451905837, 2, [(2, 2), (3, 1), (379, 1), (105200507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_105200507
  · decide +kernel

theorem prime_478451913497 : Nat.Prime 478451913497 := by
  apply nodeValid_prime [2, 367, 162960461] ⟨478451913497, 3, [(2, 3), (367, 1), (162960461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_162960461
  · decide +kernel

theorem prime_478451914093 : Nat.Prime 478451914093 := by
  apply nodeValid_prime [2, 3, 5443, 2441729] ⟨478451914093, 2, [(2, 2), (3, 2), (5443, 1), (2441729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5443
    · exact prime_2441729
  · decide +kernel

theorem prime_479243099117 : Nat.Prime 479243099117 := by
  apply nodeValid_prime [2, 41, 47501, 61519] ⟨479243099117, 3, [(2, 2), (41, 1), (47501, 1), (61519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_47501
    · exact prime_61519
  · decide +kernel

theorem prime_479243099173 : Nat.Prime 479243099173 := by
  apply nodeValid_prime [2, 3, 31, 33211, 38791] ⟨479243099173, 17, [(2, 2), (3, 1), (31, 1), (33211, 1), (38791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_33211
    · exact prime_38791
  · decide +kernel

theorem prime_479243104957 : Nat.Prime 479243104957 := by
  apply nodeValid_prime [2, 3, 7, 11, 1459, 39499] ⟨479243104957, 2, [(2, 2), (3, 3), (7, 1), (11, 1), (1459, 1), (39499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1459
    · exact prime_39499
  · decide +kernel

theorem prime_480035111287 : Nat.Prime 480035111287 := by
  apply nodeValid_prime [2, 3, 41, 47594201] ⟨480035111287, 3, [(2, 1), (3, 1), (41, 2), (47594201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_47594201
  · decide +kernel

theorem prime_480035111389 : Nat.Prime 480035111389 := by
  apply nodeValid_prime [2, 3, 7, 32693, 174799] ⟨480035111389, 2, [(2, 2), (3, 1), (7, 1), (32693, 1), (174799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_32693
    · exact prime_174799
  · decide +kernel

theorem prime_480035185517 : Nat.Prime 480035185517 := by
  apply nodeValid_prime [2, 19, 83, 4005233] ⟨480035185517, 2, [(2, 2), (19, 2), (83, 1), (4005233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_83
    · exact prime_4005233
  · decide +kernel

theorem prime_480828153607 : Nat.Prime 480828153607 := by
  apply nodeValid_prime [2, 3, 49549, 1617349] ⟨480828153607, 3, [(2, 1), (3, 1), (49549, 1), (1617349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49549
    · exact prime_1617349
  · decide +kernel

theorem prime_480828175991 : Nat.Prime 480828175991 := by
  apply nodeValid_prime [2, 5, 5861, 8203859] ⟨480828175991, 7, [(2, 1), (5, 1), (5861, 1), (8203859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5861
    · exact prime_8203859
  · decide +kernel

theorem prime_480828176957 : Nat.Prime 480828176957 := by
  apply nodeValid_prime [2, 29, 4145070491] ⟨480828176957, 2, [(2, 2), (29, 1), (4145070491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_4145070491
  · decide +kernel

theorem prime_481622006707 : Nat.Prime 481622006707 := by
  apply nodeValid_prime [2, 3, 739, 967, 112327] ⟨481622006707, 3, [(2, 1), (3, 1), (739, 1), (967, 1), (112327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_739
    · exact prime_967
    · exact prime_112327
  · decide +kernel

theorem prime_481622028023 : Nat.Prime 481622028023 := by
  apply nodeValid_prime [2, 240811014011] ⟨481622028023, 5, [(2, 1), (240811014011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_240811014011
  · decide +kernel

theorem prime_481622028133 : Nat.Prime 481622028133 := by
  apply nodeValid_prime [2, 3, 7, 101, 241, 235553] ⟨481622028133, 2, [(2, 2), (3, 1), (7, 1), (101, 1), (241, 1), (235553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
    · exact prime_241
    · exact prime_235553
  · decide +kernel

theorem prime_482416738591 : Nat.Prime 482416738591 := by
  apply nodeValid_prime [2, 3, 5, 383, 41985791] ⟨482416738591, 3, [(2, 1), (3, 1), (5, 1), (383, 1), (41985791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
    · exact prime_41985791
  · decide +kernel

theorem prime_482416752491 : Nat.Prime 482416752491 := by
  apply nodeValid_prime [2, 5, 83, 101, 263, 21881] ⟨482416752491, 2, [(2, 1), (5, 1), (83, 1), (101, 1), (263, 1), (21881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_101
    · exact prime_263
    · exact prime_21881
  · decide +kernel

theorem prime_482416753099 : Nat.Prime 482416753099 := by
  apply nodeValid_prime [2, 3, 7, 1399, 1663, 4937] ⟨482416753099, 2, [(2, 1), (3, 1), (7, 1), (1399, 1), (1663, 1), (4937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1399
    · exact prime_1663
    · exact prime_4937
  · decide +kernel

theorem prime_483212358571 : Nat.Prime 483212358571 := by
  apply nodeValid_prime [2, 3, 5, 16107078619] ⟨483212358571, 12, [(2, 1), (3, 1), (5, 1), (16107078619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16107078619
  · decide +kernel

theorem prime_483212404229 : Nat.Prime 483212404229 := by
  apply nodeValid_prime [2, 120803101057] ⟨483212404229, 2, [(2, 2), (120803101057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120803101057
  · decide +kernel

theorem prime_483212404361 : Nat.Prime 483212404361 := by
  apply nodeValid_prime [2, 5, 7, 17, 121867] ⟨483212404361, 6, [(2, 3), (5, 1), (7, 3), (17, 2), (121867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_121867
  · decide +kernel

theorem prime_484008822593 : Nat.Prime 484008822593 := by
  apply nodeValid_prime [2, 631, 11985163] ⟨484008822593, 3, [(2, 6), (631, 1), (11985163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_631
    · exact prime_11985163
  · decide +kernel

theorem prime_484008823423 : Nat.Prime 484008823423 := by
  apply nodeValid_prime [2, 3, 71, 1171, 323419] ⟨484008823423, 3, [(2, 1), (3, 2), (71, 1), (1171, 1), (323419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_1171
    · exact prime_323419
  · decide +kernel

theorem prime_484008866849 : Nat.Prime 484008866849 := by
  apply nodeValid_prime [2, 13, 23, 3891247] ⟨484008866849, 6, [(2, 5), (13, 2), (23, 1), (3891247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_3891247
  · decide +kernel

theorem prime_484806212699 : Nat.Prime 484806212699 := by
  apply nodeValid_prime [2, 43, 523, 10778741] ⟨484806212699, 2, [(2, 1), (43, 1), (523, 1), (10778741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_523
    · exact prime_10778741
  · decide +kernel

theorem prime_484806213413 : Nat.Prime 484806213413 := by
  apply nodeValid_prime [2, 5231, 23169863] ⟨484806213413, 2, [(2, 2), (5231, 1), (23169863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5231
    · exact prime_23169863
  · decide +kernel

theorem prime_484806266293 : Nat.Prime 484806266293 := by
  apply nodeValid_prime [2, 3, 168943, 239137] ⟨484806266293, 2, [(2, 2), (3, 1), (168943, 1), (239137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_168943
    · exact prime_239137
  · decide +kernel

theorem prime_485604564733 : Nat.Prime 485604564733 := by
  apply nodeValid_prime [2, 3, 7, 17, 113353073] ⟨485604564733, 5, [(2, 2), (3, 2), (7, 1), (17, 1), (113353073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_113353073
  · decide +kernel

theorem prime_485604584603 : Nat.Prime 485604584603 := by
  apply nodeValid_prime [2, 967, 251088203] ⟨485604584603, 2, [(2, 1), (967, 1), (251088203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_967
    · exact prime_251088203
  · decide +kernel

theorem prime_485604584833 : Nat.Prime 485604584833 := by
  apply nodeValid_prime [2, 3, 1433, 882481] ⟨485604584833, 5, [(2, 7), (3, 1), (1433, 1), (882481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1433
    · exact prime_882481
  · decide +kernel

theorem prime_486403751131 : Nat.Prime 486403751131 := by
  apply nodeValid_prime [2, 3, 5, 11, 1229, 1199309] ⟨486403751131, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (1229, 1), (1199309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1229
    · exact prime_1199309
  · decide +kernel

theorem prime_486403751153 : Nat.Prime 486403751153 := by
  apply nodeValid_prime [2, 11, 1187, 211661] ⟨486403751153, 3, [(2, 4), (11, 2), (1187, 1), (211661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1187
    · exact prime_211661
  · decide +kernel

theorem prime_486403759771 : Nat.Prime 486403759771 := by
  apply nodeValid_prime [2, 3, 5, 16213458659] ⟨486403759771, 2, [(2, 1), (3, 1), (5, 1), (16213458659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16213458659
  · decide +kernel

theorem prime_487203842137 : Nat.Prime 487203842137 := by
  apply nodeValid_prime [2, 3, 11, 751, 2457349] ⟨487203842137, 5, [(2, 3), (3, 1), (11, 1), (751, 1), (2457349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_751
    · exact prime_2457349
  · decide +kernel

theorem prime_487203842233 : Nat.Prime 487203842233 := by
  apply nodeValid_prime [2, 3, 6766720031] ⟨487203842233, 7, [(2, 3), (3, 2), (6766720031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6766720031
  · decide +kernel

theorem prime_487203852257 : Nat.Prime 487203852257 := by
  apply nodeValid_prime [2, 11, 131, 10565663] ⟨487203852257, 3, [(2, 5), (11, 1), (131, 1), (10565663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_131
    · exact prime_10565663
  · decide +kernel

theorem prime_488004830903 : Nat.Prime 488004830903 := by
  apply nodeValid_prime [2, 11071, 22039781] ⟨488004830903, 5, [(2, 1), (11071, 1), (22039781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11071
    · exact prime_22039781
  · decide +kernel

theorem prime_488004831269 : Nat.Prime 488004831269 := by
  apply nodeValid_prime [2, 37, 379, 8700079] ⟨488004831269, 2, [(2, 2), (37, 1), (379, 1), (8700079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_379
    · exact prime_8700079
  · decide +kernel

theorem prime_488004832813 : Nat.Prime 488004832813 := by
  apply nodeValid_prime [2, 3, 7, 17, 5099, 67021] ⟨488004832813, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (5099, 1), (67021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_5099
    · exact prime_67021
  · decide +kernel

end Sude.Lucas.Generated
