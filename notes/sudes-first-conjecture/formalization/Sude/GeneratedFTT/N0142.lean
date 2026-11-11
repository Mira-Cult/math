import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0132

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_14929 : Nat.Prime 14929 := by
  apply nodeValid_prime [2, 3, 311] ⟨14929, 7, [(2, 4), (3, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
  · decide +kernel

theorem prime_23741 : Nat.Prime 23741 := by
  apply nodeValid_prime [2, 5, 1187] ⟨23741, 2, [(2, 2), (5, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1187
  · decide +kernel

theorem prime_26713 : Nat.Prime 26713 := by
  apply nodeValid_prime [2, 3, 7, 53] ⟨26713, 10, [(2, 3), (3, 2), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_31531 : Nat.Prime 31531 := by
  apply nodeValid_prime [2, 3, 5, 1051] ⟨31531, 2, [(2, 1), (3, 1), (5, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1051
  · decide +kernel

theorem prime_37379 : Nat.Prime 37379 := by
  apply nodeValid_prime [2, 11, 1699] ⟨37379, 2, [(2, 1), (11, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1699
  · decide +kernel

theorem prime_38069 : Nat.Prime 38069 := by
  apply nodeValid_prime [2, 31, 307] ⟨38069, 2, [(2, 2), (31, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_307
  · decide +kernel

theorem prime_38737 : Nat.Prime 38737 := by
  apply nodeValid_prime [2, 3, 269] ⟨38737, 5, [(2, 4), (3, 2), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
  · decide +kernel

theorem prime_42937 : Nat.Prime 42937 := by
  apply nodeValid_prime [2, 3, 1789] ⟨42937, 5, [(2, 3), (3, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1789
  · decide +kernel

theorem prime_44893 : Nat.Prime 44893 := by
  apply nodeValid_prime [2, 3, 29, 43] ⟨44893, 5, [(2, 2), (3, 2), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_51193 : Nat.Prime 51193 := by
  apply nodeValid_prime [2, 3, 79] ⟨51193, 5, [(2, 3), (3, 4), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_51413 : Nat.Prime 51413 := by
  apply nodeValid_prime [2, 12853] ⟨51413, 2, [(2, 2), (12853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12853
  · decide +kernel

theorem prime_51797 : Nat.Prime 51797 := by
  apply nodeValid_prime [2, 23, 563] ⟨51797, 3, [(2, 2), (23, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_563
  · decide +kernel

theorem prime_58043 : Nat.Prime 58043 := by
  apply nodeValid_prime [2, 29021] ⟨58043, 2, [(2, 1), (29021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29021
  · decide +kernel

theorem prime_65557 : Nat.Prime 65557 := by
  apply nodeValid_prime [2, 3, 607] ⟨65557, 5, [(2, 2), (3, 3), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_607
  · decide +kernel

theorem prime_71647 : Nat.Prime 71647 := by
  apply nodeValid_prime [2, 3, 11941] ⟨71647, 3, [(2, 1), (3, 1), (11941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11941
  · decide +kernel

theorem prime_74759 : Nat.Prime 74759 := by
  apply nodeValid_prime [2, 37379] ⟨74759, 11, [(2, 1), (37379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37379
  · decide +kernel

theorem prime_78607 : Nat.Prime 78607 := by
  apply nodeValid_prime [2, 3, 11, 397] ⟨78607, 3, [(2, 1), (3, 2), (11, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_397
  · decide +kernel

theorem prime_87407 : Nat.Prime 87407 := by
  apply nodeValid_prime [2, 11, 29, 137] ⟨87407, 5, [(2, 1), (11, 1), (29, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_137
  · decide +kernel

theorem prime_93053 : Nat.Prime 93053 := by
  apply nodeValid_prime [2, 43, 541] ⟨93053, 2, [(2, 2), (43, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_541
  · decide +kernel

theorem prime_98179 : Nat.Prime 98179 := by
  apply nodeValid_prime [2, 3, 16363] ⟨98179, 2, [(2, 1), (3, 1), (16363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16363
  · decide +kernel

theorem prime_105361 : Nat.Prime 105361 := by
  apply nodeValid_prime [2, 3, 5, 439] ⟨105361, 17, [(2, 4), (3, 1), (5, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_119827 : Nat.Prime 119827 := by
  apply nodeValid_prime [2, 3, 7, 317] ⟨119827, 3, [(2, 1), (3, 3), (7, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_317
  · decide +kernel

theorem prime_121351 : Nat.Prime 121351 := by
  apply nodeValid_prime [2, 3, 5, 809] ⟨121351, 3, [(2, 1), (3, 1), (5, 2), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_809
  · decide +kernel

theorem prime_124121 : Nat.Prime 124121 := by
  apply nodeValid_prime [2, 5, 29, 107] ⟨124121, 3, [(2, 3), (5, 1), (29, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_107
  · decide +kernel

theorem prime_133271 : Nat.Prime 133271 := by
  apply nodeValid_prime [2, 5, 13327] ⟨133271, 13, [(2, 1), (5, 1), (13327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13327
  · decide +kernel

theorem prime_141161 : Nat.Prime 141161 := by
  apply nodeValid_prime [2, 5, 3529] ⟨141161, 3, [(2, 3), (5, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3529
  · decide +kernel

theorem prime_149519 : Nat.Prime 149519 := by
  apply nodeValid_prime [2, 74759] ⟨149519, 13, [(2, 1), (74759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_74759
  · decide +kernel

theorem prime_179827 : Nat.Prime 179827 := by
  apply nodeValid_prime [2, 3, 17, 41, 43] ⟨179827, 2, [(2, 1), (3, 1), (17, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_186041 : Nat.Prime 186041 := by
  apply nodeValid_prime [2, 5, 4651] ⟨186041, 3, [(2, 3), (5, 1), (4651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4651
  · decide +kernel

theorem prime_186107 : Nat.Prime 186107 := by
  apply nodeValid_prime [2, 93053] ⟨186107, 2, [(2, 1), (93053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93053
  · decide +kernel

theorem prime_229237 : Nat.Prime 229237 := by
  apply nodeValid_prime [2, 3, 7, 2729] ⟨229237, 6, [(2, 2), (3, 1), (7, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2729
  · decide +kernel

theorem prime_248243 : Nat.Prime 248243 := by
  apply nodeValid_prime [2, 124121] ⟨248243, 2, [(2, 1), (124121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_124121
  · decide +kernel

theorem prime_260003 : Nat.Prime 260003 := by
  apply nodeValid_prime [2, 71, 1831] ⟨260003, 2, [(2, 1), (71, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1831
  · decide +kernel

theorem prime_286589 : Nat.Prime 286589 := by
  apply nodeValid_prime [2, 71647] ⟨286589, 2, [(2, 2), (71647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71647
  · decide +kernel

theorem prime_287269 : Nat.Prime 287269 := by
  apply nodeValid_prime [2, 3, 37, 647] ⟨287269, 2, [(2, 2), (3, 1), (37, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_647
  · decide +kernel

theorem prime_327163 : Nat.Prime 327163 := by
  apply nodeValid_prime [2, 3, 11, 4957] ⟨327163, 2, [(2, 1), (3, 1), (11, 1), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4957
  · decide +kernel

theorem prime_345739 : Nat.Prime 345739 := by
  apply nodeValid_prime [2, 3, 29, 1987] ⟨345739, 7, [(2, 1), (3, 1), (29, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1987
  · decide +kernel

theorem prime_348259 : Nat.Prime 348259 := by
  apply nodeValid_prime [2, 3, 58043] ⟨348259, 2, [(2, 1), (3, 1), (58043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58043
  · decide +kernel

theorem prime_464741 : Nat.Prime 464741 := by
  apply nodeValid_prime [2, 5, 19, 1223] ⟨464741, 2, [(2, 2), (5, 1), (19, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1223
  · decide +kernel

theorem prime_498397 : Nat.Prime 498397 := by
  apply nodeValid_prime [2, 3, 41, 1013] ⟨498397, 2, [(2, 2), (3, 1), (41, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1013
  · decide +kernel

theorem prime_573179 : Nat.Prime 573179 := by
  apply nodeValid_prime [2, 286589] ⟨573179, 2, [(2, 1), (286589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_286589
  · decide +kernel

theorem prime_668201 : Nat.Prime 668201 := by
  apply nodeValid_prime [2, 5, 13, 257] ⟨668201, 6, [(2, 3), (5, 2), (13, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_257
  · decide +kernel

theorem prime_686993 : Nat.Prime 686993 := by
  apply nodeValid_prime [2, 42937] ⟨686993, 3, [(2, 4), (42937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42937
  · decide +kernel

theorem prime_696271 : Nat.Prime 696271 := by
  apply nodeValid_prime [2, 3, 5, 23209] ⟨696271, 6, [(2, 1), (3, 1), (5, 1), (23209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23209
  · decide +kernel

theorem prime_747497 : Nat.Prime 747497 := by
  apply nodeValid_prime [2, 223, 419] ⟨747497, 3, [(2, 3), (223, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_419
  · decide +kernel

theorem prime_761381 : Nat.Prime 761381 := by
  apply nodeValid_prime [2, 5, 38069] ⟨761381, 2, [(2, 2), (5, 1), (38069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_38069
  · decide +kernel

theorem prime_766543 : Nat.Prime 766543 := by
  apply nodeValid_prime [2, 3, 7, 18251] ⟨766543, 3, [(2, 1), (3, 1), (7, 1), (18251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18251
  · decide +kernel

theorem prime_821281 : Nat.Prime 821281 := by
  apply nodeValid_prime [2, 3, 5, 29, 59] ⟨821281, 7, [(2, 5), (3, 1), (5, 1), (29, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_59
  · decide +kernel

theorem prime_835441 : Nat.Prime 835441 := by
  apply nodeValid_prime [2, 3, 5, 59] ⟨835441, 14, [(2, 4), (3, 1), (5, 1), (59, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_910691 : Nat.Prime 910691 := by
  apply nodeValid_prime [2, 5, 11, 17, 487] ⟨910691, 6, [(2, 1), (5, 1), (11, 1), (17, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_487
  · decide +kernel

theorem prime_1062121 : Nat.Prime 1062121 := by
  apply nodeValid_prime [2, 3, 5, 53, 167] ⟨1062121, 19, [(2, 3), (3, 1), (5, 1), (53, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_167
  · decide +kernel

theorem prime_1104449 : Nat.Prime 1104449 := by
  apply nodeValid_prime [2, 17257] ⟨1104449, 3, [(2, 6), (17257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17257
  · decide +kernel

theorem prime_1121947 : Nat.Prime 1121947 := by
  apply nodeValid_prime [2, 3, 7, 26713] ⟨1121947, 3, [(2, 1), (3, 1), (7, 1), (26713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_26713
  · decide +kernel

theorem prime_1501667 : Nat.Prime 1501667 := by
  apply nodeValid_prime [2, 41, 18313] ⟨1501667, 2, [(2, 1), (41, 1), (18313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_18313
  · decide +kernel

theorem prime_1657627 : Nat.Prime 1657627 := by
  apply nodeValid_prime [2, 3, 431, 641] ⟨1657627, 5, [(2, 1), (3, 1), (431, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
    · exact prime_641
  · decide +kernel

theorem prime_1673681 : Nat.Prime 1673681 := by
  apply nodeValid_prime [2, 5, 20921] ⟨1673681, 3, [(2, 4), (5, 1), (20921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20921
  · decide +kernel

theorem prime_1856947 : Nat.Prime 1856947 := by
  apply nodeValid_prime [2, 3, 7, 13, 19, 179] ⟨1856947, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (19, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_179
  · decide +kernel

theorem prime_2084447 : Nat.Prime 2084447 := by
  apply nodeValid_prime [2, 7, 13, 881] ⟨2084447, 5, [(2, 1), (7, 1), (13, 2), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_881
  · decide +kernel

theorem prime_2276269 : Nat.Prime 2276269 := by
  apply nodeValid_prime [2, 3, 29, 31, 211] ⟨2276269, 2, [(2, 2), (3, 1), (29, 1), (31, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
    · exact prime_211
  · decide +kernel

theorem prime_2641487 : Nat.Prime 2641487 := by
  apply nodeValid_prime [2, 887, 1489] ⟨2641487, 5, [(2, 1), (887, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_887
    · exact prime_1489
  · decide +kernel

theorem prime_2788447 : Nat.Prime 2788447 := by
  apply nodeValid_prime [2, 3, 464741] ⟨2788447, 3, [(2, 1), (3, 1), (464741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_464741
  · decide +kernel

theorem prime_3193633 : Nat.Prime 3193633 := by
  apply nodeValid_prime [2, 3, 13, 853] ⟨3193633, 5, [(2, 5), (3, 2), (13, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_853
  · decide +kernel

theorem prime_3998131 : Nat.Prime 3998131 := by
  apply nodeValid_prime [2, 3, 5, 133271] ⟨3998131, 2, [(2, 1), (3, 1), (5, 1), (133271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_133271
  · decide +kernel

theorem prime_4121959 : Nat.Prime 4121959 := by
  apply nodeValid_prime [2, 3, 686993] ⟨4121959, 3, [(2, 1), (3, 1), (686993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_686993
  · decide +kernel

theorem prime_4356511 : Nat.Prime 4356511 := by
  apply nodeValid_prime [2, 3, 5, 19, 7643] ⟨4356511, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (7643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_7643
  · decide +kernel

theorem prime_4484983 : Nat.Prime 4484983 := by
  apply nodeValid_prime [2, 3, 747497] ⟨4484983, 6, [(2, 1), (3, 1), (747497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_747497
  · decide +kernel

theorem prime_7443679 : Nat.Prime 7443679 := by
  apply nodeValid_prime [2, 3, 11, 10253] ⟨7443679, 6, [(2, 1), (3, 1), (11, 2), (10253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_10253
  · decide +kernel

theorem prime_8164697 : Nat.Prime 8164697 := by
  apply nodeValid_prime [2, 503, 2029] ⟨8164697, 3, [(2, 3), (503, 1), (2029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_503
    · exact prime_2029
  · decide +kernel

theorem prime_9228827 : Nat.Prime 9228827 := by
  apply nodeValid_prime [2, 47, 98179] ⟨9228827, 2, [(2, 1), (47, 1), (98179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_98179
  · decide +kernel

theorem prime_10372171 : Nat.Prime 10372171 := by
  apply nodeValid_prime [2, 3, 5, 345739] ⟨10372171, 17, [(2, 1), (3, 1), (5, 1), (345739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_345739
  · decide +kernel

theorem prime_13099291 : Nat.Prime 13099291 := by
  apply nodeValid_prime [2, 3, 5, 257, 1699] ⟨13099291, 2, [(2, 1), (3, 1), (5, 1), (257, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
    · exact prime_1699
  · decide +kernel

theorem prime_13240889 : Nat.Prime 13240889 := by
  apply nodeValid_prime [2, 97, 113, 151] ⟨13240889, 3, [(2, 3), (97, 1), (113, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_113
    · exact prime_151
  · decide +kernel

theorem prime_16484599 : Nat.Prime 16484599 := by
  apply nodeValid_prime [2, 3, 13, 5419] ⟨16484599, 3, [(2, 1), (3, 2), (13, 2), (5419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5419
  · decide +kernel

theorem prime_17826157 : Nat.Prime 17826157 := by
  apply nodeValid_prime [2, 3, 37, 1487] ⟨17826157, 2, [(2, 2), (3, 4), (37, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1487
  · decide +kernel

theorem prime_19299347 : Nat.Prime 19299347 := by
  apply nodeValid_prime [2, 11, 23, 43, 887] ⟨19299347, 5, [(2, 1), (11, 1), (23, 1), (43, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_43
    · exact prime_887
  · decide +kernel

theorem prime_26139067 : Nat.Prime 26139067 := by
  apply nodeValid_prime [2, 3, 4356511] ⟨26139067, 11, [(2, 1), (3, 1), (4356511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4356511
  · decide +kernel

theorem prime_30666379 : Nat.Prime 30666379 := by
  apply nodeValid_prime [2, 3, 31, 79, 2087] ⟨30666379, 2, [(2, 1), (3, 1), (31, 1), (79, 1), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_79
    · exact prime_2087
  · decide +kernel

theorem prime_31146677 : Nat.Prime 31146677 := by
  apply nodeValid_prime [2, 11, 137, 5167] ⟨31146677, 2, [(2, 2), (11, 1), (137, 1), (5167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_137
    · exact prime_5167
  · decide +kernel

theorem prime_36980819 : Nat.Prime 36980819 := by
  apply nodeValid_prime [2, 7, 2641487] ⟨36980819, 2, [(2, 1), (7, 1), (2641487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2641487
  · decide +kernel

theorem prime_46413557 : Nat.Prime 46413557 := by
  apply nodeValid_prime [2, 7, 1657627] ⟨46413557, 2, [(2, 2), (7, 1), (1657627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1657627
  · decide +kernel

theorem prime_50151319 : Nat.Prime 50151319 := by
  apply nodeValid_prime [2, 3, 7, 103, 11593] ⟨50151319, 6, [(2, 1), (3, 1), (7, 1), (103, 1), (11593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_11593
  · decide +kernel

theorem prime_50254339 : Nat.Prime 50254339 := by
  apply nodeValid_prime [2, 3, 139, 60257] ⟨50254339, 2, [(2, 1), (3, 1), (139, 1), (60257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_60257
  · decide +kernel

theorem prime_61474493 : Nat.Prime 61474493 := by
  apply nodeValid_prime [2, 23, 668201] ⟨61474493, 2, [(2, 2), (23, 1), (668201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_668201
  · decide +kernel

theorem prime_67126193 : Nat.Prime 67126193 := by
  apply nodeValid_prime [2, 7, 599341] ⟨67126193, 3, [(2, 4), (7, 1), (599341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_599341
  · decide +kernel

theorem prime_73961639 : Nat.Prime 73961639 := by
  apply nodeValid_prime [2, 36980819] ⟨73961639, 11, [(2, 1), (36980819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36980819
  · decide +kernel

theorem prime_77582171 : Nat.Prime 77582171 := by
  apply nodeValid_prime [2, 5, 1567, 4951] ⟨77582171, 2, [(2, 1), (5, 1), (1567, 1), (4951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1567
    · exact prime_4951
  · decide +kernel

theorem prime_114305759 : Nat.Prime 114305759 := by
  apply nodeValid_prime [2, 7, 8164697] ⟨114305759, 7, [(2, 1), (7, 1), (8164697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8164697
  · decide +kernel

theorem prime_115506841 : Nat.Prime 115506841 := by
  apply nodeValid_prime [2, 3, 5, 17, 41, 1381] ⟨115506841, 26, [(2, 3), (3, 1), (5, 1), (17, 1), (41, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_41
    · exact prime_1381
  · decide +kernel

theorem prime_120133361 : Nat.Prime 120133361 := by
  apply nodeValid_prime [2, 5, 1501667] ⟨120133361, 3, [(2, 4), (5, 1), (1501667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1501667
  · decide +kernel

theorem prime_120211213 : Nat.Prime 120211213 := by
  apply nodeValid_prime [2, 3, 11, 910691] ⟨120211213, 2, [(2, 2), (3, 1), (11, 1), (910691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_910691
  · decide +kernel

theorem prime_128740373 : Nat.Prime 128740373 := by
  apply nodeValid_prime [2, 173, 186041] ⟨128740373, 2, [(2, 2), (173, 1), (186041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_186041
  · decide +kernel

theorem prime_131614129 : Nat.Prime 131614129 := by
  apply nodeValid_prime [2, 3, 131, 6977] ⟨131614129, 17, [(2, 4), (3, 2), (131, 1), (6977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_6977
  · decide +kernel

theorem prime_158682311 : Nat.Prime 158682311 := by
  apply nodeValid_prime [2, 5, 3637, 4363] ⟨158682311, 7, [(2, 1), (5, 1), (3637, 1), (4363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3637
    · exact prime_4363
  · decide +kernel

theorem prime_203927233 : Nat.Prime 203927233 := by
  apply nodeValid_prime [2, 3, 1062121] ⟨203927233, 5, [(2, 6), (3, 1), (1062121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1062121
  · decide +kernel

theorem prime_207421343 : Nat.Prime 207421343 := by
  apply nodeValid_prime [2, 317, 327163] ⟨207421343, 5, [(2, 1), (317, 1), (327163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_327163
  · decide +kernel

theorem prime_210883807 : Nat.Prime 210883807 := by
  apply nodeValid_prime [2, 3, 7, 1673681] ⟨210883807, 3, [(2, 1), (3, 2), (7, 1), (1673681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1673681
  · decide +kernel

theorem prime_228611519 : Nat.Prime 228611519 := by
  apply nodeValid_prime [2, 114305759] ⟨228611519, 11, [(2, 1), (114305759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_114305759
  · decide +kernel

theorem prime_325750567 : Nat.Prime 325750567 := by
  apply nodeValid_prime [2, 3, 17, 3193633] ⟨325750567, 3, [(2, 1), (3, 1), (17, 1), (3193633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3193633
  · decide +kernel

theorem prime_437116513 : Nat.Prime 437116513 := by
  apply nodeValid_prime [2, 3, 7, 17, 83, 461] ⟨437116513, 26, [(2, 5), (3, 1), (7, 1), (17, 1), (83, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_83
    · exact prime_461
  · decide +kernel

theorem prime_443582437 : Nat.Prime 443582437 := by
  apply nodeValid_prime [2, 3, 11, 19, 137, 1291] ⟨443582437, 14, [(2, 2), (3, 1), (11, 1), (19, 1), (137, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_137
    · exact prime_1291
  · decide +kernel

theorem prime_634334341 : Nat.Prime 634334341 := by
  apply nodeValid_prime [2, 3, 5, 839, 12601] ⟨634334341, 2, [(2, 2), (3, 1), (5, 1), (839, 1), (12601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_839
    · exact prime_12601
  · decide +kernel

theorem prime_812387111 : Nat.Prime 812387111 := by
  apply nodeValid_prime [2, 5, 163, 498397] ⟨812387111, 7, [(2, 1), (5, 1), (163, 1), (498397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_498397
  · decide +kernel

theorem prime_1787766713 : Nat.Prime 1787766713 := by
  apply nodeValid_prime [2, 29, 1013, 7607] ⟨1787766713, 3, [(2, 3), (29, 1), (1013, 1), (7607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1013
    · exact prime_7607
  · decide +kernel

theorem prime_2192941291 : Nat.Prime 2192941291 := by
  apply nodeValid_prime [2, 3, 5, 101, 151, 4793] ⟨2192941291, 2, [(2, 1), (3, 1), (5, 1), (101, 1), (151, 1), (4793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_151
    · exact prime_4793
  · decide +kernel

theorem prime_2574807461 : Nat.Prime 2574807461 := by
  apply nodeValid_prime [2, 5, 128740373] ⟨2574807461, 3, [(2, 2), (5, 1), (128740373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_128740373
  · decide +kernel

theorem prime_4884631439 : Nat.Prime 4884631439 := by
  apply nodeValid_prime [2, 4261, 573179] ⟨4884631439, 7, [(2, 1), (4261, 1), (573179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4261
    · exact prime_573179
  · decide +kernel

theorem prime_5916931121 : Nat.Prime 5916931121 := by
  apply nodeValid_prime [2, 5, 73961639] ⟨5916931121, 3, [(2, 4), (5, 1), (73961639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73961639
  · decide +kernel

theorem prime_7097318993 : Nat.Prime 7097318993 := by
  apply nodeValid_prime [2, 443582437] ⟨7097318993, 3, [(2, 4), (443582437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_443582437
  · decide +kernel

theorem prime_7233982883 : Nat.Prime 7233982883 := by
  apply nodeValid_prime [2, 7, 227, 2276269] ⟨7233982883, 2, [(2, 1), (7, 1), (227, 1), (2276269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
    · exact prime_2276269
  · decide +kernel

theorem prime_8833698437 : Nat.Prime 8833698437 := by
  apply nodeValid_prime [2, 2689, 821281] ⟨8833698437, 2, [(2, 2), (2689, 1), (821281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2689
    · exact prime_821281
  · decide +kernel

theorem prime_11033465413 : Nat.Prime 11033465413 := by
  apply nodeValid_prime [2, 3, 5113, 179827] ⟨11033465413, 6, [(2, 2), (3, 1), (5113, 1), (179827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5113
    · exact prime_179827
  · decide +kernel

theorem prime_17175843281 : Nat.Prime 17175843281 := by
  apply nodeValid_prime [2, 5, 103, 2084447] ⟨17175843281, 3, [(2, 4), (5, 1), (103, 1), (2084447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_2084447
  · decide +kernel

theorem prime_17292381371 : Nat.Prime 17292381371 := by
  apply nodeValid_prime [2, 5, 11, 3943, 39869] ⟨17292381371, 6, [(2, 1), (5, 1), (11, 1), (3943, 1), (39869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3943
    · exact prime_39869
  · decide +kernel

theorem prime_21558730289 : Nat.Prime 21558730289 := by
  apply nodeValid_prime [2, 53, 61, 409, 1019] ⟨21558730289, 3, [(2, 4), (53, 1), (61, 1), (409, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_61
    · exact prime_409
    · exact prime_1019
  · decide +kernel

theorem prime_34584762743 : Nat.Prime 34584762743 := by
  apply nodeValid_prime [2, 17292381371] ⟨34584762743, 5, [(2, 1), (17292381371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17292381371
  · decide +kernel

theorem prime_61435280947 : Nat.Prime 61435280947 := by
  apply nodeValid_prime [2, 3, 13, 197, 3998131] ⟨61435280947, 2, [(2, 1), (3, 1), (13, 1), (197, 1), (3998131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_197
    · exact prime_3998131
  · decide +kernel

theorem prime_83890037431 : Nat.Prime 83890037431 := by
  apply nodeValid_prime [2, 3, 5, 101, 9228827] ⟨83890037431, 3, [(2, 1), (3, 2), (5, 1), (101, 1), (9228827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_9228827
  · decide +kernel

theorem prime_94451189449 : Nat.Prime 94451189449 := by
  apply nodeValid_prime [2, 3, 7, 11, 4159, 12289] ⟨94451189449, 13, [(2, 3), (3, 1), (7, 1), (11, 1), (4159, 1), (12289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_4159
    · exact prime_12289
  · decide +kernel

theorem prime_118338622421 : Nat.Prime 118338622421 := by
  apply nodeValid_prime [2, 5, 5916931121] ⟨118338622421, 7, [(2, 2), (5, 1), (5916931121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5916931121
  · decide +kernel

theorem prime_173615589193 : Nat.Prime 173615589193 := by
  apply nodeValid_prime [2, 3, 7233982883] ⟨173615589193, 5, [(2, 3), (3, 1), (7233982883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7233982883
  · decide +kernel

theorem prime_176010044641 : Nat.Prime 176010044641 := by
  apply nodeValid_prime [2, 3, 5, 19, 19299347] ⟨176010044641, 17, [(2, 5), (3, 1), (5, 1), (19, 1), (19299347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_19299347
  · decide +kernel

theorem prime_521920027259 : Nat.Prime 521920027259 := by
  apply nodeValid_prime [2, 7, 17, 2192941291] ⟨521920027259, 2, [(2, 1), (7, 1), (17, 1), (2192941291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_2192941291
  · decide +kernel

theorem prime_1822963682389 : Nat.Prime 1822963682389 := by
  apply nodeValid_prime [2, 3, 59, 2574807461] ⟨1822963682389, 2, [(2, 2), (3, 1), (59, 1), (2574807461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2574807461
  · decide +kernel

theorem prime_3676041531293 : Nat.Prime 3676041531293 := by
  apply nodeValid_prime [2, 13, 19, 281, 13240889] ⟨3676041531293, 2, [(2, 2), (13, 1), (19, 1), (281, 1), (13240889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_281
    · exact prime_13240889
  · decide +kernel

theorem prime_7281849286819 : Nat.Prime 7281849286819 := by
  apply nodeValid_prime [2, 3, 19, 7097318993] ⟨7281849286819, 2, [(2, 1), (3, 3), (19, 1), (7097318993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7097318993
  · decide +kernel

theorem prime_7281849415069 : Nat.Prime 7281849415069 := by
  apply nodeValid_prime [2, 3, 19, 29, 31, 173, 22817] ⟨7281849415069, 2, [(2, 2), (3, 3), (19, 1), (29, 1), (31, 1), (173, 1), (22817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_31
    · exact prime_173
    · exact prime_22817
  · decide +kernel

theorem prime_7281849416641 : Nat.Prime 7281849416641 := by
  apply nodeValid_prime [2, 3, 5, 113, 67126193] ⟨7281849416641, 11, [(2, 6), (3, 1), (5, 1), (113, 1), (67126193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_67126193
  · decide +kernel

theorem prime_7286850837683 : Nat.Prime 7286850837683 := by
  apply nodeValid_prime [2, 13, 21558730289] ⟨7286850837683, 2, [(2, 1), (13, 2), (21558730289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_21558730289
  · decide +kernel

theorem prime_7286850838079 : Nat.Prime 7286850838079 := by
  apply nodeValid_prime [2, 7, 19, 105361, 260003] ⟨7286850838079, 7, [(2, 1), (7, 1), (19, 1), (105361, 1), (260003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_105361
    · exact prime_260003
  · decide +kernel

theorem prime_7286850841211 : Nat.Prime 7286850841211 := by
  apply nodeValid_prime [2, 5, 43, 211, 1789, 44893] ⟨7286850841211, 2, [(2, 1), (5, 1), (43, 1), (211, 1), (1789, 1), (44893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_211
    · exact prime_1789
    · exact prime_44893
  · decide +kernel

theorem prime_7291854729557 : Nat.Prime 7291854729557 := by
  apply nodeValid_prime [2, 1822963682389] ⟨7291854729557, 2, [(2, 2), (1822963682389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1822963682389
  · decide +kernel

theorem prime_7291854745979 : Nat.Prime 7291854745979 := by
  apply nodeValid_prime [2, 11, 31, 89, 120133361] ⟨7291854745979, 6, [(2, 1), (11, 1), (31, 1), (89, 1), (120133361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_89
    · exact prime_120133361
  · decide +kernel

theorem prime_7291854746107 : Nat.Prime 7291854746107 := by
  apply nodeValid_prime [2, 3, 7, 173615589193] ⟨7291854746107, 2, [(2, 1), (3, 1), (7, 1), (173615589193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173615589193
  · decide +kernel

theorem prime_7296860950199 : Nat.Prime 7296860950199 := by
  apply nodeValid_prime [2, 78607, 46413557] ⟨7296860950199, 7, [(2, 1), (78607, 1), (46413557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_78607
    · exact prime_46413557
  · decide +kernel

theorem prime_7296861031003 : Nat.Prime 7296861031003 := by
  apply nodeValid_prime [2, 3, 499, 812387111] ⟨7296861031003, 5, [(2, 1), (3, 2), (499, 1), (812387111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_499
    · exact prime_812387111
  · decide +kernel

theorem prime_7296861031783 : Nat.Prime 7296861031783 := by
  apply nodeValid_prime [2, 3, 7, 38737, 4484983] ⟨7296861031783, 3, [(2, 1), (3, 1), (7, 1), (38737, 1), (4484983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_38737
    · exact prime_4484983
  · decide +kernel

theorem prime_7301869500047 : Nat.Prime 7301869500047 := by
  apply nodeValid_prime [2, 11, 251, 120211213] ⟨7301869500047, 10, [(2, 1), (11, 2), (251, 1), (120211213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_251
    · exact prime_120211213
  · decide +kernel

theorem prime_7301869513871 : Nat.Prime 7301869513871 := by
  apply nodeValid_prime [2, 5, 17, 149519, 287269] ⟨7301869513871, 11, [(2, 1), (5, 1), (17, 1), (149519, 1), (287269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_149519
    · exact prime_287269
  · decide +kernel

theorem prime_7306880381539 : Nat.Prime 7306880381539 := by
  apply nodeValid_prime [2, 3, 2749, 10847, 40841] ⟨7306880381539, 2, [(2, 1), (3, 1), (2749, 1), (10847, 1), (40841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2749
    · exact prime_10847
    · exact prime_40841
  · decide +kernel

theorem prime_7306880381627 : Nat.Prime 7306880381627 := by
  apply nodeValid_prime [2, 7, 521920027259] ⟨7306880381627, 2, [(2, 1), (7, 1), (521920027259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_521920027259
  · decide +kernel

theorem prime_7306880381923 : Nat.Prime 7306880381923 := by
  apply nodeValid_prime [2, 3, 11, 2203, 50254339] ⟨7306880381923, 2, [(2, 1), (3, 1), (11, 1), (2203, 1), (50254339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2203
    · exact prime_50254339
  · decide +kernel

theorem prime_7311893590187 : Nat.Prime 7311893590187 := by
  apply nodeValid_prime [2, 17, 113, 15683, 121351] ⟨7311893590187, 2, [(2, 1), (17, 1), (113, 1), (15683, 1), (121351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_113
    · exact prime_15683
    · exact prime_121351
  · decide +kernel

theorem prime_7311893606593 : Nat.Prime 7311893606593 := by
  apply nodeValid_prime [2, 3, 9239, 4121959] ⟨7311893606593, 5, [(2, 6), (3, 1), (9239, 1), (4121959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9239
    · exact prime_4121959
  · decide +kernel

theorem prime_7311893607871 : Nat.Prime 7311893607871 := by
  apply nodeValid_prime [2, 3, 5, 87407, 2788447] ⟨7311893607871, 15, [(2, 1), (3, 1), (5, 1), (87407, 1), (2788447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_87407
    · exact prime_2788447
  · decide +kernel

theorem prime_7316909120041 : Nat.Prime 7316909120041 := by
  apply nodeValid_prime [2, 3, 5, 13, 23, 203927233] ⟨7316909120041, 35, [(2, 3), (3, 1), (5, 1), (13, 1), (23, 1), (203927233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_203927233
  · decide +kernel

theorem prime_7316909237707 : Nat.Prime 7316909237707 := by
  apply nodeValid_prime [2, 3, 71, 17175843281] ⟨7316909237707, 2, [(2, 1), (3, 1), (71, 1), (17175843281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_17175843281
  · decide +kernel

theorem prime_7316909239741 : Nat.Prime 7316909239741 := by
  apply nodeValid_prime [2, 3, 5, 145969, 835441] ⟨7316909239741, 6, [(2, 2), (3, 1), (5, 1), (145969, 1), (835441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_145969
    · exact prime_835441
  · decide +kernel

theorem prime_7321926974317 : Nat.Prime 7321926974317 := by
  apply nodeValid_prime [2, 3, 113, 4889, 1104449] ⟨7321926974317, 5, [(2, 2), (3, 1), (113, 1), (4889, 1), (1104449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_4889
    · exact prime_1104449
  · decide +kernel

theorem prime_7321926976489 : Nat.Prime 7321926976489 := by
  apply nodeValid_prime [2, 3, 547, 811, 229237] ⟨7321926976489, 7, [(2, 3), (3, 2), (547, 1), (811, 1), (229237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_547
    · exact prime_811
    · exact prime_229237
  · decide +kernel

theorem prime_7321926979841 : Nat.Prime 7321926979841 := by
  apply nodeValid_prime [2, 5, 11, 683, 761381] ⟨7321926979841, 12, [(2, 8), (5, 1), (11, 1), (683, 1), (761381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_683
    · exact prime_761381
  · decide +kernel

theorem prime_7326946990409 : Nat.Prime 7326946990409 := by
  apply nodeValid_prime [2, 43, 101, 210883807] ⟨7326946990409, 3, [(2, 3), (43, 1), (101, 1), (210883807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_101
    · exact prime_210883807
  · decide +kernel

theorem prime_7326946990907 : Nat.Prime 7326946990907 := by
  apply nodeValid_prime [2, 17, 29, 437116513] ⟨7326946990907, 5, [(2, 1), (17, 2), (29, 1), (437116513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_437116513
  · decide +kernel

theorem prime_7326947158501 : Nat.Prime 7326947158501 := by
  apply nodeValid_prime [2, 3, 5, 4884631439] ⟨7326947158501, 10, [(2, 2), (3, 1), (5, 3), (4884631439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4884631439
  · decide +kernel

theorem prime_7331969678729 : Nat.Prime 7331969678729 := by
  apply nodeValid_prime [2, 51413, 17826157] ⟨7331969678729, 3, [(2, 3), (51413, 1), (17826157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_51413
    · exact prime_17826157
  · decide +kernel

theorem prime_7331969701517 : Nat.Prime 7331969701517 := by
  apply nodeValid_prime [2, 53, 34584762743] ⟨7331969701517, 2, [(2, 2), (53, 1), (34584762743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_34584762743
  · decide +kernel

theorem prime_7331969702711 : Nat.Prime 7331969702711 := by
  apply nodeValid_prime [2, 5, 83, 8833698437] ⟨7331969702711, 22, [(2, 1), (5, 1), (83, 1), (8833698437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_8833698437
  · decide +kernel

theorem prime_7336994540321 : Nat.Prime 7336994540321 := by
  apply nodeValid_prime [2, 5, 397, 115506841] ⟨7336994540321, 3, [(2, 5), (5, 1), (397, 1), (115506841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_397
    · exact prime_115506841
  · decide +kernel

theorem prime_7336994590103 : Nat.Prime 7336994590103 := by
  apply nodeValid_prime [2, 31, 118338622421] ⟨7336994590103, 5, [(2, 1), (31, 1), (118338622421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_118338622421
  · decide +kernel

theorem prime_7336994590153 : Nat.Prime 7336994590153 := by
  apply nodeValid_prime [2, 3, 19, 1787766713] ⟨7336994590153, 5, [(2, 3), (3, 3), (19, 1), (1787766713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1787766713
  · decide +kernel

theorem prime_7342021647781 : Nat.Prime 7342021647781 := by
  apply nodeValid_prime [2, 3, 5, 17, 38677, 186107] ⟨7342021647781, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (38677, 1), (186107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_38677
    · exact prime_186107
  · decide +kernel

theorem prime_7342021647977 : Nat.Prime 7342021647977 := by
  apply nodeValid_prime [2, 14929, 61474493] ⟨7342021647977, 3, [(2, 3), (14929, 1), (61474493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_14929
    · exact prime_61474493
  · decide +kernel

theorem prime_7342021730297 : Nat.Prime 7342021730297 := by
  apply nodeValid_prime [2, 11, 119827, 696271] ⟨7342021730297, 3, [(2, 3), (11, 1), (119827, 1), (696271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_119827
    · exact prime_696271
  · decide +kernel

theorem prime_7347051080821 : Nat.Prime 7347051080821 := by
  apply nodeValid_prime [2, 3, 5, 11, 30666379] ⟨7347051080821, 10, [(2, 2), (3, 2), (5, 1), (11, 3), (30666379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_30666379
  · decide +kernel

theorem prime_7347051081257 : Nat.Prime 7347051081257 := by
  apply nodeValid_prime [2, 17, 2027, 4219, 6317] ⟨7347051081257, 3, [(2, 3), (17, 1), (2027, 1), (4219, 1), (6317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2027
    · exact prime_4219
    · exact prime_6317
  · decide +kernel

theorem prime_7347051253669 : Nat.Prime 7347051253669 := by
  apply nodeValid_prime [2, 3, 7, 193, 353, 811, 1583] ⟨7347051253669, 2, [(2, 2), (3, 1), (7, 1), (193, 1), (353, 1), (811, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_193
    · exact prime_353
    · exact prime_811
    · exact prime_1583
  · decide +kernel

theorem prime_7352083062587 : Nat.Prime 7352083062587 := by
  apply nodeValid_prime [2, 3676041531293] ⟨7352083062587, 2, [(2, 1), (3676041531293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3676041531293
  · decide +kernel

theorem prime_7352083062763 : Nat.Prime 7352083062763 := by
  apply nodeValid_prime [2, 3, 53, 461, 50151319] ⟨7352083062763, 2, [(2, 1), (3, 1), (53, 1), (461, 1), (50151319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_461
    · exact prime_50151319
  · decide +kernel

theorem prime_7352083096957 : Nat.Prime 7352083096957 := by
  apply nodeValid_prime [2, 3, 13, 601, 26139067] ⟨7352083096957, 2, [(2, 2), (3, 2), (13, 1), (601, 1), (26139067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_601
    · exact prime_26139067
  · decide +kernel

theorem prime_7357117219393 : Nat.Prime 7357117219393 := by
  apply nodeValid_prime [2, 3, 151, 4957, 51193] ⟨7357117219393, 5, [(2, 6), (3, 1), (151, 1), (4957, 1), (51193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_4957
    · exact prime_51193
  · decide +kernel

theorem prime_7357117219709 : Nat.Prime 7357117219709 := by
  apply nodeValid_prime [2, 1933, 3833, 248243] ⟨7357117219709, 2, [(2, 2), (1933, 1), (3833, 1), (248243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1933
    · exact prime_3833
    · exact prime_248243
  · decide +kernel

theorem prime_7357117275931 : Nat.Prime 7357117275931 := by
  apply nodeValid_prime [2, 3, 5, 29, 109, 77582171] ⟨7357117275931, 11, [(2, 1), (3, 1), (5, 1), (29, 1), (109, 1), (77582171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_109
    · exact prime_77582171
  · decide +kernel

theorem prime_7362153788923 : Nat.Prime 7362153788923 := by
  apply nodeValid_prime [2, 3, 193, 331, 1289, 4967] ⟨7362153788923, 3, [(2, 1), (3, 2), (193, 1), (331, 1), (1289, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_331
    · exact prime_1289
    · exact prime_4967
  · decide +kernel

theorem prime_7362153790193 : Nat.Prime 7362153790193 := by
  apply nodeValid_prime [2, 103, 271, 16484599] ⟨7362153790193, 3, [(2, 4), (103, 1), (271, 1), (16484599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_271
    · exact prime_16484599
  · decide +kernel

theorem prime_7362153793717 : Nat.Prime 7362153793717 := by
  apply nodeValid_prime [2, 3, 41, 229, 1973, 33119] ⟨7362153793717, 5, [(2, 2), (3, 1), (41, 1), (229, 1), (1973, 1), (33119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_229
    · exact prime_1973
    · exact prime_33119
  · decide +kernel

theorem prime_7367192648077 : Nat.Prime 7367192648077 := by
  apply nodeValid_prime [2, 3, 89, 8999, 766543] ⟨7367192648077, 2, [(2, 2), (3, 1), (89, 1), (8999, 1), (766543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_8999
    · exact prime_766543
  · decide +kernel

theorem prime_7367192776651 : Nat.Prime 7367192776651 := by
  apply nodeValid_prime [2, 3, 5, 7, 20147, 348259] ⟨7367192776651, 7, [(2, 1), (3, 1), (5, 2), (7, 1), (20147, 1), (348259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_20147
    · exact prime_348259
  · decide +kernel

theorem prime_7367192777023 : Nat.Prime 7367192777023 := by
  apply nodeValid_prime [2, 3, 13, 94451189449] ⟨7367192777023, 3, [(2, 1), (3, 1), (13, 1), (94451189449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_94451189449
  · decide +kernel

theorem prime_7372233711103 : Nat.Prime 7372233711103 := by
  apply nodeValid_prime [2, 3, 13, 149, 634334341] ⟨7372233711103, 6, [(2, 1), (3, 1), (13, 1), (149, 1), (634334341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_149
    · exact prime_634334341
  · decide +kernel

theorem prime_7372233713641 : Nat.Prime 7372233713641 := by
  apply nodeValid_prime [2, 3, 5, 61435280947] ⟨7372233713641, 7, [(2, 3), (3, 1), (5, 1), (61435280947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61435280947
  · decide +kernel

theorem prime_7372233821807 : Nat.Prime 7372233821807 := by
  apply nodeValid_prime [2, 7, 4001, 131614129] ⟨7372233821807, 5, [(2, 1), (7, 1), (4001, 1), (131614129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4001
    · exact prime_131614129
  · decide +kernel

theorem prime_7377277230529 : Nat.Prime 7377277230529 := by
  apply nodeValid_prime [2, 3, 23, 1489, 1121947] ⟨7377277230529, 7, [(2, 6), (3, 1), (23, 1), (1489, 1), (1121947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1489
    · exact prime_1121947
  · decide +kernel

theorem prime_7377277231799 : Nat.Prime 7377277231799 := by
  apply nodeValid_prime [2, 19, 29, 43, 8951, 17393] ⟨7377277231799, 13, [(2, 1), (19, 1), (29, 1), (43, 1), (8951, 1), (17393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_43
    · exact prime_8951
    · exact prime_17393
  · decide +kernel

theorem prime_7377277327513 : Nat.Prime 7377277327513 := by
  apply nodeValid_prime [2, 3, 71, 139, 31146677] ⟨7377277327513, 5, [(2, 3), (3, 1), (71, 1), (139, 1), (31146677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_139
    · exact prime_31146677
  · decide +kernel

theorem prime_7382323171549 : Nat.Prime 7382323171549 := by
  apply nodeValid_prime [2, 3, 13, 23, 228611519] ⟨7382323171549, 2, [(2, 2), (3, 3), (13, 1), (23, 1), (228611519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_228611519
  · decide +kernel

theorem prime_7382323293929 : Nat.Prime 7382323293929 := by
  apply nodeValid_prime [2, 11, 83890037431] ⟨7382323293929, 3, [(2, 3), (11, 1), (83890037431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83890037431
  · decide +kernel

theorem prime_7387371351331 : Nat.Prime 7387371351331 := by
  apply nodeValid_prime [2, 3, 5, 23741, 10372171] ⟨7387371351331, 2, [(2, 1), (3, 1), (5, 1), (23741, 1), (10372171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23741
    · exact prime_10372171
  · decide +kernel

theorem prime_7387371358033 : Nat.Prime 7387371358033 := by
  apply nodeValid_prime [2, 3, 31, 379, 13099291] ⟨7387371358033, 5, [(2, 4), (3, 1), (31, 1), (379, 1), (13099291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_379
    · exact prime_13099291
  · decide +kernel

theorem prime_7387371358427 : Nat.Prime 7387371358427 := by
  apply nodeValid_prime [2, 17, 23, 29, 325750567] ⟨7387371358427, 5, [(2, 1), (17, 1), (23, 1), (29, 1), (325750567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_29
    · exact prime_325750567
  · decide +kernel

theorem prime_7392421826407 : Nat.Prime 7392421826407 := by
  apply nodeValid_prime [2, 3, 53, 347, 7443679] ⟨7392421826407, 5, [(2, 1), (3, 3), (53, 1), (347, 1), (7443679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_347
    · exact prime_7443679
  · decide +kernel

theorem prime_7392421826711 : Nat.Prime 7392421826711 := by
  apply nodeValid_prime [2, 5, 67, 11033465413] ⟨7392421826711, 11, [(2, 1), (5, 1), (67, 1), (11033465413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_11033465413
  · decide +kernel

theorem prime_7392421874923 : Nat.Prime 7392421874923 := by
  apply nodeValid_prime [2, 3, 7, 176010044641] ⟨7392421874923, 2, [(2, 1), (3, 1), (7, 1), (176010044641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_176010044641
  · decide +kernel

theorem prime_7397474730043 : Nat.Prime 7397474730043 := by
  apply nodeValid_prime [2, 3, 277, 31531, 141161] ⟨7397474730043, 3, [(2, 1), (3, 1), (277, 1), (31531, 1), (141161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_31531
    · exact prime_141161
  · decide +kernel

theorem prime_7397474776427 : Nat.Prime 7397474776427 := by
  apply nodeValid_prime [2, 7, 59, 11519, 777479] ⟨7397474776427, 5, [(2, 1), (7, 1), (59, 1), (11519, 1), (777479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_11519
    · exact prime_777479
  · decide +kernel

theorem prime_7397474776753 : Nat.Prime 7397474776753 := by
  apply nodeValid_prime [2, 3, 743, 207421343] ⟨7397474776753, 5, [(2, 4), (3, 1), (743, 1), (207421343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_743
    · exact prime_207421343
  · decide +kernel

theorem prime_7402529806907 : Nat.Prime 7402529806907 := by
  apply nodeValid_prime [2, 13, 17, 29, 311, 1856947] ⟨7402529806907, 2, [(2, 1), (13, 1), (17, 1), (29, 1), (311, 1), (1856947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_29
    · exact prime_311
    · exact prime_1856947
  · decide +kernel

theorem prime_7402529808151 : Nat.Prime 7402529808151 := by
  apply nodeValid_prime [2, 3, 5, 311, 158682311] ⟨7402529808151, 6, [(2, 1), (3, 1), (5, 2), (311, 1), (158682311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_311
    · exact prime_158682311
  · decide +kernel

theorem prime_7402529925221 : Nat.Prime 7402529925221 := by
  apply nodeValid_prime [2, 5, 109, 51797, 65557] ⟨7402529925221, 2, [(2, 2), (5, 1), (109, 1), (51797, 1), (65557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_51797
    · exact prime_65557
  · decide +kernel

end Sude.Lucas.Generated
