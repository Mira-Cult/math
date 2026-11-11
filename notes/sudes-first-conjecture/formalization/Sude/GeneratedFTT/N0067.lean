import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
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
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0066

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7433 : Nat.Prime 7433 := by
  apply nodeValid_prime [2, 929] ⟨7433, 3, [(2, 3), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_929
  · decide +kernel

theorem prime_10141 : Nat.Prime 10141 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨10141, 2, [(2, 2), (3, 1), (5, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_11351 : Nat.Prime 11351 := by
  apply nodeValid_prime [2, 5, 227] ⟨11351, 7, [(2, 1), (5, 2), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
  · decide +kernel

theorem prime_11597 : Nat.Prime 11597 := by
  apply nodeValid_prime [2, 13, 223] ⟨11597, 3, [(2, 2), (13, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_223
  · decide +kernel

theorem prime_12479 : Nat.Prime 12479 := by
  apply nodeValid_prime [2, 17, 367] ⟨12479, 23, [(2, 1), (17, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_367
  · decide +kernel

theorem prime_12647 : Nat.Prime 12647 := by
  apply nodeValid_prime [2, 6323] ⟨12647, 5, [(2, 1), (6323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6323
  · decide +kernel

theorem prime_13999 : Nat.Prime 13999 := by
  apply nodeValid_prime [2, 3, 2333] ⟨13999, 3, [(2, 1), (3, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2333
  · decide +kernel

theorem prime_19259 : Nat.Prime 19259 := by
  apply nodeValid_prime [2, 9629] ⟨19259, 2, [(2, 1), (9629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9629
  · decide +kernel

theorem prime_23459 : Nat.Prime 23459 := by
  apply nodeValid_prime [2, 37, 317] ⟨23459, 2, [(2, 1), (37, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_317
  · decide +kernel

theorem prime_23911 : Nat.Prime 23911 := by
  apply nodeValid_prime [2, 3, 5, 797] ⟨23911, 6, [(2, 1), (3, 1), (5, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_797
  · decide +kernel

theorem prime_27739 : Nat.Prime 27739 := by
  apply nodeValid_prime [2, 3, 23, 67] ⟨27739, 3, [(2, 1), (3, 2), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_28027 : Nat.Prime 28027 := by
  apply nodeValid_prime [2, 3, 173] ⟨28027, 2, [(2, 1), (3, 4), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
  · decide +kernel

theorem prime_28309 : Nat.Prime 28309 := by
  apply nodeValid_prime [2, 3, 7, 337] ⟨28309, 2, [(2, 2), (3, 1), (7, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_337
  · decide +kernel

theorem prime_32203 : Nat.Prime 32203 := by
  apply nodeValid_prime [2, 3, 1789] ⟨32203, 2, [(2, 1), (3, 2), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1789
  · decide +kernel

theorem prime_32609 : Nat.Prime 32609 := by
  apply nodeValid_prime [2, 1019] ⟨32609, 3, [(2, 5), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1019
  · decide +kernel

theorem prime_33997 : Nat.Prime 33997 := by
  apply nodeValid_prime [2, 3, 2833] ⟨33997, 2, [(2, 2), (3, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2833
  · decide +kernel

theorem prime_34313 : Nat.Prime 34313 := by
  apply nodeValid_prime [2, 4289] ⟨34313, 3, [(2, 3), (4289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4289
  · decide +kernel

theorem prime_35363 : Nat.Prime 35363 := by
  apply nodeValid_prime [2, 17681] ⟨35363, 2, [(2, 1), (17681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17681
  · decide +kernel

theorem prime_37537 : Nat.Prime 37537 := by
  apply nodeValid_prime [2, 3, 17, 23] ⟨37537, 13, [(2, 5), (3, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_40193 : Nat.Prime 40193 := by
  apply nodeValid_prime [2, 157] ⟨40193, 3, [(2, 8), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_157
  · decide +kernel

theorem prime_44207 : Nat.Prime 44207 := by
  apply nodeValid_prime [2, 23, 31] ⟨44207, 5, [(2, 1), (23, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_48751 : Nat.Prime 48751 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨48751, 3, [(2, 1), (3, 1), (5, 4), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_49253 : Nat.Prime 49253 := by
  apply nodeValid_prime [2, 7, 1759] ⟨49253, 2, [(2, 2), (7, 1), (1759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1759
  · decide +kernel

theorem prime_49921 : Nat.Prime 49921 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨49921, 23, [(2, 8), (3, 1), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_52567 : Nat.Prime 52567 := by
  apply nodeValid_prime [2, 3, 8761] ⟨52567, 3, [(2, 1), (3, 1), (8761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8761
  · decide +kernel

theorem prime_54949 : Nat.Prime 54949 := by
  apply nodeValid_prime [2, 3, 19, 241] ⟨54949, 2, [(2, 2), (3, 1), (19, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_241
  · decide +kernel

theorem prime_59723 : Nat.Prime 59723 := by
  apply nodeValid_prime [2, 13, 2297] ⟨59723, 2, [(2, 1), (13, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2297
  · decide +kernel

theorem prime_60257 : Nat.Prime 60257 := by
  apply nodeValid_prime [2, 7, 269] ⟨60257, 3, [(2, 5), (7, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_269
  · decide +kernel

theorem prime_66643 : Nat.Prime 66643 := by
  apply nodeValid_prime [2, 3, 29, 383] ⟨66643, 2, [(2, 1), (3, 1), (29, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_383
  · decide +kernel

theorem prime_74377 : Nat.Prime 74377 := by
  apply nodeValid_prime [2, 3, 1033] ⟨74377, 5, [(2, 3), (3, 2), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
  · decide +kernel

theorem prime_75883 : Nat.Prime 75883 := by
  apply nodeValid_prime [2, 3, 12647] ⟨75883, 2, [(2, 1), (3, 1), (12647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12647
  · decide +kernel

theorem prime_80221 : Nat.Prime 80221 := by
  apply nodeValid_prime [2, 3, 5, 7, 191] ⟨80221, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_191
  · decide +kernel

theorem prime_80387 : Nat.Prime 80387 := by
  apply nodeValid_prime [2, 40193] ⟨80387, 2, [(2, 1), (40193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40193
  · decide +kernel

theorem prime_86029 : Nat.Prime 86029 := by
  apply nodeValid_prime [2, 3, 67, 107] ⟨86029, 2, [(2, 2), (3, 1), (67, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_107
  · decide +kernel

theorem prime_89209 : Nat.Prime 89209 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨89209, 22, [(2, 3), (3, 3), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_89527 : Nat.Prime 89527 := by
  apply nodeValid_prime [2, 3, 43, 347] ⟨89527, 3, [(2, 1), (3, 1), (43, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_347
  · decide +kernel

theorem prime_107741 : Nat.Prime 107741 := by
  apply nodeValid_prime [2, 5, 5387] ⟨107741, 3, [(2, 2), (5, 1), (5387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5387
  · decide +kernel

theorem prime_108929 : Nat.Prime 108929 := by
  apply nodeValid_prime [2, 23, 37] ⟨108929, 3, [(2, 7), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_133723 : Nat.Prime 133723 := by
  apply nodeValid_prime [2, 3, 17, 19, 23] ⟨133723, 2, [(2, 1), (3, 2), (17, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_138893 : Nat.Prime 138893 := by
  apply nodeValid_prime [2, 13, 2671] ⟨138893, 2, [(2, 2), (13, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2671
  · decide +kernel

theorem prime_140527 : Nat.Prime 140527 := by
  apply nodeValid_prime [2, 3, 37, 211] ⟨140527, 5, [(2, 1), (3, 2), (37, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_211
  · decide +kernel

theorem prime_142427 : Nat.Prime 142427 := by
  apply nodeValid_prime [2, 17, 59, 71] ⟨142427, 5, [(2, 1), (17, 1), (59, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
    · exact prime_71
  · decide +kernel

theorem prime_161093 : Nat.Prime 161093 := by
  apply nodeValid_prime [2, 17, 23, 103] ⟨161093, 3, [(2, 2), (17, 1), (23, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_103
  · decide +kernel

theorem prime_161743 : Nat.Prime 161743 := by
  apply nodeValid_prime [2, 3, 7, 3851] ⟨161743, 5, [(2, 1), (3, 1), (7, 1), (3851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3851
  · decide +kernel

theorem prime_187123 : Nat.Prime 187123 := by
  apply nodeValid_prime [2, 3, 13, 2399] ⟨187123, 2, [(2, 1), (3, 1), (13, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2399
  · decide +kernel

theorem prime_188107 : Nat.Prime 188107 := by
  apply nodeValid_prime [2, 3, 107, 293] ⟨188107, 3, [(2, 1), (3, 1), (107, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_293
  · decide +kernel

theorem prime_197621 : Nat.Prime 197621 := by
  apply nodeValid_prime [2, 5, 41, 241] ⟨197621, 2, [(2, 2), (5, 1), (41, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_241
  · decide +kernel

theorem prime_203807 : Nat.Prime 203807 := by
  apply nodeValid_prime [2, 181, 563] ⟨203807, 5, [(2, 1), (181, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_563
  · decide +kernel

theorem prime_299527 : Nat.Prime 299527 := by
  apply nodeValid_prime [2, 3, 49921] ⟨299527, 3, [(2, 1), (3, 1), (49921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49921
  · decide +kernel

theorem prime_319159 : Nat.Prime 319159 := by
  apply nodeValid_prime [2, 3, 7, 17, 149] ⟨319159, 3, [(2, 1), (3, 2), (7, 1), (17, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_149
  · decide +kernel

theorem prime_335171 : Nat.Prime 335171 := by
  apply nodeValid_prime [2, 5, 11, 277] ⟨335171, 2, [(2, 1), (5, 1), (11, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_277
  · decide +kernel

theorem prime_358109 : Nat.Prime 358109 := by
  apply nodeValid_prime [2, 89527] ⟨358109, 2, [(2, 2), (89527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_89527
  · decide +kernel

theorem prime_395243 : Nat.Prime 395243 := by
  apply nodeValid_prime [2, 197621] ⟨395243, 2, [(2, 1), (197621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_197621
  · decide +kernel

theorem prime_510847 : Nat.Prime 510847 := by
  apply nodeValid_prime [2, 3, 7, 12163] ⟨510847, 3, [(2, 1), (3, 1), (7, 1), (12163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12163
  · decide +kernel

theorem prime_526511 : Nat.Prime 526511 := by
  apply nodeValid_prime [2, 5, 37, 1423] ⟨526511, 13, [(2, 1), (5, 1), (37, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1423
  · decide +kernel

theorem prime_663547 : Nat.Prime 663547 := by
  apply nodeValid_prime [2, 3, 13, 47, 181] ⟨663547, 2, [(2, 1), (3, 1), (13, 1), (47, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
    · exact prime_181
  · decide +kernel

theorem prime_670343 : Nat.Prime 670343 := by
  apply nodeValid_prime [2, 335171] ⟨670343, 5, [(2, 1), (335171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_335171
  · decide +kernel

theorem prime_740189 : Nat.Prime 740189 := by
  apply nodeValid_prime [2, 211, 877] ⟨740189, 2, [(2, 2), (211, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_877
  · decide +kernel

theorem prime_846493 : Nat.Prime 846493 := by
  apply nodeValid_prime [2, 3, 23, 3067] ⟨846493, 2, [(2, 2), (3, 1), (23, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3067
  · decide +kernel

theorem prime_860291 : Nat.Prime 860291 := by
  apply nodeValid_prime [2, 5, 86029] ⟨860291, 6, [(2, 1), (5, 1), (86029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_86029
  · decide +kernel

theorem prime_927961 : Nat.Prime 927961 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 37] ⟨927961, 7, [(2, 3), (3, 1), (5, 1), (11, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_934721 : Nat.Prime 934721 := by
  apply nodeValid_prime [2, 5, 23, 127] ⟨934721, 3, [(2, 6), (5, 1), (23, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_127
  · decide +kernel

theorem prime_949261 : Nat.Prime 949261 := by
  apply nodeValid_prime [2, 3, 5, 13, 1217] ⟨949261, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1217
  · decide +kernel

theorem prime_1098017 : Nat.Prime 1098017 := by
  apply nodeValid_prime [2, 34313] ⟨1098017, 3, [(2, 5), (34313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34313
  · decide +kernel

theorem prime_1236901 : Nat.Prime 1236901 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 31] ⟨1236901, 6, [(2, 2), (3, 1), (5, 2), (7, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_1305679 : Nat.Prime 1305679 := by
  apply nodeValid_prime [2, 3, 11, 73, 271] ⟨1305679, 7, [(2, 1), (3, 1), (11, 1), (73, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_271
  · decide +kernel

theorem prime_1350343 : Nat.Prime 1350343 := by
  apply nodeValid_prime [2, 3, 7, 1531] ⟨1350343, 3, [(2, 1), (3, 2), (7, 2), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1531
  · decide +kernel

theorem prime_1400107 : Nat.Prime 1400107 := by
  apply nodeValid_prime [2, 3, 229, 1019] ⟨1400107, 3, [(2, 1), (3, 1), (229, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_1019
  · decide +kernel

theorem prime_1432547 : Nat.Prime 1432547 := by
  apply nodeValid_prime [2, 283, 2531] ⟨1432547, 2, [(2, 1), (283, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_2531
  · decide +kernel

theorem prime_1929289 : Nat.Prime 1929289 := by
  apply nodeValid_prime [2, 3, 80387] ⟨1929289, 13, [(2, 3), (3, 1), (80387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80387
  · decide +kernel

theorem prime_2178359 : Nat.Prime 2178359 := by
  apply nodeValid_prime [2, 7, 13, 11969] ⟨2178359, 7, [(2, 1), (7, 1), (13, 1), (11969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_11969
  · decide +kernel

theorem prime_2371459 : Nat.Prime 2371459 := by
  apply nodeValid_prime [2, 3, 395243] ⟨2371459, 2, [(2, 1), (3, 1), (395243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_395243
  · decide +kernel

theorem prime_2848541 : Nat.Prime 2848541 := by
  apply nodeValid_prime [2, 5, 142427] ⟨2848541, 7, [(2, 2), (5, 1), (142427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_142427
  · decide +kernel

theorem prime_3153191 : Nat.Prime 3153191 := by
  apply nodeValid_prime [2, 5, 43, 7333] ⟨3153191, 13, [(2, 1), (5, 1), (43, 1), (7333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_7333
  · decide +kernel

theorem prime_3159067 : Nat.Prime 3159067 := by
  apply nodeValid_prime [2, 3, 526511] ⟨3159067, 3, [(2, 1), (3, 1), (526511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_526511
  · decide +kernel

theorem prime_4189733 : Nat.Prime 4189733 := by
  apply nodeValid_prime [2, 37, 28309] ⟨4189733, 2, [(2, 2), (37, 1), (28309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_28309
  · decide +kernel

theorem prime_5738641 : Nat.Prime 5738641 := by
  apply nodeValid_prime [2, 3, 5, 23911] ⟨5738641, 11, [(2, 4), (3, 1), (5, 1), (23911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23911
  · decide +kernel

theorem prime_6039193 : Nat.Prime 6039193 := by
  apply nodeValid_prime [2, 3, 29, 8677] ⟨6039193, 7, [(2, 3), (3, 1), (29, 1), (8677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_8677
  · decide +kernel

theorem prime_6306383 : Nat.Prime 6306383 := by
  apply nodeValid_prime [2, 3153191] ⟨6306383, 5, [(2, 1), (3153191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3153191
  · decide +kernel

theorem prime_7059179 : Nat.Prime 7059179 := by
  apply nodeValid_prime [2, 7, 449, 1123] ⟨7059179, 2, [(2, 1), (7, 1), (449, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_449
    · exact prime_1123
  · decide +kernel

theorem prime_8498873 : Nat.Prime 8498873 := by
  apply nodeValid_prime [2, 389, 2731] ⟨8498873, 3, [(2, 3), (389, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_389
    · exact prime_2731
  · decide +kernel

theorem prime_8985811 : Nat.Prime 8985811 := by
  apply nodeValid_prime [2, 3, 5, 299527] ⟨8985811, 2, [(2, 1), (3, 1), (5, 1), (299527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_299527
  · decide +kernel

theorem prime_9038551 : Nat.Prime 9038551 := by
  apply nodeValid_prime [2, 3, 5, 60257] ⟨9038551, 3, [(2, 1), (3, 1), (5, 2), (60257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_60257
  · decide +kernel

theorem prime_13174037 : Nat.Prime 13174037 := by
  apply nodeValid_prime [2, 101, 32609] ⟨13174037, 2, [(2, 2), (101, 1), (32609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_32609
  · decide +kernel

theorem prime_17949389 : Nat.Prime 17949389 := by
  apply nodeValid_prime [2, 233, 19259] ⟨17949389, 2, [(2, 2), (233, 1), (19259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_19259
  · decide +kernel

theorem prime_19486133 : Nat.Prime 19486133 := by
  apply nodeValid_prime [2, 101, 139, 347] ⟨19486133, 2, [(2, 2), (101, 1), (139, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_139
    · exact prime_347
  · decide +kernel

theorem prime_20371159 : Nat.Prime 20371159 := by
  apply nodeValid_prime [2, 3, 683, 1657] ⟨20371159, 6, [(2, 1), (3, 2), (683, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_1657
  · decide +kernel

theorem prime_23714591 : Nat.Prime 23714591 := by
  apply nodeValid_prime [2, 5, 2371459] ⟨23714591, 19, [(2, 1), (5, 1), (2371459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2371459
  · decide +kernel

theorem prime_29191189 : Nat.Prime 29191189 := by
  apply nodeValid_prime [2, 3, 13, 187123] ⟨29191189, 2, [(2, 2), (3, 1), (13, 1), (187123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_187123
  · decide +kernel

theorem prime_30970477 : Nat.Prime 30970477 := by
  apply nodeValid_prime [2, 3, 860291] ⟨30970477, 5, [(2, 2), (3, 2), (860291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_860291
  · decide +kernel

theorem prime_32643557 : Nat.Prime 32643557 := by
  apply nodeValid_prime [2, 11, 73, 10163] ⟨32643557, 2, [(2, 2), (11, 1), (73, 1), (10163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_10163
  · decide +kernel

theorem prime_40039189 : Nat.Prime 40039189 := by
  apply nodeValid_prime [2, 3, 7, 109, 4373] ⟨40039189, 2, [(2, 2), (3, 1), (7, 1), (109, 1), (4373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
    · exact prime_4373
  · decide +kernel

theorem prime_49310819 : Nat.Prime 49310819 := by
  apply nodeValid_prime [2, 1051, 23459] ⟨49310819, 2, [(2, 1), (1051, 1), (23459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1051
    · exact prime_23459
  · decide +kernel

theorem prime_62706923 : Nat.Prime 62706923 := by
  apply nodeValid_prime [2, 107, 179, 1637] ⟨62706923, 2, [(2, 1), (107, 1), (179, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_179
    · exact prime_1637
  · decide +kernel

theorem prime_68967721 : Nat.Prime 68967721 := by
  apply nodeValid_prime [2, 3, 5, 19, 3361] ⟨68967721, 58, [(2, 3), (3, 3), (5, 1), (19, 1), (3361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_3361
  · decide +kernel

theorem prime_87749569 : Nat.Prime 87749569 := by
  apply nodeValid_prime [2, 3, 16927] ⟨87749569, 11, [(2, 6), (3, 4), (16927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16927
  · decide +kernel

theorem prime_121618747 : Nat.Prime 121618747 := by
  apply nodeValid_prime [2, 3, 101, 7433] ⟨121618747, 3, [(2, 1), (3, 4), (101, 1), (7433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_7433
  · decide +kernel

theorem prime_138079577 : Nat.Prime 138079577 := by
  apply nodeValid_prime [2, 17, 59723] ⟨138079577, 3, [(2, 3), (17, 2), (59723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59723
  · decide +kernel

theorem prime_145816477 : Nat.Prime 145816477 := by
  apply nodeValid_prime [2, 3, 13, 934721] ⟨145816477, 2, [(2, 2), (3, 1), (13, 1), (934721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_934721
  · decide +kernel

theorem prime_160681949 : Nat.Prime 160681949 := by
  apply nodeValid_prime [2, 7, 5738641] ⟨160681949, 10, [(2, 2), (7, 1), (5738641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5738641
  · decide +kernel

theorem prime_188599291 : Nat.Prime 188599291 := by
  apply nodeValid_prime [2, 3, 5, 11, 43, 13291] ⟨188599291, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (43, 1), (13291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_13291
  · decide +kernel

theorem prime_197845853 : Nat.Prime 197845853 := by
  apply nodeValid_prime [2, 569, 86927] ⟨197845853, 2, [(2, 2), (569, 1), (86927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_569
    · exact prime_86927
  · decide +kernel

theorem prime_259763447 : Nat.Prime 259763447 := by
  apply nodeValid_prime [2, 31, 4189733] ⟨259763447, 5, [(2, 1), (31, 1), (4189733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_4189733
  · decide +kernel

theorem prime_321363899 : Nat.Prime 321363899 := by
  apply nodeValid_prime [2, 160681949] ⟨321363899, 2, [(2, 1), (160681949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160681949
  · decide +kernel

theorem prime_367788017 : Nat.Prime 367788017 := by
  apply nodeValid_prime [2, 19, 73, 16573] ⟨367788017, 3, [(2, 4), (19, 1), (73, 1), (16573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
    · exact prime_16573
  · decide +kernel

theorem prime_457009799 : Nat.Prime 457009799 := by
  apply nodeValid_prime [2, 7, 32643557] ⟨457009799, 14, [(2, 1), (7, 1), (32643557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_32643557
  · decide +kernel

theorem prime_461828713 : Nat.Prime 461828713 := by
  apply nodeValid_prime [2, 3, 29, 663547] ⟨461828713, 5, [(2, 3), (3, 1), (29, 1), (663547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_663547
  · decide +kernel

theorem prime_549326269 : Nat.Prime 549326269 := by
  apply nodeValid_prime [2, 3, 313, 48751] ⟨549326269, 2, [(2, 2), (3, 2), (313, 1), (48751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
    · exact prime_48751
  · decide +kernel

theorem prime_789785153 : Nat.Prime 789785153 := by
  apply nodeValid_prime [2, 13, 949261] ⟨789785153, 3, [(2, 6), (13, 1), (949261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_949261
  · decide +kernel

theorem prime_2823295351 : Nat.Prime 2823295351 := by
  apply nodeValid_prime [2, 3, 5, 2143, 8783] ⟨2823295351, 3, [(2, 1), (3, 1), (5, 2), (2143, 1), (8783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2143
    · exact prime_8783
  · decide +kernel

theorem prime_2931705391 : Nat.Prime 2931705391 := by
  apply nodeValid_prime [2, 3, 5, 89, 1098017] ⟨2931705391, 3, [(2, 1), (3, 1), (5, 1), (89, 1), (1098017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_1098017
  · decide +kernel

theorem prime_6982234079 : Nat.Prime 6982234079 := by
  apply nodeValid_prime [2, 2437, 1432547] ⟨6982234079, 7, [(2, 1), (2437, 1), (1432547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2437
    · exact prime_1432547
  · decide +kernel

theorem prime_8195182409 : Nat.Prime 8195182409 := by
  apply nodeValid_prime [2, 7, 11597, 12619] ⟨8195182409, 3, [(2, 3), (7, 1), (11597, 1), (12619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11597
    · exact prime_12619
  · decide +kernel

theorem prime_9652225003 : Nat.Prime 9652225003 := by
  apply nodeValid_prime [2, 3, 7, 37, 41, 197, 769] ⟨9652225003, 12, [(2, 1), (3, 1), (7, 1), (37, 1), (41, 1), (197, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_41
    · exact prime_197
    · exact prime_769
  · decide +kernel

theorem prime_11340929407 : Nat.Prime 11340929407 := by
  apply nodeValid_prime [2, 3, 97, 19486133] ⟨11340929407, 5, [(2, 1), (3, 1), (97, 1), (19486133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_19486133
  · decide +kernel

theorem prime_18633559753 : Nat.Prime 18633559753 := by
  apply nodeValid_prime [2, 3, 149, 787, 2207] ⟨18633559753, 5, [(2, 3), (3, 2), (149, 1), (787, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_787
    · exact prime_2207
  · decide +kernel

theorem prime_19281833941 : Nat.Prime 19281833941 := by
  apply nodeValid_prime [2, 3, 5, 321363899] ⟨19281833941, 7, [(2, 2), (3, 1), (5, 1), (321363899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_321363899
  · decide +kernel

theorem prime_46821128177 : Nat.Prime 46821128177 := by
  apply nodeValid_prime [2, 19, 41, 197711] ⟨46821128177, 3, [(2, 4), (19, 2), (41, 1), (197711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_197711
  · decide +kernel

theorem prime_47260034203 : Nat.Prime 47260034203 := by
  apply nodeValid_prime [2, 3, 1249, 6306383] ⟨47260034203, 2, [(2, 1), (3, 1), (1249, 1), (6306383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1249
    · exact prime_6306383
  · decide +kernel

theorem prime_58389799879 : Nat.Prime 58389799879 := by
  apply nodeValid_prime [2, 3, 19, 8985811] ⟨58389799879, 3, [(2, 1), (3, 2), (19, 2), (8985811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_8985811
  · decide +kernel

theorem prime_117600587359 : Nat.Prime 117600587359 := by
  apply nodeValid_prime [2, 3, 13999, 1400107] ⟨117600587359, 3, [(2, 1), (3, 1), (13999, 1), (1400107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13999
    · exact prime_1400107
  · decide +kernel

theorem prime_139808166349 : Nat.Prime 139808166349 := by
  apply nodeValid_prime [2, 3, 677, 1697, 10141] ⟨139808166349, 7, [(2, 2), (3, 1), (677, 1), (1697, 1), (10141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
    · exact prime_1697
    · exact prime_10141
  · decide +kernel

theorem prime_174964718231 : Nat.Prime 174964718231 := by
  apply nodeValid_prime [2, 5, 313, 347, 161093] ⟨174964718231, 7, [(2, 1), (5, 1), (313, 1), (347, 1), (161093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_313
    · exact prime_347
    · exact prime_161093
  · decide +kernel

theorem prime_694146055763 : Nat.Prime 694146055763 := by
  apply nodeValid_prime [2, 23, 80221, 188107] ⟨694146055763, 2, [(2, 1), (23, 1), (80221, 1), (188107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_80221
    · exact prime_188107
  · decide +kernel

theorem prime_708075289193 : Nat.Prime 708075289193 := by
  apply nodeValid_prime [2, 59, 283, 467, 11351] ⟨708075289193, 3, [(2, 3), (59, 1), (283, 1), (467, 1), (11351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_283
    · exact prime_467
    · exact prime_11351
  · decide +kernel

theorem prime_1378548973559 : Nat.Prime 1378548973559 := by
  apply nodeValid_prime [2, 29, 163, 145816477] ⟨1378548973559, 7, [(2, 1), (29, 1), (163, 1), (145816477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_163
    · exact prime_145816477
  · decide +kernel

theorem prime_1378548973979 : Nat.Prime 1378548973979 := by
  apply nodeValid_prime [2, 11, 3491, 17949389] ⟨1378548973979, 2, [(2, 1), (11, 1), (3491, 1), (17949389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3491
    · exact prime_17949389
  · decide +kernel

theorem prime_1378548995233 : Nat.Prime 1378548995233 := by
  apply nodeValid_prime [2, 3, 229, 62706923] ⟨1378548995233, 5, [(2, 5), (3, 1), (229, 1), (62706923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_62706923
  · decide +kernel

theorem prime_1380169590809 : Nat.Prime 1380169590809 := by
  apply nodeValid_prime [2, 203807, 846493] ⟨1380169590809, 3, [(2, 3), (203807, 1), (846493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_203807
    · exact prime_846493
  · decide +kernel

theorem prime_1380169592981 : Nat.Prime 1380169592981 := by
  apply nodeValid_prime [2, 5, 151, 457009799] ⟨1380169592981, 2, [(2, 2), (5, 1), (151, 1), (457009799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_457009799
  · decide +kernel

theorem prime_1380169611539 : Nat.Prime 1380169611539 := by
  apply nodeValid_prime [2, 3659, 188599291] ⟨1380169611539, 2, [(2, 1), (3659, 1), (188599291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3659
    · exact prime_188599291
  · decide +kernel

theorem prime_1381791509003 : Nat.Prime 1381791509003 := by
  apply nodeValid_prime [2, 358109, 1929289] ⟨1381791509003, 2, [(2, 1), (358109, 1), (1929289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_358109
    · exact prime_1929289
  · decide +kernel

theorem prime_1381791509297 : Nat.Prime 1381791509297 := by
  apply nodeValid_prime [2, 11, 17, 461828713] ⟨1381791509297, 3, [(2, 4), (11, 1), (17, 1), (461828713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_461828713
  · decide +kernel

theorem prime_1381791515173 : Nat.Prime 1381791515173 := by
  apply nodeValid_prime [2, 3, 23, 829, 6039193] ⟨1381791515173, 2, [(2, 2), (3, 1), (23, 1), (829, 1), (6039193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_829
    · exact prime_6039193
  · decide +kernel

theorem prime_1383414713371 : Nat.Prime 1383414713371 := by
  apply nodeValid_prime [2, 3, 5, 263, 877, 66643] ⟨1383414713371, 2, [(2, 1), (3, 2), (5, 1), (263, 1), (877, 1), (66643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
    · exact prime_877
    · exact prime_66643
  · decide +kernel

theorem prime_1383414721379 : Nat.Prime 1383414721379 := by
  apply nodeValid_prime [2, 47, 59, 337, 740189] ⟨1383414721379, 2, [(2, 1), (47, 1), (59, 1), (337, 1), (740189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_59
    · exact prime_337
    · exact prime_740189
  · decide +kernel

theorem prime_1383414721991 : Nat.Prime 1383414721991 := by
  apply nodeValid_prime [2, 5, 7, 2823295351] ⟨1383414721991, 7, [(2, 1), (5, 1), (7, 2), (2823295351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2823295351
  · decide +kernel

theorem prime_1385039197097 : Nat.Prime 1385039197097 := by
  apply nodeValid_prime [2, 1973, 87749569] ⟨1385039197097, 3, [(2, 3), (1973, 1), (87749569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1973
    · exact prime_87749569
  · decide +kernel

theorem prime_1385039205959 : Nat.Prime 1385039205959 := by
  apply nodeValid_prime [2, 52567, 13174037] ⟨1385039205959, 13, [(2, 1), (52567, 1), (13174037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_52567
    · exact prime_13174037
  · decide +kernel

theorem prime_1385039206457 : Nat.Prime 1385039206457 := by
  apply nodeValid_prime [2, 149, 10667, 108929] ⟨1385039206457, 3, [(2, 3), (149, 1), (10667, 1), (108929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_10667
    · exact prime_108929
  · decide +kernel

theorem prime_1386664973081 : Nat.Prime 1386664973081 := by
  apply nodeValid_prime [2, 5, 28027, 1236901] ⟨1386664973081, 3, [(2, 3), (5, 1), (28027, 1), (1236901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_28027
    · exact prime_1236901
  · decide +kernel

theorem prime_1386664998293 : Nat.Prime 1386664998293 := by
  apply nodeValid_prime [2, 7, 233, 2801, 75883] ⟨1386664998293, 2, [(2, 2), (7, 1), (233, 1), (2801, 1), (75883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_233
    · exact prime_2801
    · exact prime_75883
  · decide +kernel

theorem prime_1386664998427 : Nat.Prime 1386664998427 := by
  apply nodeValid_prime [2, 3, 1117, 68967721] ⟨1386664998427, 2, [(2, 1), (3, 2), (1117, 1), (68967721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1117
    · exact prime_68967721
  · decide +kernel

theorem prime_1388292043753 : Nat.Prime 1388292043753 := by
  apply nodeValid_prime [2, 3, 19281833941] ⟨1388292043753, 5, [(2, 3), (3, 2), (19281833941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19281833941
  · decide +kernel

theorem prime_1388292110917 : Nat.Prime 1388292110917 := by
  apply nodeValid_prime [2, 3, 53, 4273, 510847] ⟨1388292110917, 2, [(2, 2), (3, 1), (53, 1), (4273, 1), (510847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_4273
    · exact prime_510847
  · decide +kernel

theorem prime_1388292111527 : Nat.Prime 1388292111527 := by
  apply nodeValid_prime [2, 694146055763] ⟨1388292111527, 5, [(2, 1), (694146055763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_694146055763
  · decide +kernel

theorem prime_1389920400433 : Nat.Prime 1389920400433 := by
  apply nodeValid_prime [2, 3, 9652225003] ⟨1389920400433, 5, [(2, 4), (3, 2), (9652225003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9652225003
  · decide +kernel

theorem prime_1389920400943 : Nat.Prime 1389920400943 := by
  apply nodeValid_prime [2, 3, 191, 1307, 927961] ⟨1389920400943, 5, [(2, 1), (3, 1), (191, 1), (1307, 1), (927961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_1307
    · exact prime_927961
  · decide +kernel

theorem prime_1389920406947 : Nat.Prime 1389920406947 := by
  apply nodeValid_prime [2, 17, 1021, 40039189] ⟨1389920406947, 2, [(2, 1), (17, 1), (1021, 1), (40039189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1021
    · exact prime_40039189
  · decide +kernel

theorem prime_1391550059099 : Nat.Prime 1391550059099 := by
  apply nodeValid_prime [2, 59, 3733, 3159067] ⟨1391550059099, 2, [(2, 1), (59, 1), (3733, 1), (3159067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_3733
    · exact prime_3159067
  · decide +kernel

theorem prime_1391550066989 : Nat.Prime 1391550066989 := by
  apply nodeValid_prime [2, 241, 1069, 1350343] ⟨1391550066989, 2, [(2, 2), (241, 1), (1069, 1), (1350343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_1069
    · exact prime_1350343
  · decide +kernel

theorem prime_1391550067937 : Nat.Prime 1391550067937 := by
  apply nodeValid_prime [2, 7, 44207, 140527] ⟨1391550067937, 3, [(2, 5), (7, 1), (44207, 1), (140527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_44207
    · exact prime_140527
  · decide +kernel

theorem prime_1393181008397 : Nat.Prime 1393181008397 := by
  apply nodeValid_prime [2, 947, 367788017] ⟨1393181008397, 2, [(2, 2), (947, 1), (367788017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_947
    · exact prime_367788017
  · decide +kernel

theorem prime_1393181009531 : Nat.Prime 1393181009531 := by
  apply nodeValid_prime [2, 5, 17, 8195182409] ⟨1393181009531, 2, [(2, 1), (5, 1), (17, 1), (8195182409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_8195182409
  · decide +kernel

theorem prime_1393181009893 : Nat.Prime 1393181009893 := by
  apply nodeValid_prime [2, 3, 7, 789785153] ⟨1393181009893, 2, [(2, 2), (3, 2), (7, 2), (789785153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_789785153
  · decide +kernel

theorem prime_1394813256731 : Nat.Prime 1394813256731 := by
  apply nodeValid_prime [2, 5, 41, 167, 20371159] ⟨1394813256731, 2, [(2, 1), (5, 1), (41, 1), (167, 1), (20371159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_167
    · exact prime_20371159
  · decide +kernel

theorem prime_1394813263369 : Nat.Prime 1394813263369 := by
  apply nodeValid_prime [2, 3, 7, 47, 1321, 133723] ⟨1394813263369, 13, [(2, 3), (3, 1), (7, 1), (47, 1), (1321, 1), (133723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_1321
    · exact prime_133723
  · decide +kernel

theorem prime_1394813263651 : Nat.Prime 1394813263651 := by
  apply nodeValid_prime [2, 3, 5, 47, 197845853] ⟨1394813263651, 12, [(2, 1), (3, 1), (5, 2), (47, 1), (197845853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_197845853
  · decide +kernel

theorem prime_1396446789781 : Nat.Prime 1396446789781 := by
  apply nodeValid_prime [2, 3, 5, 7, 157, 7059179] ⟨1396446789781, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (157, 1), (7059179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_157
    · exact prime_7059179
  · decide +kernel

theorem prime_1396446815801 : Nat.Prime 1396446815801 := by
  apply nodeValid_prime [2, 5, 6982234079] ⟨1396446815801, 6, [(2, 3), (5, 2), (6982234079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6982234079
  · decide +kernel

theorem prime_1396446819413 : Nat.Prime 1396446819413 := by
  apply nodeValid_prime [2, 263, 35363, 37537] ⟨1396446819413, 2, [(2, 2), (263, 1), (35363, 1), (37537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_35363
    · exact prime_37537
  · decide +kernel

theorem prime_1398081620587 : Nat.Prime 1398081620587 := by
  apply nodeValid_prime [2, 3, 7, 59, 113, 647, 7717] ⟨1398081620587, 2, [(2, 1), (3, 1), (7, 1), (59, 1), (113, 1), (647, 1), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_113
    · exact prime_647
    · exact prime_7717
  · decide +kernel

theorem prime_1398081663491 : Nat.Prime 1398081663491 := by
  apply nodeValid_prime [2, 5, 139808166349] ⟨1398081663491, 2, [(2, 1), (5, 1), (139808166349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139808166349
  · decide +kernel

theorem prime_1398081663821 : Nat.Prime 1398081663821 := by
  apply nodeValid_prime [2, 5, 89209, 783599] ⟨1398081663821, 2, [(2, 2), (5, 1), (89209, 1), (783599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89209
    · exact prime_783599
  · decide +kernel

theorem prime_1399717745267 : Nat.Prime 1399717745267 := by
  apply nodeValid_prime [2, 19, 54949, 670343] ⟨1399717745267, 2, [(2, 1), (19, 1), (54949, 1), (670343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_54949
    · exact prime_670343
  · decide +kernel

theorem prime_1399717745849 : Nat.Prime 1399717745849 := by
  apply nodeValid_prime [2, 174964718231] ⟨1399717745849, 3, [(2, 3), (174964718231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_174964718231
  · decide +kernel

theorem prime_1399717753397 : Nat.Prime 1399717753397 := by
  apply nodeValid_prime [2, 53, 137, 151, 319159] ⟨1399717753397, 2, [(2, 2), (53, 1), (137, 1), (151, 1), (319159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_137
    · exact prime_151
    · exact prime_319159
  · decide +kernel

theorem prime_1401355176899 : Nat.Prime 1401355176899 := by
  apply nodeValid_prime [2, 239, 2931705391] ⟨1401355176899, 2, [(2, 1), (239, 1), (2931705391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_2931705391
  · decide +kernel

theorem prime_1401355195777 : Nat.Prime 1401355195777 := by
  apply nodeValid_prime [2, 3, 263, 367, 4201] ⟨1401355195777, 5, [(2, 7), (3, 3), (263, 1), (367, 1), (4201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_367
    · exact prime_4201
  · decide +kernel

theorem prime_1401355197097 : Nat.Prime 1401355197097 := by
  apply nodeValid_prime [2, 3, 58389799879] ⟨1401355197097, 13, [(2, 3), (3, 1), (58389799879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58389799879
  · decide +kernel

theorem prime_1402993865393 : Nat.Prime 1402993865393 := by
  apply nodeValid_prime [2, 7, 103, 121618747] ⟨1402993865393, 3, [(2, 4), (7, 1), (103, 1), (121618747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_103
    · exact prime_121618747
  · decide +kernel

theorem prime_1402993867229 : Nat.Prime 1402993867229 := by
  apply nodeValid_prime [2, 353, 761, 1305679] ⟨1402993867229, 2, [(2, 2), (353, 1), (761, 1), (1305679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_761
    · exact prime_1305679
  · decide +kernel

theorem prime_1402993897541 : Nat.Prime 1402993897541 := by
  apply nodeValid_prime [2, 5, 32203, 2178359] ⟨1402993897541, 3, [(2, 2), (5, 1), (32203, 1), (2178359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_32203
    · exact prime_2178359
  · decide +kernel

theorem prime_1404633845311 : Nat.Prime 1404633845311 := by
  apply nodeValid_prime [2, 3, 5, 46821128177] ⟨1404633845311, 6, [(2, 1), (3, 1), (5, 1), (46821128177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46821128177
  · decide +kernel

theorem prime_1404633845317 : Nat.Prime 1404633845317 := by
  apply nodeValid_prime [2, 3, 13, 277, 4643, 7001] ⟨1404633845317, 2, [(2, 2), (3, 1), (13, 1), (277, 1), (4643, 1), (7001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_277
    · exact prime_4643
    · exact prime_7001
  · decide +kernel

theorem prime_1404633922777 : Nat.Prime 1404633922777 := by
  apply nodeValid_prime [2, 3, 7, 239, 33997] ⟨1404633922777, 5, [(2, 3), (3, 2), (7, 4), (239, 1), (33997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_239
    · exact prime_33997
  · decide +kernel

theorem prime_1406275246301 : Nat.Prime 1406275246301 := by
  apply nodeValid_prime [2, 5, 593, 23714591] ⟨1406275246301, 2, [(2, 2), (5, 2), (593, 1), (23714591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_593
    · exact prime_23714591
  · decide +kernel

theorem prime_1406275246469 : Nat.Prime 1406275246469 := by
  apply nodeValid_prime [2, 31, 11340929407] ⟨1406275246469, 2, [(2, 2), (31, 1), (11340929407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_11340929407
  · decide +kernel

theorem prime_1406275248641 : Nat.Prime 1406275248641 := by
  apply nodeValid_prime [2, 5, 549326269] ⟨1406275248641, 3, [(2, 9), (5, 1), (549326269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_549326269
  · decide +kernel

theorem prime_1407917876039 : Nat.Prime 1407917876039 := by
  apply nodeValid_prime [2, 149, 383, 733, 16829] ⟨1407917876039, 11, [(2, 1), (149, 1), (383, 1), (733, 1), (16829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_383
    · exact prime_733
    · exact prime_16829
  · decide +kernel

theorem prime_1407917882741 : Nat.Prime 1407917882741 := by
  apply nodeValid_prime [2, 5, 271, 259763447] ⟨1407917882741, 2, [(2, 2), (5, 1), (271, 1), (259763447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
    · exact prime_259763447
  · decide +kernel

theorem prime_1407917884421 : Nat.Prime 1407917884421 := by
  apply nodeValid_prime [2, 5, 2273, 30970477] ⟨1407917884421, 2, [(2, 2), (5, 1), (2273, 1), (30970477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2273
    · exact prime_30970477
  · decide +kernel

theorem prime_1409561806801 : Nat.Prime 1409561806801 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 907, 10883] ⟨1409561806801, 23, [(2, 4), (3, 1), (5, 2), (7, 1), (17, 1), (907, 1), (10883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_907
    · exact prime_10883
  · decide +kernel

theorem prime_1409561853151 : Nat.Prime 1409561853151 := by
  apply nodeValid_prime [2, 3, 5, 11, 277, 463, 6661] ⟨1409561853151, 11, [(2, 1), (3, 1), (5, 2), (11, 1), (277, 1), (463, 1), (6661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_277
    · exact prime_463
    · exact prime_6661
  · decide +kernel

theorem prime_1409561854907 : Nat.Prime 1409561854907 := by
  apply nodeValid_prime [2, 1487, 9623, 49253] ⟨1409561854907, 2, [(2, 1), (1487, 1), (9623, 1), (49253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1487
    · exact prime_9623
    · exact prime_49253
  · decide +kernel

theorem prime_1411207044733 : Nat.Prime 1411207044733 := by
  apply nodeValid_prime [2, 3, 4337, 9038551] ⟨1411207044733, 2, [(2, 2), (3, 2), (4337, 1), (9038551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4337
    · exact prime_9038551
  · decide +kernel

theorem prime_1411207048271 : Nat.Prime 1411207048271 := by
  apply nodeValid_prime [2, 5, 17, 59, 1013, 138893] ⟨1411207048271, 11, [(2, 1), (5, 1), (17, 1), (59, 1), (1013, 1), (138893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_59
    · exact prime_1013
    · exact prime_138893
  · decide +kernel

theorem prime_1411207048309 : Nat.Prime 1411207048309 := by
  apply nodeValid_prime [2, 3, 117600587359] ⟨1411207048309, 6, [(2, 2), (3, 1), (117600587359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_117600587359
  · decide +kernel

theorem prime_1412853547601 : Nat.Prime 1412853547601 := by
  apply nodeValid_prime [2, 5, 11, 29191189] ⟨1412853547601, 3, [(2, 4), (5, 2), (11, 2), (29191189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29191189
  · decide +kernel

theorem prime_1412853547673 : Nat.Prime 1412853547673 := by
  apply nodeValid_prime [2, 7, 17, 521, 2848541] ⟨1412853547673, 5, [(2, 3), (7, 1), (17, 1), (521, 1), (2848541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_521
    · exact prime_2848541
  · decide +kernel

theorem prime_1412853585989 : Nat.Prime 1412853585989 := by
  apply nodeValid_prime [2, 13, 19, 29, 49310819] ⟨1412853585989, 10, [(2, 2), (13, 1), (19, 1), (29, 1), (49310819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_29
    · exact prime_49310819
  · decide +kernel

theorem prime_1414501428883 : Nat.Prime 1414501428883 := by
  apply nodeValid_prime [2, 3, 27739, 8498873] ⟨1414501428883, 2, [(2, 1), (3, 1), (27739, 1), (8498873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27739
    · exact prime_8498873
  · decide +kernel

theorem prime_1414501487929 : Nat.Prime 1414501487929 := by
  apply nodeValid_prime [2, 3, 37, 71, 1493, 5009] ⟨1414501487929, 11, [(2, 3), (3, 2), (37, 1), (71, 1), (1493, 1), (5009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_1493
    · exact prime_5009
  · decide +kernel

theorem prime_1414501488493 : Nat.Prime 1414501488493 := by
  apply nodeValid_prime [2, 3, 127, 12479, 74377] ⟨1414501488493, 13, [(2, 2), (3, 1), (127, 1), (12479, 1), (74377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_12479
    · exact prime_74377
  · decide +kernel

theorem prime_1416150541081 : Nat.Prime 1416150541081 := by
  apply nodeValid_prime [2, 3, 5, 11, 67, 161743] ⟨1416150541081, 21, [(2, 3), (3, 3), (5, 1), (11, 2), (67, 1), (161743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_67
    · exact prime_161743
  · decide +kernel

theorem prime_1416150541229 : Nat.Prime 1416150541229 := by
  apply nodeValid_prime [2, 19, 18633559753] ⟨1416150541229, 2, [(2, 2), (19, 1), (18633559753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_18633559753
  · decide +kernel

theorem prime_1416150578387 : Nat.Prime 1416150578387 := by
  apply nodeValid_prime [2, 708075289193] ⟨1416150578387, 2, [(2, 1), (708075289193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_708075289193
  · decide +kernel

theorem prime_1417801026091 : Nat.Prime 1417801026091 := by
  apply nodeValid_prime [2, 3, 5, 47260034203] ⟨1417801026091, 3, [(2, 1), (3, 1), (5, 1), (47260034203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47260034203
  · decide +kernel

theorem prime_1417801096637 : Nat.Prime 1417801096637 := by
  apply nodeValid_prime [2, 17, 151, 138079577] ⟨1417801096637, 2, [(2, 2), (17, 1), (151, 1), (138079577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_151
    · exact prime_138079577
  · decide +kernel

theorem prime_1417801097387 : Nat.Prime 1417801097387 := by
  apply nodeValid_prime [2, 37, 79, 2251, 107741] ⟨1417801097387, 2, [(2, 1), (37, 1), (79, 1), (2251, 1), (107741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_79
    · exact prime_2251
    · exact prime_107741
  · decide +kernel

end Sude.Lucas.Generated
