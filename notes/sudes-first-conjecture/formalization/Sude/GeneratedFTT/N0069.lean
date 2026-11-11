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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0066

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5431 : Nat.Prime 5431 := by
  apply nodeValid_prime [2, 3, 5, 181] ⟨5431, 3, [(2, 1), (3, 1), (5, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
  · decide +kernel

theorem prime_6221 : Nat.Prime 6221 := by
  apply nodeValid_prime [2, 5, 311] ⟨6221, 3, [(2, 2), (5, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_311
  · decide +kernel

theorem prime_7883 : Nat.Prime 7883 := by
  apply nodeValid_prime [2, 7, 563] ⟨7883, 2, [(2, 1), (7, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_563
  · decide +kernel

theorem prime_9871 : Nat.Prime 9871 := by
  apply nodeValid_prime [2, 3, 5, 7, 47] ⟨9871, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_11279 : Nat.Prime 11279 := by
  apply nodeValid_prime [2, 5639] ⟨11279, 7, [(2, 1), (5639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5639
  · decide +kernel

theorem prime_12611 : Nat.Prime 12611 := by
  apply nodeValid_prime [2, 5, 13, 97] ⟨12611, 2, [(2, 1), (5, 1), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_15173 : Nat.Prime 15173 := by
  apply nodeValid_prime [2, 3793] ⟨15173, 2, [(2, 2), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3793
  · decide +kernel

theorem prime_17683 : Nat.Prime 17683 := by
  apply nodeValid_prime [2, 3, 7, 421] ⟨17683, 5, [(2, 1), (3, 1), (7, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_421
  · decide +kernel

theorem prime_22397 : Nat.Prime 22397 := by
  apply nodeValid_prime [2, 11, 509] ⟨22397, 2, [(2, 2), (11, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_509
  · decide +kernel

theorem prime_26099 : Nat.Prime 26099 := by
  apply nodeValid_prime [2, 13049] ⟨26099, 2, [(2, 1), (13049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13049
  · decide +kernel

theorem prime_26591 : Nat.Prime 26591 := by
  apply nodeValid_prime [2, 5, 2659] ⟨26591, 22, [(2, 1), (5, 1), (2659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2659
  · decide +kernel

theorem prime_27941 : Nat.Prime 27941 := by
  apply nodeValid_prime [2, 5, 11, 127] ⟨27941, 2, [(2, 2), (5, 1), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_29443 : Nat.Prime 29443 := by
  apply nodeValid_prime [2, 3, 7, 701] ⟨29443, 2, [(2, 1), (3, 1), (7, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_701
  · decide +kernel

theorem prime_31333 : Nat.Prime 31333 := by
  apply nodeValid_prime [2, 3, 7, 373] ⟨31333, 5, [(2, 2), (3, 1), (7, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_373
  · decide +kernel

theorem prime_33749 : Nat.Prime 33749 := by
  apply nodeValid_prime [2, 11, 13, 59] ⟨33749, 2, [(2, 2), (11, 1), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_34487 : Nat.Prime 34487 := by
  apply nodeValid_prime [2, 43, 401] ⟨34487, 5, [(2, 1), (43, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_401
  · decide +kernel

theorem prime_35171 : Nat.Prime 35171 := by
  apply nodeValid_prime [2, 5, 3517] ⟨35171, 2, [(2, 1), (5, 1), (3517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3517
  · decide +kernel

theorem prime_47609 : Nat.Prime 47609 := by
  apply nodeValid_prime [2, 11, 541] ⟨47609, 6, [(2, 3), (11, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_541
  · decide +kernel

theorem prime_48397 : Nat.Prime 48397 := by
  apply nodeValid_prime [2, 3, 37, 109] ⟨48397, 5, [(2, 2), (3, 1), (37, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_109
  · decide +kernel

theorem prime_52127 : Nat.Prime 52127 := by
  apply nodeValid_prime [2, 67, 389] ⟨52127, 5, [(2, 1), (67, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_389
  · decide +kernel

theorem prime_56659 : Nat.Prime 56659 := by
  apply nodeValid_prime [2, 3, 7, 19, 71] ⟨56659, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_60293 : Nat.Prime 60293 := by
  apply nodeValid_prime [2, 15073] ⟨60293, 2, [(2, 2), (15073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15073
  · decide +kernel

theorem prime_60661 : Nat.Prime 60661 := by
  apply nodeValid_prime [2, 3, 5, 337] ⟨60661, 2, [(2, 2), (3, 2), (5, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_337
  · decide +kernel

theorem prime_67499 : Nat.Prime 67499 := by
  apply nodeValid_prime [2, 33749] ⟨67499, 2, [(2, 1), (33749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33749
  · decide +kernel

theorem prime_70327 : Nat.Prime 70327 := by
  apply nodeValid_prime [2, 3, 3907] ⟨70327, 11, [(2, 1), (3, 2), (3907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3907
  · decide +kernel

theorem prime_85199 : Nat.Prime 85199 := by
  apply nodeValid_prime [2, 41, 1039] ⟨85199, 7, [(2, 1), (41, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1039
  · decide +kernel

theorem prime_85601 : Nat.Prime 85601 := by
  apply nodeValid_prime [2, 5, 107] ⟨85601, 3, [(2, 5), (5, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_88007 : Nat.Prime 88007 := by
  apply nodeValid_prime [2, 79, 557] ⟨88007, 5, [(2, 1), (79, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_557
  · decide +kernel

theorem prime_109819 : Nat.Prime 109819 := by
  apply nodeValid_prime [2, 3, 6101] ⟨109819, 3, [(2, 1), (3, 2), (6101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6101
  · decide +kernel

theorem prime_119657 : Nat.Prime 119657 := by
  apply nodeValid_prime [2, 14957] ⟨119657, 3, [(2, 3), (14957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14957
  · decide +kernel

theorem prime_120587 : Nat.Prime 120587 := by
  apply nodeValid_prime [2, 60293] ⟨120587, 2, [(2, 1), (60293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60293
  · decide +kernel

theorem prime_127817 : Nat.Prime 127817 := by
  apply nodeValid_prime [2, 13, 1229] ⟨127817, 3, [(2, 3), (13, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1229
  · decide +kernel

theorem prime_134999 : Nat.Prime 134999 := by
  apply nodeValid_prime [2, 67499] ⟨134999, 7, [(2, 1), (67499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67499
  · decide +kernel

theorem prime_135349 : Nat.Prime 135349 := by
  apply nodeValid_prime [2, 3, 11279] ⟨135349, 6, [(2, 2), (3, 1), (11279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11279
  · decide +kernel

theorem prime_171203 : Nat.Prime 171203 := by
  apply nodeValid_prime [2, 85601] ⟨171203, 2, [(2, 1), (85601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_85601
  · decide +kernel

theorem prime_180907 : Nat.Prime 180907 := by
  apply nodeValid_prime [2, 3, 11, 2741] ⟨180907, 12, [(2, 1), (3, 1), (11, 1), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2741
  · decide +kernel

theorem prime_226637 : Nat.Prime 226637 := by
  apply nodeValid_prime [2, 56659] ⟨226637, 2, [(2, 2), (56659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56659
  · decide +kernel

theorem prime_238361 : Nat.Prime 238361 := by
  apply nodeValid_prime [2, 5, 59, 101] ⟨238361, 3, [(2, 3), (5, 1), (59, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_101
  · decide +kernel

theorem prime_279919 : Nat.Prime 279919 := by
  apply nodeValid_prime [2, 3, 15551] ⟨279919, 3, [(2, 1), (3, 2), (15551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15551
  · decide +kernel

theorem prime_296243 : Nat.Prime 296243 := by
  apply nodeValid_prime [2, 17, 8713] ⟨296243, 2, [(2, 1), (17, 1), (8713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_8713
  · decide +kernel

theorem prime_298937 : Nat.Prime 298937 := by
  apply nodeValid_prime [2, 11, 43, 79] ⟨298937, 3, [(2, 3), (11, 1), (43, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_79
  · decide +kernel

theorem prime_298943 : Nat.Prime 298943 := by
  apply nodeValid_prime [2, 7, 131, 163] ⟨298943, 7, [(2, 1), (7, 1), (131, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_163
  · decide +kernel

theorem prime_313331 : Nat.Prime 313331 := by
  apply nodeValid_prime [2, 5, 31333] ⟨313331, 2, [(2, 1), (5, 1), (31333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31333
  · decide +kernel

theorem prime_379513 : Nat.Prime 379513 := by
  apply nodeValid_prime [2, 3, 7, 251] ⟨379513, 5, [(2, 3), (3, 3), (7, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_251
  · decide +kernel

theorem prime_434383 : Nat.Prime 434383 := by
  apply nodeValid_prime [2, 3, 13, 5569] ⟨434383, 6, [(2, 1), (3, 1), (13, 1), (5569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5569
  · decide +kernel

theorem prime_441547 : Nat.Prime 441547 := by
  apply nodeValid_prime [2, 3, 7, 10513] ⟨441547, 2, [(2, 1), (3, 1), (7, 1), (10513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10513
  · decide +kernel

theorem prime_569243 : Nat.Prime 569243 := by
  apply nodeValid_prime [2, 241, 1181] ⟨569243, 2, [(2, 1), (241, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_1181
  · decide +kernel

theorem prime_626663 : Nat.Prime 626663 := by
  apply nodeValid_prime [2, 313331] ⟨626663, 5, [(2, 1), (313331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_313331
  · decide +kernel

theorem prime_659177 : Nat.Prime 659177 := by
  apply nodeValid_prime [2, 7, 79, 149] ⟨659177, 3, [(2, 3), (7, 1), (79, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_149
  · decide +kernel

theorem prime_670447 : Nat.Prime 670447 := by
  apply nodeValid_prime [2, 3, 7, 17, 313] ⟨670447, 3, [(2, 1), (3, 2), (7, 1), (17, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_313
  · decide +kernel

theorem prime_671501 : Nat.Prime 671501 := by
  apply nodeValid_prime [2, 5, 17, 79] ⟨671501, 3, [(2, 2), (5, 3), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_964697 : Nat.Prime 964697 := by
  apply nodeValid_prime [2, 120587] ⟨964697, 3, [(2, 3), (120587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120587
  · decide +kernel

theorem prime_978647 : Nat.Prime 978647 := by
  apply nodeValid_prime [2, 643, 761] ⟨978647, 5, [(2, 1), (643, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_643
    · exact prime_761
  · decide +kernel

theorem prime_1430713 : Nat.Prime 1430713 := by
  apply nodeValid_prime [2, 3, 31, 641] ⟨1430713, 15, [(2, 3), (3, 2), (31, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_641
  · decide +kernel

theorem prime_1454443 : Nat.Prime 1454443 := by
  apply nodeValid_prime [2, 3, 11, 22037] ⟨1454443, 2, [(2, 1), (3, 1), (11, 1), (22037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_22037
  · decide +kernel

theorem prime_1647377 : Nat.Prime 1647377 := by
  apply nodeValid_prime [2, 19, 5419] ⟨1647377, 3, [(2, 4), (19, 1), (5419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5419
  · decide +kernel

theorem prime_1765541 : Nat.Prime 1765541 := by
  apply nodeValid_prime [2, 5, 7, 12611] ⟨1765541, 2, [(2, 2), (5, 1), (7, 1), (12611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_12611
  · decide +kernel

theorem prime_1871473 : Nat.Prime 1871473 := by
  apply nodeValid_prime [2, 3, 127, 307] ⟨1871473, 10, [(2, 4), (3, 1), (127, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_307
  · decide +kernel

theorem prime_1906439 : Nat.Prime 1906439 := by
  apply nodeValid_prime [2, 31, 97, 317] ⟨1906439, 13, [(2, 1), (31, 1), (97, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_97
    · exact prime_317
  · decide +kernel

theorem prime_2146043 : Nat.Prime 2146043 := by
  apply nodeValid_prime [2, 131, 8191] ⟨2146043, 2, [(2, 1), (131, 1), (8191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_8191
  · decide +kernel

theorem prime_2736077 : Nat.Prime 2736077 := by
  apply nodeValid_prime [2, 7, 19, 37, 139] ⟨2736077, 2, [(2, 2), (7, 1), (19, 1), (37, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_37
    · exact prime_139
  · decide +kernel

theorem prime_2789167 : Nat.Prime 2789167 := by
  apply nodeValid_prime [2, 3, 59, 7879] ⟨2789167, 3, [(2, 1), (3, 1), (59, 1), (7879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_7879
  · decide +kernel

theorem prime_3229117 : Nat.Prime 3229117 := by
  apply nodeValid_prime [2, 3, 11, 17, 1439] ⟨3229117, 2, [(2, 2), (3, 1), (11, 1), (17, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_1439
  · decide +kernel

theorem prime_3398753 : Nat.Prime 3398753 := by
  apply nodeValid_prime [2, 7, 15173] ⟨3398753, 3, [(2, 5), (7, 1), (15173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15173
  · decide +kernel

theorem prime_3555217 : Nat.Prime 3555217 := by
  apply nodeValid_prime [2, 3, 7, 3527] ⟨3555217, 5, [(2, 4), (3, 2), (7, 1), (3527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3527
  · decide +kernel

theorem prime_3799681 : Nat.Prime 3799681 := by
  apply nodeValid_prime [2, 3, 5, 1979] ⟨3799681, 13, [(2, 7), (3, 1), (5, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1979
  · decide +kernel

theorem prime_4343831 : Nat.Prime 4343831 := by
  apply nodeValid_prime [2, 5, 434383] ⟨4343831, 7, [(2, 1), (5, 1), (434383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_434383
  · decide +kernel

theorem prime_5623949 : Nat.Prime 5623949 := by
  apply nodeValid_prime [2, 11, 127817] ⟨5623949, 2, [(2, 2), (11, 1), (127817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127817
  · decide +kernel

theorem prime_6753413 : Nat.Prime 6753413 := by
  apply nodeValid_prime [2, 31, 107, 509] ⟨6753413, 2, [(2, 2), (31, 1), (107, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_107
    · exact prime_509
  · decide +kernel

theorem prime_6797507 : Nat.Prime 6797507 := by
  apply nodeValid_prime [2, 3398753] ⟨6797507, 2, [(2, 1), (3398753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3398753
  · decide +kernel

theorem prime_6860677 : Nat.Prime 6860677 := by
  apply nodeValid_prime [2, 3, 79, 7237] ⟨6860677, 2, [(2, 2), (3, 1), (79, 1), (7237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_7237
  · decide +kernel

theorem prime_7532933 : Nat.Prime 7532933 := by
  apply nodeValid_prime [2, 11, 171203] ⟨7532933, 2, [(2, 2), (11, 1), (171203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_171203
  · decide +kernel

theorem prime_8968111 : Nat.Prime 8968111 := by
  apply nodeValid_prime [2, 3, 5, 298937] ⟨8968111, 3, [(2, 1), (3, 1), (5, 1), (298937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_298937
  · decide +kernel

theorem prime_15553567 : Nat.Prime 15553567 := by
  apply nodeValid_prime [2, 3, 7, 23, 1789] ⟨15553567, 6, [(2, 1), (3, 3), (7, 1), (23, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_1789
  · decide +kernel

theorem prime_19410253 : Nat.Prime 19410253 := by
  apply nodeValid_prime [2, 3, 23, 70327] ⟨19410253, 2, [(2, 2), (3, 1), (23, 1), (70327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_70327
  · decide +kernel

theorem prime_34750649 : Nat.Prime 34750649 := by
  apply nodeValid_prime [2, 4343831] ⟨34750649, 3, [(2, 3), (4343831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4343831
  · decide +kernel

theorem prime_35903869 : Nat.Prime 35903869 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 61] ⟨35903869, 10, [(2, 2), (3, 1), (7, 3), (11, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_36389471 : Nat.Prime 36389471 := by
  apply nodeValid_prime [2, 5, 13, 279919] ⟨36389471, 29, [(2, 1), (5, 1), (13, 1), (279919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_279919
  · decide +kernel

theorem prime_37776733 : Nat.Prime 37776733 := by
  apply nodeValid_prime [2, 3, 7, 131, 3433] ⟨37776733, 14, [(2, 2), (3, 1), (7, 1), (131, 1), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_131
    · exact prime_3433
  · decide +kernel

theorem prime_64073551 : Nat.Prime 64073551 := by
  apply nodeValid_prime [2, 3, 5, 347, 1231] ⟨64073551, 3, [(2, 1), (3, 1), (5, 2), (347, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_347
    · exact prime_1231
  · decide +kernel

theorem prime_72444683 : Nat.Prime 72444683 := by
  apply nodeValid_prime [2, 19, 1906439] ⟨72444683, 2, [(2, 1), (19, 1), (1906439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1906439
  · decide +kernel

theorem prime_74070127 : Nat.Prime 74070127 := by
  apply nodeValid_prime [2, 3, 13, 35171] ⟨74070127, 6, [(2, 1), (3, 4), (13, 1), (35171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_35171
  · decide +kernel

theorem prime_75583439 : Nat.Prime 75583439 := by
  apply nodeValid_prime [2, 7, 1559, 3463] ⟨75583439, 7, [(2, 1), (7, 1), (1559, 1), (3463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1559
    · exact prime_3463
  · decide +kernel

theorem prime_104260969 : Nat.Prime 104260969 := by
  apply nodeValid_prime [2, 3, 7, 37, 5591] ⟨104260969, 11, [(2, 3), (3, 2), (7, 1), (37, 1), (5591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_5591
  · decide +kernel

theorem prime_106657777 : Nat.Prime 106657777 := by
  apply nodeValid_prime [2, 3, 149, 1657] ⟨106657777, 5, [(2, 4), (3, 3), (149, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_1657
  · decide +kernel

theorem prime_155689817 : Nat.Prime 155689817 := by
  apply nodeValid_prime [2, 2027, 9601] ⟨155689817, 3, [(2, 3), (2027, 1), (9601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2027
    · exact prime_9601
  · decide +kernel

theorem prime_163234937 : Nat.Prime 163234937 := by
  apply nodeValid_prime [2, 3109, 6563] ⟨163234937, 3, [(2, 3), (3109, 1), (6563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3109
    · exact prime_6563
  · decide +kernel

theorem prime_186627281 : Nat.Prime 186627281 := by
  apply nodeValid_prime [2, 5, 7, 47609] ⟨186627281, 3, [(2, 4), (5, 1), (7, 2), (47609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47609
  · decide +kernel

theorem prime_281758691 : Nat.Prime 281758691 := by
  apply nodeValid_prime [2, 5, 31, 101, 8999] ⟨281758691, 2, [(2, 1), (5, 1), (31, 1), (101, 1), (8999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_101
    · exact prime_8999
  · decide +kernel

theorem prime_385803961 : Nat.Prime 385803961 := by
  apply nodeValid_prime [2, 3, 5, 53, 60661] ⟨385803961, 19, [(2, 3), (3, 1), (5, 1), (53, 1), (60661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_60661
  · decide +kernel

theorem prime_417767473 : Nat.Prime 417767473 := by
  apply nodeValid_prime [2, 3, 151, 19213] ⟨417767473, 11, [(2, 4), (3, 2), (151, 1), (19213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_19213
  · decide +kernel

theorem prime_438466579 : Nat.Prime 438466579 := by
  apply nodeValid_prime [2, 3, 11, 97, 68489] ⟨438466579, 3, [(2, 1), (3, 1), (11, 1), (97, 1), (68489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_68489
  · decide +kernel

theorem prime_550703401 : Nat.Prime 550703401 := by
  apply nodeValid_prime [2, 3, 5, 13, 5431] ⟨550703401, 7, [(2, 3), (3, 1), (5, 2), (13, 2), (5431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_5431
  · decide +kernel

theorem prime_582521981 : Nat.Prime 582521981 := by
  apply nodeValid_prime [2, 5, 4831, 6029] ⟨582521981, 2, [(2, 2), (5, 1), (4831, 1), (6029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4831
    · exact prime_6029
  · decide +kernel

theorem prime_785953661 : Nat.Prime 785953661 := by
  apply nodeValid_prime [2, 5, 89, 441547] ⟨785953661, 3, [(2, 2), (5, 1), (89, 1), (441547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_441547
  · decide +kernel

theorem prime_827935363 : Nat.Prime 827935363 := by
  apply nodeValid_prime [2, 3, 47, 978647] ⟨827935363, 2, [(2, 1), (3, 2), (47, 1), (978647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_978647
  · decide +kernel

theorem prime_997521199 : Nat.Prime 997521199 := by
  apply nodeValid_prime [2, 3, 919, 180907] ⟨997521199, 15, [(2, 1), (3, 1), (919, 1), (180907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_919
    · exact prime_180907
  · decide +kernel

theorem prime_1245518537 : Nat.Prime 1245518537 := by
  apply nodeValid_prime [2, 155689817] ⟨1245518537, 3, [(2, 3), (155689817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_155689817
  · decide +kernel

theorem prime_1700940847 : Nat.Prime 1700940847 := by
  apply nodeValid_prime [2, 3, 11, 1777, 14503] ⟨1700940847, 3, [(2, 1), (3, 1), (11, 1), (1777, 1), (14503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1777
    · exact prime_14503
  · decide +kernel

theorem prime_2199014473 : Nat.Prime 2199014473 := by
  apply nodeValid_prime [2, 3, 139, 659177] ⟨2199014473, 5, [(2, 3), (3, 1), (139, 1), (659177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_659177
  · decide +kernel

theorem prime_3030391333 : Nat.Prime 3030391333 := by
  apply nodeValid_prime [2, 3, 953, 29443] ⟨3030391333, 2, [(2, 2), (3, 3), (953, 1), (29443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_953
    · exact prime_29443
  · decide +kernel

theorem prime_3114747359 : Nat.Prime 3114747359 := by
  apply nodeValid_prime [2, 227, 6860677] ⟨3114747359, 11, [(2, 1), (227, 1), (6860677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_6860677
  · decide +kernel

theorem prime_3862952237 : Nat.Prime 3862952237 := by
  apply nodeValid_prime [2, 11, 13, 6753413] ⟨3862952237, 2, [(2, 2), (11, 1), (13, 1), (6753413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_6753413
  · decide +kernel

theorem prime_4806482797 : Nat.Prime 4806482797 := by
  apply nodeValid_prime [2, 3, 5021, 26591] ⟨4806482797, 11, [(2, 2), (3, 2), (5021, 1), (26591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5021
    · exact prime_26591
  · decide +kernel

theorem prime_6323875993 : Nat.Prime 6323875993 := by
  apply nodeValid_prime [2, 3, 7, 3469, 3617] ⟨6323875993, 5, [(2, 3), (3, 2), (7, 1), (3469, 1), (3617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3469
    · exact prime_3617
  · decide +kernel

theorem prime_6749507969 : Nat.Prime 6749507969 := by
  apply nodeValid_prime [2, 7, 7532933] ⟨6749507969, 3, [(2, 7), (7, 1), (7532933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7532933
  · decide +kernel

theorem prime_8163011413 : Nat.Prime 8163011413 := by
  apply nodeValid_prime [2, 3, 75583439] ⟨8163011413, 6, [(2, 2), (3, 3), (75583439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75583439
  · decide +kernel

theorem prime_8177481401 : Nat.Prime 8177481401 := by
  apply nodeValid_prime [2, 5, 11, 1091, 3407] ⟨8177481401, 3, [(2, 3), (5, 2), (11, 1), (1091, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1091
    · exact prime_3407
  · decide +kernel

theorem prime_8573801911 : Nat.Prime 8573801911 := by
  apply nodeValid_prime [2, 3, 5, 13451, 21247] ⟨8573801911, 3, [(2, 1), (3, 1), (5, 1), (13451, 1), (21247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13451
    · exact prime_21247
  · decide +kernel

theorem prime_9646264739 : Nat.Prime 9646264739 := by
  apply nodeValid_prime [2, 11, 438466579] ⟨9646264739, 2, [(2, 1), (11, 1), (438466579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_438466579
  · decide +kernel

theorem prime_12115474823 : Nat.Prime 12115474823 := by
  apply nodeValid_prime [2, 11, 550703401] ⟨12115474823, 5, [(2, 1), (11, 1), (550703401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_550703401
  · decide +kernel

theorem prime_16214312669 : Nat.Prime 16214312669 := by
  apply nodeValid_prime [2, 23, 9769, 18041] ⟨16214312669, 2, [(2, 2), (23, 1), (9769, 1), (18041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_9769
    · exact prime_18041
  · decide +kernel

theorem prime_19695387763 : Nat.Prime 19695387763 := by
  apply nodeValid_prime [2, 3, 2897, 125899] ⟨19695387763, 2, [(2, 1), (3, 3), (2897, 1), (125899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2897
    · exact prime_125899
  · decide +kernel

theorem prime_23361519791 : Nat.Prime 23361519791 := by
  apply nodeValid_prime [2, 5, 7, 71, 671501] ⟨23361519791, 7, [(2, 1), (5, 1), (7, 2), (71, 1), (671501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_671501
  · decide +kernel

theorem prime_26424767543 : Nat.Prime 26424767543 := by
  apply nodeValid_prime [2, 193, 229, 298943] ⟨26424767543, 5, [(2, 1), (193, 1), (229, 1), (298943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_229
    · exact prime_298943
  · decide +kernel

theorem prime_52305132667 : Nat.Prime 52305132667 := by
  apply nodeValid_prime [2, 3, 103, 761, 111217] ⟨52305132667, 2, [(2, 1), (3, 1), (103, 1), (761, 1), (111217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_761
    · exact prime_111217
  · decide +kernel

theorem prime_52910257027 : Nat.Prime 52910257027 := by
  apply nodeValid_prime [2, 3, 11, 293, 2736077] ⟨52910257027, 2, [(2, 1), (3, 1), (11, 1), (293, 1), (2736077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_293
    · exact prime_2736077
  · decide +kernel

theorem prime_149856299041 : Nat.Prime 149856299041 := by
  apply nodeValid_prime [2, 3, 5, 7, 61, 157, 4657] ⟨149856299041, 17, [(2, 5), (3, 1), (5, 1), (7, 1), (61, 1), (157, 1), (4657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_157
    · exact prime_4657
  · decide +kernel

theorem prime_186892158329 : Nat.Prime 186892158329 := by
  apply nodeValid_prime [2, 23361519791] ⟨186892158329, 3, [(2, 3), (23361519791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23361519791
  · decide +kernel

theorem prime_368673482239 : Nat.Prime 368673482239 := by
  apply nodeValid_prime [2, 3, 461, 5107, 26099] ⟨368673482239, 6, [(2, 1), (3, 1), (461, 1), (5107, 1), (26099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
    · exact prime_5107
    · exact prime_26099
  · decide +kernel

theorem prime_742445876591 : Nat.Prime 742445876591 := by
  apply nodeValid_prime [2, 5, 11, 6749507969] ⟨742445876591, 11, [(2, 1), (5, 1), (11, 1), (6749507969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_6749507969
  · decide +kernel

theorem prime_1461170769601 : Nat.Prime 1461170769601 := by
  apply nodeValid_prime [2, 3, 5, 13043, 23339] ⟨1461170769601, 41, [(2, 6), (3, 1), (5, 2), (13043, 1), (23339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13043
    · exact prime_23339
  · decide +kernel

theorem prime_1461170770289 : Nat.Prime 1461170770289 := by
  apply nodeValid_prime [2, 19, 4806482797] ⟨1461170770289, 3, [(2, 4), (19, 1), (4806482797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4806482797
  · decide +kernel

theorem prime_1461170850907 : Nat.Prime 1461170850907 := by
  apply nodeValid_prime [2, 3, 13, 27941, 670447] ⟨1461170850907, 3, [(2, 1), (3, 1), (13, 1), (27941, 1), (670447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_27941
    · exact prime_670447
  · decide +kernel

theorem prime_1462856622289 : Nat.Prime 1462856622289 := by
  apply nodeValid_prime [2, 3, 5419, 5623949] ⟨1462856622289, 7, [(2, 4), (3, 1), (5419, 1), (5623949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5419
    · exact prime_5623949
  · decide +kernel

theorem prime_1462856734201 : Nat.Prime 1462856734201 := by
  apply nodeValid_prime [2, 3, 5, 67, 36389471] ⟨1462856734201, 31, [(2, 3), (3, 1), (5, 2), (67, 1), (36389471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_36389471
  · decide +kernel

theorem prime_1462856734429 : Nat.Prime 1462856734429 := by
  apply nodeValid_prime [2, 3, 127, 4027, 238361] ⟨1462856734429, 6, [(2, 2), (3, 1), (127, 1), (4027, 1), (238361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_4027
    · exact prime_238361
  · decide +kernel

theorem prime_1464543639019 : Nat.Prime 1464543639019 := by
  apply nodeValid_prime [2, 3, 37, 2199014473] ⟨1464543639019, 2, [(2, 1), (3, 2), (37, 1), (2199014473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2199014473
  · decide +kernel

theorem prime_1464543639599 : Nat.Prime 1464543639599 := by
  apply nodeValid_prime [2, 13, 39371, 1430713] ⟨1464543639599, 23, [(2, 1), (13, 1), (39371, 1), (1430713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_39371
    · exact prime_1430713
  · decide +kernel

theorem prime_1464543714677 : Nat.Prime 1464543714677 := by
  apply nodeValid_prime [2, 7, 52305132667] ⟨1464543714677, 2, [(2, 2), (7, 1), (52305132667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_52305132667
  · decide +kernel

theorem prime_1466232126283 : Nat.Prime 1466232126283 := by
  apply nodeValid_prime [2, 3, 7, 11, 421, 119657] ⟨1466232126283, 2, [(2, 1), (3, 3), (7, 2), (11, 1), (421, 1), (119657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_421
    · exact prime_119657
  · decide +kernel

theorem prime_1466232239723 : Nat.Prime 1466232239723 := by
  apply nodeValid_prime [2, 23, 9871, 3229117] ⟨1466232239723, 2, [(2, 1), (23, 1), (9871, 1), (3229117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_9871
    · exact prime_3229117
  · decide +kernel

theorem prime_1466232240329 : Nat.Prime 1466232240329 := by
  apply nodeValid_prime [2, 19, 9646264739] ⟨1466232240329, 3, [(2, 3), (19, 1), (9646264739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_9646264739
  · decide +kernel

theorem prime_1467921850061 : Nat.Prime 1467921850061 := by
  apply nodeValid_prime [2, 5, 19, 3862952237] ⟨1467921850061, 2, [(2, 2), (5, 1), (19, 1), (3862952237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3862952237
  · decide +kernel

theorem prime_1467921857069 : Nat.Prime 1467921857069 := by
  apply nodeValid_prime [2, 89, 48397, 85199] ⟨1467921857069, 2, [(2, 2), (89, 1), (48397, 1), (85199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_48397
    · exact prime_85199
  · decide +kernel

theorem prime_1467921857099 : Nat.Prime 1467921857099 := by
  apply nodeValid_prime [2, 359, 733, 2789167] ⟨1467921857099, 2, [(2, 1), (359, 1), (733, 1), (2789167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_733
    · exact prime_2789167
  · decide +kernel

theorem prime_1469612839339 : Nat.Prime 1469612839339 := by
  apply nodeValid_prime [2, 3, 7, 23, 72444683] ⟨1469612839339, 2, [(2, 1), (3, 2), (7, 2), (23, 1), (72444683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_72444683
  · decide +kernel

theorem prime_1469612840491 : Nat.Prime 1469612840491 := by
  apply nodeValid_prime [2, 3, 5, 103, 109, 1454443] ⟨1469612840491, 11, [(2, 1), (3, 2), (5, 1), (103, 1), (109, 1), (1454443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_109
    · exact prime_1454443
  · decide +kernel

theorem prime_1469612891809 : Nat.Prime 1469612891809 := by
  apply nodeValid_prime [2, 3, 1700940847] ⟨1469612891809, 7, [(2, 5), (3, 3), (1700940847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1700940847
  · decide +kernel

theorem prime_1471305223933 : Nat.Prime 1471305223933 := by
  apply nodeValid_prime [2, 3, 7883, 15553567] ⟨1471305223933, 2, [(2, 2), (3, 1), (7883, 1), (15553567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7883
    · exact prime_15553567
  · decide +kernel

theorem prime_1471305224149 : Nat.Prime 1471305224149 := by
  apply nodeValid_prime [2, 3, 34487, 3555217] ⟨1471305224149, 11, [(2, 2), (3, 1), (34487, 1), (3555217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34487
    · exact prime_3555217
  · decide +kernel

theorem prime_1471305253393 : Nat.Prime 1471305253393 := by
  apply nodeValid_prime [2, 3, 13, 785953661] ⟨1471305253393, 10, [(2, 4), (3, 2), (13, 1), (785953661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_785953661
  · decide +kernel

theorem prime_1472998941179 : Nat.Prime 1472998941179 := by
  apply nodeValid_prime [2, 19, 37, 251, 1129, 3697] ⟨1472998941179, 6, [(2, 1), (19, 1), (37, 1), (251, 1), (1129, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_251
    · exact prime_1129
    · exact prime_3697
  · decide +kernel

theorem prime_1472998968841 : Nat.Prime 1472998968841 := by
  apply nodeValid_prime [2, 3, 5, 7, 937, 1871473] ⟨1472998968841, 23, [(2, 3), (3, 1), (5, 1), (7, 1), (937, 1), (1871473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_937
    · exact prime_1871473
  · decide +kernel

theorem prime_1472998970033 : Nat.Prime 1472998970033 := by
  apply nodeValid_prime [2, 883, 104260969] ⟨1472998970033, 3, [(2, 4), (883, 1), (104260969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_883
    · exact prime_104260969
  · decide +kernel

theorem prime_1474693928693 : Nat.Prime 1474693928693 := by
  apply nodeValid_prime [2, 43, 8573801911] ⟨1474693928693, 2, [(2, 2), (43, 1), (8573801911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_8573801911
  · decide +kernel

theorem prime_1474693928957 : Nat.Prime 1474693928957 := by
  apply nodeValid_prime [2, 368673482239] ⟨1474693928957, 2, [(2, 2), (368673482239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_368673482239
  · decide +kernel

theorem prime_1474693947809 : Nat.Prime 1474693947809 := by
  apply nodeValid_prime [2, 37, 1245518537] ⟨1474693947809, 3, [(2, 5), (37, 1), (1245518537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1245518537
  · decide +kernel

theorem prime_1476390248167 : Nat.Prime 1476390248167 := by
  apply nodeValid_prime [2, 3, 79, 3114747359] ⟨1476390248167, 5, [(2, 1), (3, 1), (79, 1), (3114747359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_3114747359
  · decide +kernel

theorem prime_1476390249583 : Nat.Prime 1476390249583 := by
  apply nodeValid_prime [2, 3, 19, 31, 417767473] ⟨1476390249583, 5, [(2, 1), (3, 1), (19, 1), (31, 1), (417767473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_417767473
  · decide +kernel

theorem prime_1476390279107 : Nat.Prime 1476390279107 := by
  apply nodeValid_prime [2, 19541, 37776733] ⟨1476390279107, 2, [(2, 1), (19541, 1), (37776733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19541
    · exact prime_37776733
  · decide +kernel

theorem prime_1478087928407 : Nat.Prime 1478087928407 := by
  apply nodeValid_prime [2, 61, 12115474823] ⟨1478087928407, 5, [(2, 1), (61, 1), (12115474823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_12115474823
  · decide +kernel

theorem prime_1478088065521 : Nat.Prime 1478088065521 := by
  apply nodeValid_prime [2, 3, 5, 11, 186627281] ⟨1478088065521, 13, [(2, 4), (3, 2), (5, 1), (11, 1), (186627281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_186627281
  · decide +kernel

theorem prime_1478088067387 : Nat.Prime 1478088067387 := by
  apply nodeValid_prime [2, 3, 7, 23, 43, 2473, 14389] ⟨1478088067387, 2, [(2, 1), (3, 1), (7, 1), (23, 1), (43, 1), (2473, 1), (14389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_43
    · exact prime_2473
    · exact prime_14389
  · decide +kernel

theorem prime_1479786905717 : Nat.Prime 1479786905717 := by
  apply nodeValid_prime [2, 7, 269, 3769, 52127] ⟨1479786905717, 2, [(2, 2), (7, 1), (269, 1), (3769, 1), (52127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_269
    · exact prime_3769
    · exact prime_52127
  · decide +kernel

theorem prime_1479786982363 : Nat.Prime 1479786982363 := by
  apply nodeValid_prime [2, 3, 13, 6323875993] ⟨1479786982363, 3, [(2, 1), (3, 2), (13, 1), (6323875993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6323875993
  · decide +kernel

theorem prime_1479786982409 : Nat.Prime 1479786982409 := by
  apply nodeValid_prime [2, 7, 26424767543] ⟨1479786982409, 3, [(2, 3), (7, 1), (26424767543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_26424767543
  · decide +kernel

theorem prime_1481487196757 : Nat.Prime 1481487196757 := by
  apply nodeValid_prime [2, 7, 52910257027] ⟨1481487196757, 2, [(2, 2), (7, 1), (52910257027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_52910257027
  · decide +kernel

theorem prime_1481487197279 : Nat.Prime 1481487197279 := by
  apply nodeValid_prime [2, 11, 239, 281758691] ⟨1481487197279, 11, [(2, 1), (11, 1), (239, 1), (281758691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_281758691
  · decide +kernel

theorem prime_1481487210241 : Nat.Prime 1481487210241 := by
  apply nodeValid_prime [2, 3, 5, 385803961] ⟨1481487210241, 7, [(2, 8), (3, 1), (5, 1), (385803961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_385803961
  · decide +kernel

theorem prime_1483188828391 : Nat.Prime 1483188828391 := by
  apply nodeValid_prime [2, 3, 5, 17, 35903869] ⟨1483188828391, 6, [(2, 1), (3, 5), (5, 1), (17, 1), (35903869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_35903869
  · decide +kernel

theorem prime_1483188837373 : Nat.Prime 1483188837373 := by
  apply nodeValid_prime [2, 3, 11, 19, 29, 6797507] ⟨1483188837373, 2, [(2, 2), (3, 2), (11, 1), (19, 1), (29, 1), (6797507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_29
    · exact prime_6797507
  · decide +kernel

theorem prime_1483188837803 : Nat.Prime 1483188837803 := by
  apply nodeValid_prime [2, 7, 109819, 964697] ⟨1483188837803, 2, [(2, 1), (7, 1), (109819, 1), (964697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109819
    · exact prime_964697
  · decide +kernel

theorem prime_1484891753171 : Nat.Prime 1484891753171 := by
  apply nodeValid_prime [2, 5, 7, 3030391333] ⟨1484891753171, 2, [(2, 1), (5, 1), (7, 2), (3030391333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3030391333
  · decide +kernel

theorem prime_1484891753183 : Nat.Prime 1484891753183 := by
  apply nodeValid_prime [2, 742445876591] ⟨1484891753183, 5, [(2, 1), (742445876591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_742445876591
  · decide +kernel

theorem prime_1484891765087 : Nat.Prime 1484891765087 := by
  apply nodeValid_prime [2, 67, 17683, 626663] ⟨1484891765087, 5, [(2, 1), (67, 1), (17683, 1), (626663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_17683
    · exact prime_626663
  · decide +kernel

theorem prime_1486596028097 : Nat.Prime 1486596028097 := by
  apply nodeValid_prime [2, 73, 2357, 134999] ⟨1486596028097, 3, [(2, 6), (73, 1), (2357, 1), (134999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_2357
    · exact prime_134999
  · decide +kernel

theorem prime_1486596095513 : Nat.Prime 1486596095513 := by
  apply nodeValid_prime [2, 11, 29, 582521981] ⟨1486596095513, 3, [(2, 3), (11, 1), (29, 1), (582521981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_582521981
  · decide +kernel

theorem prime_1486596095827 : Nat.Prime 1486596095827 := by
  apply nodeValid_prime [2, 3, 23, 101, 106657777] ⟨1486596095827, 5, [(2, 1), (3, 1), (23, 1), (101, 1), (106657777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_101
    · exact prime_106657777
  · decide +kernel

theorem prime_1488301614983 : Nat.Prime 1488301614983 := by
  apply nodeValid_prime [2, 7, 13, 8177481401] ⟨1488301614983, 7, [(2, 1), (7, 1), (13, 1), (8177481401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_8177481401
  · decide +kernel

theorem prime_1488301627853 : Nat.Prime 1488301627853 := by
  apply nodeValid_prime [2, 13, 29, 43, 1765541] ⟨1488301627853, 2, [(2, 2), (13, 2), (29, 1), (43, 1), (1765541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_43
    · exact prime_1765541
  · decide +kernel

theorem prime_1488301628909 : Nat.Prime 1488301628909 := by
  apply nodeValid_prime [2, 373, 997521199] ⟨1488301628909, 2, [(2, 2), (373, 1), (997521199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_997521199
  · decide +kernel

theorem prime_1490008504937 : Nat.Prime 1490008504937 := by
  apply nodeValid_prime [2, 7, 163, 163234937] ⟨1490008504937, 3, [(2, 3), (7, 1), (163, 1), (163234937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163
    · exact prime_163234937
  · decide +kernel

theorem prime_1490008505131 : Nat.Prime 1490008505131 := by
  apply nodeValid_prime [2, 3, 5, 19, 137, 751, 941] ⟨1490008505131, 2, [(2, 1), (3, 4), (5, 1), (19, 1), (137, 1), (751, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_137
    · exact prime_751
    · exact prime_941
  · decide +kernel

theorem prime_1490008526947 : Nat.Prime 1490008526947 := by
  apply nodeValid_prime [2, 3, 67, 4651, 88547] ⟨1490008526947, 2, [(2, 1), (3, 3), (67, 1), (4651, 1), (88547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_4651
    · exact prime_88547
  · decide +kernel

theorem prime_1491716763557 : Nat.Prime 1491716763557 := by
  apply nodeValid_prime [2, 19213, 19410253] ⟨1491716763557, 2, [(2, 2), (19213, 1), (19410253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19213
    · exact prime_19410253
  · decide +kernel

theorem prime_1491716763791 : Nat.Prime 1491716763791 := by
  apply nodeValid_prime [2, 5, 11, 43, 83, 3799681] ⟨1491716763791, 7, [(2, 1), (5, 1), (11, 1), (43, 1), (83, 1), (3799681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_83
    · exact prime_3799681
  · decide +kernel

theorem prime_1491716765549 : Nat.Prime 1491716765549 := by
  apply nodeValid_prime [2, 23, 16214312669] ⟨1491716765549, 2, [(2, 2), (23, 1), (16214312669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_16214312669
  · decide +kernel

theorem prime_1493426324597 : Nat.Prime 1493426324597 := by
  apply nodeValid_prime [2, 226637, 1647377] ⟨1493426324597, 2, [(2, 2), (226637, 1), (1647377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_226637
    · exact prime_1647377
  · decide +kernel

theorem prime_1493426326709 : Nat.Prime 1493426326709 := by
  apply nodeValid_prime [2, 5827, 64073551] ⟨1493426326709, 2, [(2, 2), (5827, 1), (64073551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5827
    · exact prime_64073551
  · decide +kernel

theorem prime_1493426337829 : Nat.Prime 1493426337829 := by
  apply nodeValid_prime [2, 3, 311, 4547, 88007] ⟨1493426337829, 10, [(2, 2), (3, 1), (311, 1), (4547, 1), (88007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_4547
    · exact prime_88007
  · decide +kernel

theorem prime_1495137232249 : Nat.Prime 1495137232249 := by
  apply nodeValid_prime [2, 3, 11, 9949, 569243] ⟨1495137232249, 7, [(2, 3), (3, 1), (11, 1), (9949, 1), (569243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9949
    · exact prime_569243
  · decide +kernel

theorem prime_1495137266633 : Nat.Prime 1495137266633 := by
  apply nodeValid_prime [2, 186892158329] ⟨1495137266633, 3, [(2, 3), (186892158329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_186892158329
  · decide +kernel

theorem prime_1495137267581 : Nat.Prime 1495137267581 := by
  apply nodeValid_prime [2, 5, 11, 37, 59, 139, 22397] ⟨1495137267581, 2, [(2, 2), (5, 1), (11, 1), (37, 1), (59, 1), (139, 1), (22397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_59
    · exact prime_139
    · exact prime_22397
  · decide +kernel

theorem prime_1496849455027 : Nat.Prime 1496849455027 := by
  apply nodeValid_prime [2, 3, 2393, 34750649] ⟨1496849455027, 2, [(2, 1), (3, 2), (2393, 1), (34750649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2393
    · exact prime_34750649
  · decide +kernel

theorem prime_1496849469989 : Nat.Prime 1496849469989 := by
  apply nodeValid_prime [2, 19, 19695387763] ⟨1496849469989, 2, [(2, 2), (19, 1), (19695387763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_19695387763
  · decide +kernel

theorem prime_1496849470789 : Nat.Prime 1496849470789 := by
  apply nodeValid_prime [2, 3, 7, 1987, 8968111] ⟨1496849470789, 6, [(2, 2), (3, 1), (7, 1), (1987, 1), (8968111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1987
    · exact prime_8968111
  · decide +kernel

theorem prime_1498562990081 : Nat.Prime 1498562990081 := by
  apply nodeValid_prime [2, 5, 13, 19, 296243] ⟨1498562990081, 7, [(2, 12), (5, 1), (13, 1), (19, 1), (296243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_296243
  · decide +kernel

theorem prime_1498562990411 : Nat.Prime 1498562990411 := by
  apply nodeValid_prime [2, 5, 149856299041] ⟨1498562990411, 2, [(2, 1), (5, 1), (149856299041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149856299041
  · decide +kernel

theorem prime_1498563007031 : Nat.Prime 1498563007031 := by
  apply nodeValid_prime [2, 5, 181, 827935363] ⟨1498563007031, 23, [(2, 1), (5, 1), (181, 1), (827935363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_181
    · exact prime_827935363
  · decide +kernel

theorem prime_1500277884661 : Nat.Prime 1500277884661 := by
  apply nodeValid_prime [2, 3, 5, 197, 2267, 6221] ⟨1500277884661, 6, [(2, 2), (3, 3), (5, 1), (197, 1), (2267, 1), (6221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
    · exact prime_2267
    · exact prime_6221
  · decide +kernel

theorem prime_1500277885387 : Nat.Prime 1500277885387 := by
  apply nodeValid_prime [2, 3, 7, 41, 157, 135349] ⟨1500277885387, 2, [(2, 1), (3, 1), (7, 1), (41, 2), (157, 1), (135349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_157
    · exact prime_135349
  · decide +kernel

theorem prime_1500277888159 : Nat.Prime 1500277888159 := by
  apply nodeValid_prime [2, 3, 7, 61, 1543, 379513] ⟨1500277888159, 7, [(2, 1), (3, 1), (7, 1), (61, 1), (1543, 1), (379513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_1543
    · exact prime_379513
  · decide +kernel

theorem prime_1501994035271 : Nat.Prime 1501994035271 := by
  apply nodeValid_prime [2, 5, 17, 23, 179, 2146043] ⟨1501994035271, 7, [(2, 1), (5, 1), (17, 1), (23, 1), (179, 1), (2146043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_179
    · exact prime_2146043
  · decide +kernel

theorem prime_1501994035307 : Nat.Prime 1501994035307 := by
  apply nodeValid_prime [2, 10139, 74070127] ⟨1501994035307, 2, [(2, 1), (10139, 1), (74070127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10139
    · exact prime_74070127
  · decide +kernel

theorem prime_1501994099993 : Nat.Prime 1501994099993 := by
  apply nodeValid_prime [2, 23, 8163011413] ⟨1501994099993, 3, [(2, 3), (23, 1), (8163011413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_8163011413
  · decide +kernel

end Sude.Lucas.Generated
