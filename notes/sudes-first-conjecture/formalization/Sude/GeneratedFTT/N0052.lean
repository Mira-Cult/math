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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2903 : Nat.Prime 2903 := by
  apply nodeValid_prime [2, 1451] ⟨2903, 5, [(2, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1451
  · decide +kernel

theorem prime_5081 : Nat.Prime 5081 := by
  apply nodeValid_prime [2, 5, 127] ⟨5081, 3, [(2, 3), (5, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_5297 : Nat.Prime 5297 := by
  apply nodeValid_prime [2, 331] ⟨5297, 3, [(2, 4), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_331
  · decide +kernel

theorem prime_8179 : Nat.Prime 8179 := by
  apply nodeValid_prime [2, 3, 29, 47] ⟨8179, 2, [(2, 1), (3, 1), (29, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_47
  · decide +kernel

theorem prime_9649 : Nat.Prime 9649 := by
  apply nodeValid_prime [2, 3, 67] ⟨9649, 7, [(2, 4), (3, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
  · decide +kernel

theorem prime_9743 : Nat.Prime 9743 := by
  apply nodeValid_prime [2, 4871] ⟨9743, 5, [(2, 1), (4871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4871
  · decide +kernel

theorem prime_10009 : Nat.Prime 10009 := by
  apply nodeValid_prime [2, 3, 139] ⟨10009, 11, [(2, 3), (3, 2), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_10163 : Nat.Prime 10163 := by
  apply nodeValid_prime [2, 5081] ⟨10163, 2, [(2, 1), (5081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5081
  · decide +kernel

theorem prime_11743 : Nat.Prime 11743 := by
  apply nodeValid_prime [2, 3, 19, 103] ⟨11743, 3, [(2, 1), (3, 1), (19, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_103
  · decide +kernel

theorem prime_12239 : Nat.Prime 12239 := by
  apply nodeValid_prime [2, 29, 211] ⟨12239, 13, [(2, 1), (29, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_211
  · decide +kernel

theorem prime_16759 : Nat.Prime 16759 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨16759, 3, [(2, 1), (3, 2), (7, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_18127 : Nat.Prime 18127 := by
  apply nodeValid_prime [2, 3, 19, 53] ⟨18127, 3, [(2, 1), (3, 2), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_18191 : Nat.Prime 18191 := by
  apply nodeValid_prime [2, 5, 17, 107] ⟨18191, 29, [(2, 1), (5, 1), (17, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_107
  · decide +kernel

theorem prime_19471 : Nat.Prime 19471 := by
  apply nodeValid_prime [2, 3, 5, 11, 59] ⟨19471, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_24137 : Nat.Prime 24137 := by
  apply nodeValid_prime [2, 7, 431] ⟨24137, 3, [(2, 3), (7, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_431
  · decide +kernel

theorem prime_29137 : Nat.Prime 29137 := by
  apply nodeValid_prime [2, 3, 607] ⟨29137, 5, [(2, 4), (3, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_607
  · decide +kernel

theorem prime_30169 : Nat.Prime 30169 := by
  apply nodeValid_prime [2, 3, 419] ⟨30169, 7, [(2, 3), (3, 2), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419
  · decide +kernel

theorem prime_32717 : Nat.Prime 32717 := by
  apply nodeValid_prime [2, 8179] ⟨32717, 2, [(2, 2), (8179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8179
  · decide +kernel

theorem prime_32803 : Nat.Prime 32803 := by
  apply nodeValid_prime [2, 3, 7, 11, 71] ⟨32803, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_35281 : Nat.Prime 35281 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨35281, 23, [(2, 4), (3, 2), (5, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_35317 : Nat.Prime 35317 := by
  apply nodeValid_prime [2, 3, 109] ⟨35317, 5, [(2, 2), (3, 4), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_37223 : Nat.Prime 37223 := by
  apply nodeValid_prime [2, 37, 503] ⟨37223, 5, [(2, 1), (37, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_503
  · decide +kernel

theorem prime_38729 : Nat.Prime 38729 := by
  apply nodeValid_prime [2, 47, 103] ⟨38729, 3, [(2, 3), (47, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_103
  · decide +kernel

theorem prime_38749 : Nat.Prime 38749 := by
  apply nodeValid_prime [2, 3, 3229] ⟨38749, 2, [(2, 2), (3, 1), (3229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3229
  · decide +kernel

theorem prime_40123 : Nat.Prime 40123 := by
  apply nodeValid_prime [2, 3, 743] ⟨40123, 2, [(2, 1), (3, 3), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_743
  · decide +kernel

theorem prime_47119 : Nat.Prime 47119 := by
  apply nodeValid_prime [2, 3, 7853] ⟨47119, 3, [(2, 1), (3, 1), (7853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7853
  · decide +kernel

theorem prime_50359 : Nat.Prime 50359 := by
  apply nodeValid_prime [2, 3, 7, 11, 109] ⟨50359, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_53113 : Nat.Prime 53113 := by
  apply nodeValid_prime [2, 3, 2213] ⟨53113, 5, [(2, 3), (3, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2213
  · decide +kernel

theorem prime_57667 : Nat.Prime 57667 := by
  apply nodeValid_prime [2, 3, 7, 1373] ⟨57667, 3, [(2, 1), (3, 1), (7, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1373
  · decide +kernel

theorem prime_57847 : Nat.Prime 57847 := by
  apply nodeValid_prime [2, 3, 31, 311] ⟨57847, 3, [(2, 1), (3, 1), (31, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_311
  · decide +kernel

theorem prime_70717 : Nat.Prime 70717 := by
  apply nodeValid_prime [2, 3, 71, 83] ⟨70717, 2, [(2, 2), (3, 1), (71, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_83
  · decide +kernel

theorem prime_73039 : Nat.Prime 73039 := by
  apply nodeValid_prime [2, 3, 7, 37, 47] ⟨73039, 3, [(2, 1), (3, 1), (7, 1), (37, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_47
  · decide +kernel

theorem prime_78823 : Nat.Prime 78823 := by
  apply nodeValid_prime [2, 3, 29, 151] ⟨78823, 3, [(2, 1), (3, 2), (29, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_151
  · decide +kernel

theorem prime_82039 : Nat.Prime 82039 := by
  apply nodeValid_prime [2, 3, 11, 113] ⟨82039, 15, [(2, 1), (3, 1), (11, 2), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
  · decide +kernel

theorem prime_116827 : Nat.Prime 116827 := by
  apply nodeValid_prime [2, 3, 19471] ⟨116827, 2, [(2, 1), (3, 1), (19471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19471
  · decide +kernel

theorem prime_117503 : Nat.Prime 117503 := by
  apply nodeValid_prime [2, 7, 11, 109] ⟨117503, 5, [(2, 1), (7, 2), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_122279 : Nat.Prime 122279 := by
  apply nodeValid_prime [2, 13, 4703] ⟨122279, 11, [(2, 1), (13, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4703
  · decide +kernel

theorem prime_141269 : Nat.Prime 141269 := by
  apply nodeValid_prime [2, 35317] ⟨141269, 2, [(2, 2), (35317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35317
  · decide +kernel

theorem prime_143743 : Nat.Prime 143743 := by
  apply nodeValid_prime [2, 3, 23957] ⟨143743, 3, [(2, 1), (3, 1), (23957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23957
  · decide +kernel

theorem prime_189997 : Nat.Prime 189997 := by
  apply nodeValid_prime [2, 3, 71, 223] ⟨189997, 5, [(2, 2), (3, 1), (71, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_223
  · decide +kernel

theorem prime_223339 : Nat.Prime 223339 := by
  apply nodeValid_prime [2, 3, 37223] ⟨223339, 2, [(2, 1), (3, 1), (37223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37223
  · decide +kernel

theorem prime_225157 : Nat.Prime 225157 := by
  apply nodeValid_prime [2, 3, 29, 647] ⟨225157, 2, [(2, 2), (3, 1), (29, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_647
  · decide +kernel

theorem prime_235007 : Nat.Prime 235007 := by
  apply nodeValid_prime [2, 117503] ⟨235007, 5, [(2, 1), (117503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117503
  · decide +kernel

theorem prime_248749 : Nat.Prime 248749 := by
  apply nodeValid_prime [2, 3, 19, 1091] ⟨248749, 2, [(2, 2), (3, 1), (19, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1091
  · decide +kernel

theorem prime_248797 : Nat.Prime 248797 := by
  apply nodeValid_prime [2, 3, 6911] ⟨248797, 2, [(2, 2), (3, 2), (6911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6911
  · decide +kernel

theorem prime_258539 : Nat.Prime 258539 := by
  apply nodeValid_prime [2, 7, 59, 313] ⟨258539, 2, [(2, 1), (7, 1), (59, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_313
  · decide +kernel

theorem prime_282869 : Nat.Prime 282869 := by
  apply nodeValid_prime [2, 70717] ⟨282869, 2, [(2, 2), (70717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_70717
  · decide +kernel

theorem prime_306853 : Nat.Prime 306853 := by
  apply nodeValid_prime [2, 3, 7, 13, 281] ⟨306853, 5, [(2, 2), (3, 1), (7, 1), (13, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_281
  · decide +kernel

theorem prime_419141 : Nat.Prime 419141 := by
  apply nodeValid_prime [2, 5, 19, 1103] ⟨419141, 2, [(2, 2), (5, 1), (19, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1103
  · decide +kernel

theorem prime_424997 : Nat.Prime 424997 := by
  apply nodeValid_prime [2, 11, 13, 743] ⟨424997, 2, [(2, 2), (11, 1), (13, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_743
  · decide +kernel

theorem prime_438847 : Nat.Prime 438847 := by
  apply nodeValid_prime [2, 3, 73141] ⟨438847, 3, [(2, 1), (3, 1), (73141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73141
  · decide +kernel

theorem prime_450403 : Nat.Prime 450403 := by
  apply nodeValid_prime [2, 3, 271, 277] ⟨450403, 3, [(2, 1), (3, 1), (271, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_277
  · decide +kernel

theorem prime_452633 : Nat.Prime 452633 := by
  apply nodeValid_prime [2, 29, 1951] ⟨452633, 3, [(2, 3), (29, 1), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1951
  · decide +kernel

theorem prime_515477 : Nat.Prime 515477 := by
  apply nodeValid_prime [2, 13, 23, 431] ⟨515477, 2, [(2, 2), (13, 1), (23, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_431
  · decide +kernel

theorem prime_517079 : Nat.Prime 517079 := by
  apply nodeValid_prime [2, 258539] ⟨517079, 17, [(2, 1), (258539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_258539
  · decide +kernel

theorem prime_700963 : Nat.Prime 700963 := by
  apply nodeValid_prime [2, 3, 116827] ⟨700963, 2, [(2, 1), (3, 1), (116827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_116827
  · decide +kernel

theorem prime_704581 : Nat.Prime 704581 := by
  apply nodeValid_prime [2, 3, 5, 11743] ⟨704581, 2, [(2, 2), (3, 1), (5, 1), (11743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11743
  · decide +kernel

theorem prime_725399 : Nat.Prime 725399 := by
  apply nodeValid_prime [2, 47, 7717] ⟨725399, 11, [(2, 1), (47, 1), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_7717
  · decide +kernel

theorem prime_752903 : Nat.Prime 752903 := by
  apply nodeValid_prime [2, 487, 773] ⟨752903, 5, [(2, 1), (487, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_773
  · decide +kernel

theorem prime_788231 : Nat.Prime 788231 := by
  apply nodeValid_prime [2, 5, 78823] ⟨788231, 13, [(2, 1), (5, 1), (78823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_78823
  · decide +kernel

theorem prime_800977 : Nat.Prime 800977 := by
  apply nodeValid_prime [2, 3, 11, 37, 41] ⟨800977, 5, [(2, 4), (3, 1), (11, 1), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_1036369 : Nat.Prime 1036369 := by
  apply nodeValid_prime [2, 3, 2399] ⟨1036369, 14, [(2, 4), (3, 3), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2399
  · decide +kernel

theorem prime_1176293 : Nat.Prime 1176293 := by
  apply nodeValid_prime [2, 13, 22621] ⟨1176293, 2, [(2, 2), (13, 1), (22621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_22621
  · decide +kernel

theorem prime_1346119 : Nat.Prime 1346119 := by
  apply nodeValid_prime [2, 3, 157, 1429] ⟨1346119, 3, [(2, 1), (3, 1), (157, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_1429
  · decide +kernel

theorem prime_1492783 : Nat.Prime 1492783 := by
  apply nodeValid_prime [2, 3, 248797] ⟨1492783, 5, [(2, 1), (3, 1), (248797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_248797
  · decide +kernel

theorem prime_1560781 : Nat.Prime 1560781 := by
  apply nodeValid_prime [2, 3, 5, 13, 23, 29] ⟨1560781, 10, [(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_1744433 : Nat.Prime 1744433 := by
  apply nodeValid_prime [2, 31, 3517] ⟨1744433, 3, [(2, 4), (31, 1), (3517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3517
  · decide +kernel

theorem prime_1847117 : Nat.Prime 1847117 := by
  apply nodeValid_prime [2, 163, 2833] ⟨1847117, 2, [(2, 2), (163, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_2833
  · decide +kernel

theorem prime_1896871 : Nat.Prime 1896871 := by
  apply nodeValid_prime [2, 3, 5, 53, 1193] ⟨1896871, 3, [(2, 1), (3, 1), (5, 1), (53, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_1193
  · decide +kernel

theorem prime_3618029 : Nat.Prime 3618029 := by
  apply nodeValid_prime [2, 89, 10163] ⟨3618029, 2, [(2, 2), (89, 1), (10163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_10163
  · decide +kernel

theorem prime_4517419 : Nat.Prime 4517419 := by
  apply nodeValid_prime [2, 3, 752903] ⟨4517419, 2, [(2, 1), (3, 1), (752903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_752903
  · decide +kernel

theorem prime_4753901 : Nat.Prime 4753901 := by
  apply nodeValid_prime [2, 5, 137, 347] ⟨4753901, 7, [(2, 2), (5, 2), (137, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_347
  · decide +kernel

theorem prime_5000539 : Nat.Prime 5000539 := by
  apply nodeValid_prime [2, 3, 107, 7789] ⟨5000539, 3, [(2, 1), (3, 1), (107, 1), (7789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_7789
  · decide +kernel

theorem prime_7409011 : Nat.Prime 7409011 := by
  apply nodeValid_prime [2, 3, 5, 7, 35281] ⟨7409011, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (35281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_35281
  · decide +kernel

theorem prime_8566279 : Nat.Prime 8566279 := by
  apply nodeValid_prime [2, 3, 7, 29137] ⟨8566279, 6, [(2, 1), (3, 1), (7, 2), (29137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29137
  · decide +kernel

theorem prime_10851349 : Nat.Prime 10851349 := by
  apply nodeValid_prime [2, 3, 907, 997] ⟨10851349, 2, [(2, 2), (3, 1), (907, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
    · exact prime_997
  · decide +kernel

theorem prime_12446237 : Nat.Prime 12446237 := by
  apply nodeValid_prime [2, 11, 282869] ⟨12446237, 2, [(2, 2), (11, 1), (282869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_282869
  · decide +kernel

theorem prime_12887827 : Nat.Prime 12887827 := by
  apply nodeValid_prime [2, 3, 7, 306853] ⟨12887827, 2, [(2, 1), (3, 1), (7, 1), (306853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_306853
  · decide +kernel

theorem prime_15313703 : Nat.Prime 15313703 := by
  apply nodeValid_prime [2, 17, 450403] ⟨15313703, 5, [(2, 1), (17, 1), (450403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_450403
  · decide +kernel

theorem prime_20691967 : Nat.Prime 20691967 := by
  apply nodeValid_prime [2, 3, 89, 38749] ⟨20691967, 5, [(2, 1), (3, 1), (89, 1), (38749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_38749
  · decide +kernel

theorem prime_23884529 : Nat.Prime 23884529 := by
  apply nodeValid_prime [2, 1492783] ⟨23884529, 3, [(2, 4), (1492783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1492783
  · decide +kernel

theorem prime_25717721 : Nat.Prime 25717721 := by
  apply nodeValid_prime [2, 5, 7, 53, 1733] ⟨25717721, 3, [(2, 3), (5, 1), (7, 1), (53, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_1733
  · decide +kernel

theorem prime_25745207 : Nat.Prime 25745207 := by
  apply nodeValid_prime [2, 373, 34511] ⟨25745207, 5, [(2, 1), (373, 1), (34511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_34511
  · decide +kernel

theorem prime_30863851 : Nat.Prime 30863851 := by
  apply nodeValid_prime [2, 3, 5, 205759] ⟨30863851, 3, [(2, 1), (3, 1), (5, 2), (205759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_205759
  · decide +kernel

theorem prime_33270371 : Nat.Prime 33270371 := by
  apply nodeValid_prime [2, 5, 7, 461, 1031] ⟨33270371, 2, [(2, 1), (5, 1), (7, 1), (461, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_461
    · exact prime_1031
  · decide +kernel

theorem prime_41039353 : Nat.Prime 41039353 := by
  apply nodeValid_prime [2, 3, 189997] ⟨41039353, 5, [(2, 3), (3, 3), (189997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_189997
  · decide +kernel

theorem prime_53873947 : Nat.Prime 53873947 := by
  apply nodeValid_prime [2, 3, 7, 239, 1789] ⟨53873947, 3, [(2, 1), (3, 2), (7, 1), (239, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_239
    · exact prime_1789
  · decide +kernel

theorem prime_63072181 : Nat.Prime 63072181 := by
  apply nodeValid_prime [2, 3, 5, 59, 5939] ⟨63072181, 2, [(2, 2), (3, 2), (5, 1), (59, 1), (5939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_5939
  · decide +kernel

theorem prime_78527353 : Nat.Prime 78527353 := by
  apply nodeValid_prime [2, 3, 17, 197, 977] ⟨78527353, 5, [(2, 3), (3, 1), (17, 1), (197, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_197
    · exact prime_977
  · decide +kernel

theorem prime_87298499 : Nat.Prime 87298499 := by
  apply nodeValid_prime [2, 7, 89, 10009] ⟨87298499, 2, [(2, 1), (7, 2), (89, 1), (10009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_10009
  · decide +kernel

theorem prime_101955257 : Nat.Prime 101955257 := by
  apply nodeValid_prime [2, 13, 17, 57667] ⟨101955257, 5, [(2, 3), (13, 1), (17, 1), (57667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_57667
  · decide +kernel

theorem prime_112898713 : Nat.Prime 112898713 := by
  apply nodeValid_prime [2, 3, 103, 109, 419] ⟨112898713, 5, [(2, 3), (3, 1), (103, 1), (109, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_109
    · exact prime_419
  · decide +kernel

theorem prime_120198763 : Nat.Prime 120198763 := by
  apply nodeValid_prime [2, 3, 197, 11299] ⟨120198763, 2, [(2, 1), (3, 3), (197, 1), (11299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_11299
  · decide +kernel

theorem prime_138100801 : Nat.Prime 138100801 := by
  apply nodeValid_prime [2, 3, 5, 28771] ⟨138100801, 13, [(2, 6), (3, 1), (5, 2), (28771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28771
  · decide +kernel

theorem prime_149636693 : Nat.Prime 149636693 := by
  apply nodeValid_prime [2, 3877, 9649] ⟨149636693, 2, [(2, 2), (3877, 1), (9649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3877
    · exact prime_9649
  · decide +kernel

theorem prime_231980887 : Nat.Prime 231980887 := by
  apply nodeValid_prime [2, 3, 12887827] ⟨231980887, 3, [(2, 1), (3, 2), (12887827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12887827
  · decide +kernel

theorem prime_239855813 : Nat.Prime 239855813 := by
  apply nodeValid_prime [2, 7, 8566279] ⟨239855813, 2, [(2, 2), (7, 1), (8566279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8566279
  · decide +kernel

theorem prime_247006691 : Nat.Prime 247006691 := by
  apply nodeValid_prime [2, 5, 7, 61, 57847] ⟨247006691, 2, [(2, 1), (5, 1), (7, 1), (61, 1), (57847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_57847
  · decide +kernel

theorem prime_263769137 : Nat.Prime 263769137 := by
  apply nodeValid_prime [2, 683, 24137] ⟨263769137, 3, [(2, 4), (683, 1), (24137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_683
    · exact prime_24137
  · decide +kernel

theorem prime_494013383 : Nat.Prime 494013383 := by
  apply nodeValid_prime [2, 247006691] ⟨494013383, 5, [(2, 1), (247006691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_247006691
  · decide +kernel

theorem prime_505012271 : Nat.Prime 505012271 := by
  apply nodeValid_prime [2, 5, 7, 59, 122279] ⟨505012271, 7, [(2, 1), (5, 1), (7, 1), (59, 1), (122279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_122279
  · decide +kernel

theorem prime_877158923 : Nat.Prime 877158923 := by
  apply nodeValid_prime [2, 281, 1560781] ⟨877158923, 2, [(2, 1), (281, 1), (1560781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_1560781
  · decide +kernel

theorem prime_1237241479 : Nat.Prime 1237241479 := by
  apply nodeValid_prime [2, 3, 11, 3539, 5297] ⟨1237241479, 6, [(2, 1), (3, 1), (11, 1), (3539, 1), (5297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3539
    · exact prime_5297
  · decide +kernel

theorem prime_1429021361 : Nat.Prime 1429021361 := by
  apply nodeValid_prime [2, 5, 13, 17, 131, 617] ⟨1429021361, 3, [(2, 4), (5, 1), (13, 1), (17, 1), (131, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_131
    · exact prime_617
  · decide +kernel

theorem prime_1603955077 : Nat.Prime 1603955077 := by
  apply nodeValid_prime [2, 3, 67, 1373, 1453] ⟨1603955077, 2, [(2, 2), (3, 1), (67, 1), (1373, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1373
    · exact prime_1453
  · decide +kernel

theorem prime_1659063137 : Nat.Prime 1659063137 := by
  apply nodeValid_prime [2, 367, 141269] ⟨1659063137, 3, [(2, 5), (367, 1), (141269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_141269
  · decide +kernel

theorem prime_2010825329 : Nat.Prime 2010825329 := by
  apply nodeValid_prime [2, 19, 103, 149, 431] ⟨2010825329, 3, [(2, 4), (19, 1), (103, 1), (149, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_103
    · exact prime_149
    · exact prime_431
  · decide +kernel

theorem prime_2741121629 : Nat.Prime 2741121629 := by
  apply nodeValid_prime [2, 7, 53, 1847117] ⟨2741121629, 2, [(2, 2), (7, 1), (53, 1), (1847117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_1847117
  · decide +kernel

theorem prime_3541507259 : Nat.Prime 3541507259 := by
  apply nodeValid_prime [2, 239, 7409011] ⟨3541507259, 2, [(2, 1), (239, 1), (7409011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_7409011
  · decide +kernel

theorem prime_4040098169 : Nat.Prime 4040098169 := by
  apply nodeValid_prime [2, 505012271] ⟨4040098169, 3, [(2, 3), (505012271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_505012271
  · decide +kernel

theorem prime_5676496291 : Nat.Prime 5676496291 := by
  apply nodeValid_prime [2, 3, 5, 63072181] ⟨5676496291, 2, [(2, 1), (3, 2), (5, 1), (63072181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_63072181
  · decide +kernel

theorem prime_6116260373 : Nat.Prime 6116260373 := by
  apply nodeValid_prime [2, 23, 83, 800977] ⟨6116260373, 2, [(2, 2), (23, 1), (83, 1), (800977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_83
    · exact prime_800977
  · decide +kernel

theorem prime_6628838449 : Nat.Prime 6628838449 := by
  apply nodeValid_prime [2, 3, 138100801] ⟨6628838449, 11, [(2, 4), (3, 1), (138100801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_138100801
  · decide +kernel

theorem prime_11215078271 : Nat.Prime 11215078271 := by
  apply nodeValid_prime [2, 5, 11, 101955257] ⟨11215078271, 11, [(2, 1), (5, 1), (11, 1), (101955257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_101955257
  · decide +kernel

theorem prime_13200153623 : Nat.Prime 13200153623 := by
  apply nodeValid_prime [2, 223, 1627, 18191] ⟨13200153623, 5, [(2, 1), (223, 1), (1627, 1), (18191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_1627
    · exact prime_18191
  · decide +kernel

theorem prime_17543178461 : Nat.Prime 17543178461 := by
  apply nodeValid_prime [2, 5, 877158923] ⟨17543178461, 2, [(2, 2), (5, 1), (877158923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_877158923
  · decide +kernel

theorem prime_18100796947 : Nat.Prime 18100796947 := by
  apply nodeValid_prime [2, 3, 197, 15313703] ⟨18100796947, 3, [(2, 1), (3, 1), (197, 1), (15313703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_15313703
  · decide +kernel

theorem prime_18274144321 : Nat.Prime 18274144321 := by
  apply nodeValid_prime [2, 3, 5, 235007] ⟨18274144321, 19, [(2, 6), (3, 5), (5, 1), (235007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_235007
  · decide +kernel

theorem prime_22048444153 : Nat.Prime 22048444153 := by
  apply nodeValid_prime [2, 3, 7, 37, 67, 2521] ⟨22048444153, 11, [(2, 3), (3, 2), (7, 2), (37, 1), (67, 1), (2521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_67
    · exact prime_2521
  · decide +kernel

theorem prime_87002363209 : Nat.Prime 87002363209 := by
  apply nodeValid_prime [2, 3, 2693, 1346119] ⟨87002363209, 13, [(2, 3), (3, 1), (2693, 1), (1346119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2693
    · exact prime_1346119
  · decide +kernel

theorem prime_217505907889 : Nat.Prime 217505907889 := by
  apply nodeValid_prime [2, 3, 127, 193, 199, 929] ⟨217505907889, 11, [(2, 4), (3, 1), (127, 1), (193, 1), (199, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_193
    · exact prime_199
    · exact prime_929
  · decide +kernel

theorem prime_437983483571 : Nat.Prime 437983483571 := by
  apply nodeValid_prime [2, 5, 31, 9829, 143743] ⟨437983483571, 2, [(2, 1), (5, 1), (31, 1), (9829, 1), (143743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_9829
    · exact prime_143743
  · decide +kernel

theorem prime_857044732681 : Nat.Prime 857044732681 := by
  apply nodeValid_prime [2, 3, 5, 17, 31, 4517419] ⟨857044732681, 26, [(2, 3), (3, 2), (5, 1), (17, 1), (31, 1), (4517419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_4517419
  · decide +kernel

theorem prime_857044756679 : Nat.Prime 857044756679 := by
  apply nodeValid_prime [2, 11, 3541507259] ⟨857044756679, 11, [(2, 1), (11, 2), (3541507259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3541507259
  · decide +kernel

theorem prime_857044756961 : Nat.Prime 857044756961 := by
  apply nodeValid_prime [2, 5, 7, 23, 33270371] ⟨857044756961, 3, [(2, 5), (5, 1), (7, 1), (23, 1), (33270371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_33270371
  · decide +kernel

theorem prime_858219167369 : Nat.Prime 858219167369 := by
  apply nodeValid_prime [2, 29, 67, 673, 82039] ⟨858219167369, 3, [(2, 3), (29, 1), (67, 1), (673, 1), (82039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_67
    · exact prime_673
    · exact prime_82039
  · decide +kernel

theorem prime_858219167821 : Nat.Prime 858219167821 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 120198763] ⟨858219167821, 14, [(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (120198763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_120198763
  · decide +kernel

theorem prime_858219169609 : Nat.Prime 858219169609 := by
  apply nodeValid_prime [2, 3, 6833, 1744433] ⟨858219169609, 11, [(2, 3), (3, 2), (6833, 1), (1744433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6833
    · exact prime_1744433
  · decide +kernel

theorem prime_859394695517 : Nat.Prime 859394695517 := by
  apply nodeValid_prime [2, 7, 17, 19, 1301, 73039] ⟨859394695517, 3, [(2, 2), (7, 1), (17, 1), (19, 1), (1301, 1), (73039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_19
    · exact prime_1301
    · exact prime_73039
  · decide +kernel

theorem prime_859394703281 : Nat.Prime 859394703281 := by
  apply nodeValid_prime [2, 5, 59, 251, 725399] ⟨859394703281, 3, [(2, 4), (5, 1), (59, 1), (251, 1), (725399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_251
    · exact prime_725399
  · decide +kernel

theorem prime_859394704967 : Nat.Prime 859394704967 := by
  apply nodeValid_prime [2, 7, 37, 1659063137] ⟨859394704967, 5, [(2, 1), (7, 1), (37, 1), (1659063137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_1659063137
  · decide +kernel

theorem prime_860571313187 : Nat.Prime 860571313187 := by
  apply nodeValid_prime [2, 13, 67, 494013383] ⟨860571313187, 5, [(2, 1), (13, 1), (67, 1), (494013383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_494013383
  · decide +kernel

theorem prime_860571325283 : Nat.Prime 860571325283 := by
  apply nodeValid_prime [2, 307, 2719, 515477] ⟨860571325283, 2, [(2, 1), (307, 1), (2719, 1), (515477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_2719
    · exact prime_515477
  · decide +kernel

theorem prime_860571325337 : Nat.Prime 860571325337 := by
  apply nodeValid_prime [2, 127, 1993, 424997] ⟨860571325337, 3, [(2, 3), (127, 1), (1993, 1), (424997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_1993
    · exact prime_424997
  · decide +kernel

theorem prime_861748998091 : Nat.Prime 861748998091 := by
  apply nodeValid_prime [2, 3, 5, 2341, 2731, 4493] ⟨861748998091, 2, [(2, 1), (3, 1), (5, 1), (2341, 1), (2731, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2341
    · exact prime_2731
    · exact prime_4493
  · decide +kernel

theorem prime_861748998371 : Nat.Prime 861748998371 := by
  apply nodeValid_prime [2, 5, 13, 6628838449] ⟨861748998371, 2, [(2, 1), (5, 1), (13, 1), (6628838449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_6628838449
  · decide +kernel

theorem prime_861749029487 : Nat.Prime 861749029487 := by
  apply nodeValid_prime [2, 59, 673, 10851349] ⟨861749029487, 5, [(2, 1), (59, 1), (673, 1), (10851349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_673
    · exact prime_10851349
  · decide +kernel

theorem prime_862927831427 : Nat.Prime 862927831427 := by
  apply nodeValid_prime [2, 269, 1603955077] ⟨862927831427, 2, [(2, 1), (269, 1), (1603955077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_1603955077
  · decide +kernel

theorem prime_862927847963 : Nat.Prime 862927847963 := by
  apply nodeValid_prime [2, 41, 47119, 223339] ⟨862927847963, 2, [(2, 1), (41, 1), (47119, 1), (223339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_47119
    · exact prime_223339
  · decide +kernel

theorem prime_862927848227 : Nat.Prime 862927848227 := by
  apply nodeValid_prime [2, 16759, 25745207] ⟨862927848227, 2, [(2, 1), (16759, 1), (25745207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16759
    · exact prime_25745207
  · decide +kernel

theorem prime_864107692523 : Nat.Prime 864107692523 := by
  apply nodeValid_prime [2, 17, 19, 1697, 788231] ⟨864107692523, 2, [(2, 1), (17, 1), (19, 1), (1697, 1), (788231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_1697
    · exact prime_788231
  · decide +kernel

theorem prime_864107692813 : Nat.Prime 864107692813 := by
  apply nodeValid_prime [2, 3, 7, 13, 263769137] ⟨864107692813, 11, [(2, 2), (3, 2), (7, 1), (13, 1), (263769137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_263769137
  · decide +kernel

theorem prime_864107725823 : Nat.Prime 864107725823 := by
  apply nodeValid_prime [2, 11, 59, 281, 307, 7717] ⟨864107725823, 5, [(2, 1), (11, 1), (59, 1), (281, 1), (307, 1), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_281
    · exact prime_307
    · exact prime_7717
  · decide +kernel

theorem prime_865288708223 : Nat.Prime 865288708223 := by
  apply nodeValid_prime [2, 157, 12239, 225157] ⟨865288708223, 5, [(2, 1), (157, 1), (12239, 1), (225157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_12239
    · exact prime_225157
  · decide +kernel

theorem prime_865288708511 : Nat.Prime 865288708511 := by
  apply nodeValid_prime [2, 5, 373, 231980887] ⟨865288708511, 13, [(2, 1), (5, 1), (373, 1), (231980887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_373
    · exact prime_231980887
  · decide +kernel

theorem prime_865288716613 : Nat.Prime 865288716613 := by
  apply nodeValid_prime [2, 3, 3019, 23884529] ⟨865288716613, 2, [(2, 2), (3, 1), (3019, 1), (23884529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3019
    · exact prime_23884529
  · decide +kernel

theorem prime_866470811617 : Nat.Prime 866470811617 := by
  apply nodeValid_prime [2, 3, 2903, 1036369] ⟨866470811617, 5, [(2, 5), (3, 2), (2903, 1), (1036369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2903
    · exact prime_1036369
  · decide +kernel

theorem prime_866470811771 : Nat.Prime 866470811771 := by
  apply nodeValid_prime [2, 5, 23, 113, 1019, 32717] ⟨866470811771, 6, [(2, 1), (5, 1), (23, 1), (113, 1), (1019, 1), (32717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_113
    · exact prime_1019
    · exact prime_32717
  · decide +kernel

theorem prime_866470813003 : Nat.Prime 866470813003 := by
  apply nodeValid_prime [2, 3, 613, 78527353] ⟨866470813003, 2, [(2, 1), (3, 2), (613, 1), (78527353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_78527353
  · decide +kernel

theorem prime_867654001127 : Nat.Prime 867654001127 := by
  apply nodeValid_prime [2, 11, 31, 41039353] ⟨867654001127, 5, [(2, 1), (11, 1), (31, 2), (41039353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_41039353
  · decide +kernel

theorem prime_867654006607 : Nat.Prime 867654006607 := by
  apply nodeValid_prime [2, 3, 4441, 3618029] ⟨867654006607, 5, [(2, 1), (3, 3), (4441, 1), (3618029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4441
    · exact prime_3618029
  · decide +kernel

theorem prime_867654008233 : Nat.Prime 867654008233 := by
  apply nodeValid_prime [2, 3, 11, 53, 137, 452633] ⟨867654008233, 5, [(2, 3), (3, 1), (11, 1), (53, 1), (137, 1), (452633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_137
    · exact prime_452633
  · decide +kernel

theorem prime_868838252911 : Nat.Prime 868838252911 := by
  apply nodeValid_prime [2, 3, 5, 491, 1523, 38729] ⟨868838252911, 3, [(2, 1), (3, 1), (5, 1), (491, 1), (1523, 1), (38729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_491
    · exact prime_1523
    · exact prime_38729
  · decide +kernel

theorem prime_868838253457 : Nat.Prime 868838253457 := by
  apply nodeValid_prime [2, 3, 18100796947] ⟨868838253457, 5, [(2, 4), (3, 1), (18100796947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18100796947
  · decide +kernel

theorem prime_868838287511 : Nat.Prime 868838287511 := by
  apply nodeValid_prime [2, 5, 43, 40123, 50359] ⟨868838287511, 29, [(2, 1), (5, 1), (43, 1), (40123, 1), (50359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_40123
    · exact prime_50359
  · decide +kernel

theorem prime_870023631557 : Nat.Prime 870023631557 := by
  apply nodeValid_prime [2, 217505907889] ⟨870023631557, 2, [(2, 2), (217505907889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_217505907889
  · decide +kernel

theorem prime_870023632091 : Nat.Prime 870023632091 := by
  apply nodeValid_prime [2, 5, 87002363209] ⟨870023632091, 2, [(2, 1), (5, 1), (87002363209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_87002363209
  · decide +kernel

theorem prime_870023664611 : Nat.Prime 870023664611 := by
  apply nodeValid_prime [2, 5, 19, 67, 97, 704581] ⟨870023664611, 6, [(2, 1), (5, 1), (19, 1), (67, 1), (97, 1), (704581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_67
    · exact prime_97
    · exact prime_704581
  · decide +kernel

theorem prime_871210087763 : Nat.Prime 871210087763 := by
  apply nodeValid_prime [2, 7, 47, 181, 223, 32803] ⟨871210087763, 2, [(2, 1), (7, 1), (47, 1), (181, 1), (223, 1), (32803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_181
    · exact prime_223
    · exact prime_32803
  · decide +kernel

theorem prime_871210087849 : Nat.Prime 871210087849 := by
  apply nodeValid_prime [2, 3, 6379, 1896871] ⟨871210087849, 7, [(2, 3), (3, 2), (6379, 1), (1896871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6379
    · exact prime_1896871
  · decide +kernel

theorem prime_871210139119 : Nat.Prime 871210139119 := by
  apply nodeValid_prime [2, 3, 11, 13200153623] ⟨871210139119, 3, [(2, 1), (3, 1), (11, 1), (13200153623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13200153623
  · decide +kernel

theorem prime_872397612253 : Nat.Prime 872397612253 := by
  apply nodeValid_prime [2, 3, 43, 6427, 9743] ⟨872397612253, 6, [(2, 2), (3, 4), (43, 1), (6427, 1), (9743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_6427
    · exact prime_9743
  · decide +kernel

theorem prime_872397612367 : Nat.Prime 872397612367 := by
  apply nodeValid_prime [2, 3, 7, 673, 30863851] ⟨872397612367, 5, [(2, 1), (3, 1), (7, 1), (673, 1), (30863851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_673
    · exact prime_30863851
  · decide +kernel

theorem prime_872397703451 : Nat.Prime 872397703451 := by
  apply nodeValid_prime [2, 5, 7, 13, 163, 1176293] ⟨872397703451, 6, [(2, 1), (5, 2), (7, 1), (13, 1), (163, 1), (1176293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_163
    · exact prime_1176293
  · decide +kernel

theorem prime_873586354159 : Nat.Prime 873586354159 := by
  apply nodeValid_prime [2, 3, 7, 157, 700963] ⟨873586354159, 12, [(2, 1), (3, 4), (7, 2), (157, 1), (700963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
    · exact prime_700963
  · decide +kernel

theorem prime_873586355563 : Nat.Prime 873586355563 := by
  apply nodeValid_prime [2, 3, 41, 83, 4753901] ⟨873586355563, 3, [(2, 1), (3, 3), (41, 1), (83, 1), (4753901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_83
    · exact prime_4753901
  · decide +kernel

theorem prime_873586355657 : Nat.Prime 873586355657 := by
  apply nodeValid_prime [2, 7, 30169, 517079] ⟨873586355657, 3, [(2, 3), (7, 1), (30169, 1), (517079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_30169
    · exact prime_517079
  · decide +kernel

theorem prime_874776105139 : Nat.Prime 874776105139 := by
  apply nodeValid_prime [2, 3, 13, 11215078271] ⟨874776105139, 3, [(2, 1), (3, 1), (13, 1), (11215078271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_11215078271
  · decide +kernel

theorem prime_874776105799 : Nat.Prime 874776105799 := by
  apply nodeValid_prime [2, 3, 7, 31, 37, 73, 248749] ⟨874776105799, 3, [(2, 1), (3, 1), (7, 1), (31, 1), (37, 1), (73, 1), (248749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_37
    · exact prime_73
    · exact prime_248749
  · decide +kernel

theorem prime_874776107279 : Nat.Prime 874776107279 := by
  apply nodeValid_prime [2, 37, 79, 149636693] ⟨874776107279, 7, [(2, 1), (37, 1), (79, 1), (149636693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_79
    · exact prime_149636693
  · decide +kernel

theorem prime_875966967133 : Nat.Prime 875966967133 := by
  apply nodeValid_prime [2, 3, 59, 1237241479] ⟨875966967133, 2, [(2, 2), (3, 1), (59, 1), (1237241479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_1237241479
  · decide +kernel

theorem prime_875966967143 : Nat.Prime 875966967143 := by
  apply nodeValid_prime [2, 437983483571] ⟨875966967143, 5, [(2, 1), (437983483571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_437983483571
  · decide +kernel

theorem prime_875966967311 : Nat.Prime 875966967311 := by
  apply nodeValid_prime [2, 5, 208991, 419141] ⟨875966967311, 13, [(2, 1), (5, 1), (208991, 1), (419141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_208991
    · exact prime_419141
  · decide +kernel

theorem prime_877158921281 : Nat.Prime 877158921281 := by
  apply nodeValid_prime [2, 5, 2741121629] ⟨877158921281, 3, [(2, 6), (5, 1), (2741121629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2741121629
  · decide +kernel

theorem prime_877158923051 : Nat.Prime 877158923051 := by
  apply nodeValid_prime [2, 5, 17543178461] ⟨877158923051, 2, [(2, 1), (5, 2), (17543178461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17543178461
  · decide +kernel

theorem prime_877158927409 : Nat.Prime 877158927409 := by
  apply nodeValid_prime [2, 3, 18274144321] ⟨877158927409, 11, [(2, 4), (3, 1), (18274144321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18274144321
  · decide +kernel

theorem prime_878351987141 : Nat.Prime 878351987141 := by
  apply nodeValid_prime [2, 5, 389, 112898713] ⟨878351987141, 2, [(2, 2), (5, 1), (389, 1), (112898713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_389
    · exact prime_112898713
  · decide +kernel

theorem prime_878351987207 : Nat.Prime 878351987207 := by
  apply nodeValid_prime [2, 1831, 239855813] ⟨878351987207, 5, [(2, 1), (1831, 1), (239855813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1831
    · exact prime_239855813
  · decide +kernel

theorem prime_878351988461 : Nat.Prime 878351988461 := by
  apply nodeValid_prime [2, 5, 47, 73, 241, 53113] ⟨878351988461, 7, [(2, 2), (5, 1), (47, 1), (73, 1), (241, 1), (53113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_73
    · exact prime_241
    · exact prime_53113
  · decide +kernel

theorem prime_879546058201 : Nat.Prime 879546058201 := by
  apply nodeValid_prime [2, 3, 5, 19, 25717721] ⟨879546058201, 7, [(2, 3), (3, 2), (5, 2), (19, 1), (25717721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_25717721
  · decide +kernel

theorem prime_879546058723 : Nat.Prime 879546058723 := by
  apply nodeValid_prime [2, 3, 907, 53873947] ⟨879546058723, 3, [(2, 1), (3, 2), (907, 1), (53873947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
    · exact prime_53873947
  · decide +kernel

theorem prime_879546141251 : Nat.Prime 879546141251 := by
  apply nodeValid_prime [2, 5, 7, 1777, 8081] ⟨879546141251, 2, [(2, 1), (5, 4), (7, 2), (1777, 1), (8081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1777
    · exact prime_8081
  · decide +kernel

theorem prime_880741400843 : Nat.Prime 880741400843 := by
  apply nodeValid_prime [2, 109, 4040098169] ⟨880741400843, 2, [(2, 1), (109, 1), (4040098169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_4040098169
  · decide +kernel

theorem prime_880741493713 : Nat.Prime 880741493713 := by
  apply nodeValid_prime [2, 3, 6116260373] ⟨880741493713, 5, [(2, 4), (3, 2), (6116260373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6116260373
  · decide +kernel

theorem prime_880741494103 : Nat.Prime 880741494103 := by
  apply nodeValid_prime [2, 3, 73, 2010825329] ⟨880741494103, 3, [(2, 1), (3, 1), (73, 1), (2010825329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_2010825329
  · decide +kernel

theorem prime_881937752783 : Nat.Prime 881937752783 := by
  apply nodeValid_prime [2, 3163, 7691, 18127] ⟨881937752783, 5, [(2, 1), (3163, 1), (7691, 1), (18127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3163
    · exact prime_7691
    · exact prime_18127
  · decide +kernel

theorem prime_881937766121 : Nat.Prime 881937766121 := by
  apply nodeValid_prime [2, 5, 22048444153] ⟨881937766121, 3, [(2, 3), (5, 1), (22048444153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22048444153
  · decide +kernel

theorem prime_881937766201 : Nat.Prime 881937766201 := by
  apply nodeValid_prime [2, 3, 5, 503, 2922259] ⟨881937766201, 13, [(2, 3), (3, 1), (5, 2), (503, 1), (2922259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_503
    · exact prime_2922259
  · decide +kernel

theorem prime_883135191713 : Nat.Prime 883135191713 := by
  apply nodeValid_prime [2, 5519, 5000539] ⟨883135191713, 3, [(2, 5), (5519, 1), (5000539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5519
    · exact prime_5000539
  · decide +kernel

theorem prime_883135192573 : Nat.Prime 883135192573 := by
  apply nodeValid_prime [2, 3, 73, 12446237] ⟨883135192573, 2, [(2, 2), (3, 5), (73, 1), (12446237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_12446237
  · decide +kernel

theorem prime_883135201099 : Nat.Prime 883135201099 := by
  apply nodeValid_prime [2, 3, 103, 1429021361] ⟨883135201099, 3, [(2, 1), (3, 1), (103, 1), (1429021361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_1429021361
  · decide +kernel

theorem prime_884333755111 : Nat.Prime 884333755111 := by
  apply nodeValid_prime [2, 3, 5, 13, 5167, 438847] ⟨884333755111, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (5167, 1), (438847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_5167
    · exact prime_438847
  · decide +kernel

theorem prime_884333794871 : Nat.Prime 884333794871 := by
  apply nodeValid_prime [2, 5, 1013, 87298499] ⟨884333794871, 7, [(2, 1), (5, 1), (1013, 1), (87298499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1013
    · exact prime_87298499
  · decide +kernel

theorem prime_885533419733 : Nat.Prime 885533419733 := by
  apply nodeValid_prime [2, 13, 823, 20691967] ⟨885533419733, 2, [(2, 2), (13, 1), (823, 1), (20691967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_823
    · exact prime_20691967
  · decide +kernel

theorem prime_885533421251 : Nat.Prime 885533421251 := by
  apply nodeValid_prime [2, 5, 17, 2753, 15137] ⟨885533421251, 2, [(2, 1), (5, 4), (17, 1), (2753, 1), (15137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2753
    · exact prime_15137
  · decide +kernel

theorem prime_885533421397 : Nat.Prime 885533421397 := by
  apply nodeValid_prime [2, 3, 13, 5676496291] ⟨885533421397, 5, [(2, 2), (3, 1), (13, 1), (5676496291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5676496291
  · decide +kernel

end Sude.Lucas.Generated
