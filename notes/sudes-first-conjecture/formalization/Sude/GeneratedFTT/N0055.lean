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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3257 : Nat.Prime 3257 := by
  apply nodeValid_prime [2, 11, 37] ⟨3257, 3, [(2, 3), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_7489 : Nat.Prime 7489 := by
  apply nodeValid_prime [2, 3, 13] ⟨7489, 7, [(2, 6), (3, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_8389 : Nat.Prime 8389 := by
  apply nodeValid_prime [2, 3, 233] ⟨8389, 6, [(2, 2), (3, 2), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
  · decide +kernel

theorem prime_8923 : Nat.Prime 8923 := by
  apply nodeValid_prime [2, 3, 1487] ⟨8923, 2, [(2, 1), (3, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1487
  · decide +kernel

theorem prime_11443 : Nat.Prime 11443 := by
  apply nodeValid_prime [2, 3, 1907] ⟨11443, 2, [(2, 1), (3, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1907
  · decide +kernel

theorem prime_12071 : Nat.Prime 12071 := by
  apply nodeValid_prime [2, 5, 17, 71] ⟨12071, 11, [(2, 1), (5, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_13309 : Nat.Prime 13309 := by
  apply nodeValid_prime [2, 3, 1109] ⟨13309, 6, [(2, 2), (3, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1109
  · decide +kernel

theorem prime_15031 : Nat.Prime 15031 := by
  apply nodeValid_prime [2, 3, 5, 167] ⟨15031, 3, [(2, 1), (3, 2), (5, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
  · decide +kernel

theorem prime_17393 : Nat.Prime 17393 := by
  apply nodeValid_prime [2, 1087] ⟨17393, 3, [(2, 4), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1087
  · decide +kernel

theorem prime_18257 : Nat.Prime 18257 := by
  apply nodeValid_prime [2, 7, 163] ⟨18257, 5, [(2, 4), (7, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163
  · decide +kernel

theorem prime_19841 : Nat.Prime 19841 := by
  apply nodeValid_prime [2, 5, 31] ⟨19841, 3, [(2, 7), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_21317 : Nat.Prime 21317 := by
  apply nodeValid_prime [2, 73] ⟨21317, 2, [(2, 2), (73, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73
  · decide +kernel

theorem prime_22613 : Nat.Prime 22613 := by
  apply nodeValid_prime [2, 5653] ⟨22613, 2, [(2, 2), (5653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5653
  · decide +kernel

theorem prime_24859 : Nat.Prime 24859 := by
  apply nodeValid_prime [2, 3, 1381] ⟨24859, 2, [(2, 1), (3, 2), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1381
  · decide +kernel

theorem prime_26177 : Nat.Prime 26177 := by
  apply nodeValid_prime [2, 409] ⟨26177, 3, [(2, 6), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_409
  · decide +kernel

theorem prime_27431 : Nat.Prime 27431 := by
  apply nodeValid_prime [2, 5, 13, 211] ⟨27431, 17, [(2, 1), (5, 1), (13, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_211
  · decide +kernel

theorem prime_27817 : Nat.Prime 27817 := by
  apply nodeValid_prime [2, 3, 19, 61] ⟨27817, 5, [(2, 3), (3, 1), (19, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_29347 : Nat.Prime 29347 := by
  apply nodeValid_prime [2, 3, 67, 73] ⟨29347, 3, [(2, 1), (3, 1), (67, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_73
  · decide +kernel

theorem prime_33809 : Nat.Prime 33809 := by
  apply nodeValid_prime [2, 2113] ⟨33809, 3, [(2, 4), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2113
  · decide +kernel

theorem prime_34919 : Nat.Prime 34919 := by
  apply nodeValid_prime [2, 13, 17, 79] ⟨34919, 19, [(2, 1), (13, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_37339 : Nat.Prime 37339 := by
  apply nodeValid_prime [2, 3, 7, 127] ⟨37339, 3, [(2, 1), (3, 1), (7, 2), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_39409 : Nat.Prime 39409 := by
  apply nodeValid_prime [2, 3, 821] ⟨39409, 7, [(2, 4), (3, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_821
  · decide +kernel

theorem prime_49333 : Nat.Prime 49333 := by
  apply nodeValid_prime [2, 3, 4111] ⟨49333, 2, [(2, 2), (3, 1), (4111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4111
  · decide +kernel

theorem prime_55711 : Nat.Prime 55711 := by
  apply nodeValid_prime [2, 3, 5, 619] ⟨55711, 3, [(2, 1), (3, 2), (5, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_619
  · decide +kernel

theorem prime_57709 : Nat.Prime 57709 := by
  apply nodeValid_prime [2, 3, 7, 229] ⟨57709, 2, [(2, 2), (3, 2), (7, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_229
  · decide +kernel

theorem prime_58027 : Nat.Prime 58027 := by
  apply nodeValid_prime [2, 3, 19, 509] ⟨58027, 2, [(2, 1), (3, 1), (19, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_509
  · decide +kernel

theorem prime_58679 : Nat.Prime 58679 := by
  apply nodeValid_prime [2, 29339] ⟨58679, 11, [(2, 1), (29339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29339
  · decide +kernel

theorem prime_64793 : Nat.Prime 64793 := by
  apply nodeValid_prime [2, 7, 13, 89] ⟨64793, 3, [(2, 3), (7, 1), (13, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_89
  · decide +kernel

theorem prime_66889 : Nat.Prime 66889 := by
  apply nodeValid_prime [2, 3, 929] ⟨66889, 17, [(2, 3), (3, 2), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
  · decide +kernel

theorem prime_68909 : Nat.Prime 68909 := by
  apply nodeValid_prime [2, 7, 23, 107] ⟨68909, 2, [(2, 2), (7, 1), (23, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_107
  · decide +kernel

theorem prime_74021 : Nat.Prime 74021 := by
  apply nodeValid_prime [2, 5, 3701] ⟨74021, 2, [(2, 2), (5, 1), (3701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3701
  · decide +kernel

theorem prime_78697 : Nat.Prime 78697 := by
  apply nodeValid_prime [2, 3, 1093] ⟨78697, 5, [(2, 3), (3, 2), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1093
  · decide +kernel

theorem prime_80677 : Nat.Prime 80677 := by
  apply nodeValid_prime [2, 3, 83] ⟨80677, 2, [(2, 2), (3, 5), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_87613 : Nat.Prime 87613 := by
  apply nodeValid_prime [2, 3, 7, 149] ⟨87613, 2, [(2, 2), (3, 1), (7, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_89231 : Nat.Prime 89231 := by
  apply nodeValid_prime [2, 5, 8923] ⟨89231, 14, [(2, 1), (5, 1), (8923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8923
  · decide +kernel

theorem prime_89491 : Nat.Prime 89491 := by
  apply nodeValid_prime [2, 3, 5, 19, 157] ⟨89491, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_157
  · decide +kernel

theorem prime_91303 : Nat.Prime 91303 := by
  apply nodeValid_prime [2, 3, 15217] ⟨91303, 3, [(2, 1), (3, 1), (15217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15217
  · decide +kernel

theorem prime_98897 : Nat.Prime 98897 := by
  apply nodeValid_prime [2, 7, 883] ⟨98897, 3, [(2, 4), (7, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_883
  · decide +kernel

theorem prime_112799 : Nat.Prime 112799 := by
  apply nodeValid_prime [2, 7, 1151] ⟨112799, 7, [(2, 1), (7, 2), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1151
  · decide +kernel

theorem prime_114031 : Nat.Prime 114031 := by
  apply nodeValid_prime [2, 3, 5, 7, 181] ⟨114031, 6, [(2, 1), (3, 2), (5, 1), (7, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_181
  · decide +kernel

theorem prime_119047 : Nat.Prime 119047 := by
  apply nodeValid_prime [2, 3, 19841] ⟨119047, 3, [(2, 1), (3, 1), (19841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19841
  · decide +kernel

theorem prime_123979 : Nat.Prime 123979 := by
  apply nodeValid_prime [2, 3, 20663] ⟨123979, 2, [(2, 1), (3, 1), (20663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20663
  · decide +kernel

theorem prime_141731 : Nat.Prime 141731 := by
  apply nodeValid_prime [2, 5, 14173] ⟨141731, 2, [(2, 1), (5, 1), (14173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14173
  · decide +kernel

theorem prime_157277 : Nat.Prime 157277 := by
  apply nodeValid_prime [2, 7, 41, 137] ⟨157277, 3, [(2, 2), (7, 1), (41, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_137
  · decide +kernel

theorem prime_157637 : Nat.Prime 157637 := by
  apply nodeValid_prime [2, 39409] ⟨157637, 2, [(2, 2), (39409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39409
  · decide +kernel

theorem prime_162671 : Nat.Prime 162671 := by
  apply nodeValid_prime [2, 5, 16267] ⟨162671, 11, [(2, 1), (5, 1), (16267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16267
  · decide +kernel

theorem prime_164953 : Nat.Prime 164953 := by
  apply nodeValid_prime [2, 3, 29, 79] ⟨164953, 5, [(2, 3), (3, 2), (29, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_79
  · decide +kernel

theorem prime_202729 : Nat.Prime 202729 := by
  apply nodeValid_prime [2, 3, 8447] ⟨202729, 11, [(2, 3), (3, 1), (8447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8447
  · decide +kernel

theorem prime_283463 : Nat.Prime 283463 := by
  apply nodeValid_prime [2, 141731] ⟨283463, 5, [(2, 1), (141731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_141731
  · decide +kernel

theorem prime_322709 : Nat.Prime 322709 := by
  apply nodeValid_prime [2, 80677] ⟨322709, 2, [(2, 2), (80677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_80677
  · decide +kernel

theorem prime_365473 : Nat.Prime 365473 := by
  apply nodeValid_prime [2, 3, 47] ⟨365473, 5, [(2, 5), (3, 5), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_396379 : Nat.Prime 396379 := by
  apply nodeValid_prime [2, 3, 19, 61] ⟨396379, 2, [(2, 1), (3, 2), (19, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_452989 : Nat.Prime 452989 := by
  apply nodeValid_prime [2, 3, 12583] ⟨452989, 6, [(2, 2), (3, 2), (12583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12583
  · decide +kernel

theorem prime_462443 : Nat.Prime 462443 := by
  apply nodeValid_prime [2, 59, 3919] ⟨462443, 2, [(2, 1), (59, 1), (3919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_3919
  · decide +kernel

theorem prime_484751 : Nat.Prime 484751 := by
  apply nodeValid_prime [2, 5, 7, 277] ⟨484751, 7, [(2, 1), (5, 3), (7, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_510803 : Nat.Prime 510803 := by
  apply nodeValid_prime [2, 97, 2633] ⟨510803, 2, [(2, 1), (97, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_2633
  · decide +kernel

theorem prime_516017 : Nat.Prime 516017 := by
  apply nodeValid_prime [2, 32251] ⟨516017, 3, [(2, 4), (32251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32251
  · decide +kernel

theorem prime_558979 : Nat.Prime 558979 := by
  apply nodeValid_prime [2, 3, 7, 13309] ⟨558979, 2, [(2, 1), (3, 1), (7, 1), (13309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13309
  · decide +kernel

theorem prime_634331 : Nat.Prime 634331 := by
  apply nodeValid_prime [2, 5, 229, 277] ⟨634331, 10, [(2, 1), (5, 1), (229, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_277
  · decide +kernel

theorem prime_845069 : Nat.Prime 845069 := by
  apply nodeValid_prime [2, 7, 30181] ⟨845069, 3, [(2, 2), (7, 1), (30181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_30181
  · decide +kernel

theorem prime_876131 : Nat.Prime 876131 := by
  apply nodeValid_prime [2, 5, 87613] ⟨876131, 7, [(2, 1), (5, 1), (87613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_87613
  · decide +kernel

theorem prime_1045493 : Nat.Prime 1045493 := by
  apply nodeValid_prime [2, 7, 37339] ⟨1045493, 2, [(2, 2), (7, 1), (37339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37339
  · decide +kernel

theorem prime_1078417 : Nat.Prime 1078417 := by
  apply nodeValid_prime [2, 3, 7489] ⟨1078417, 5, [(2, 4), (3, 2), (7489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7489
  · decide +kernel

theorem prime_1209073 : Nat.Prime 1209073 := by
  apply nodeValid_prime [2, 3, 25189] ⟨1209073, 5, [(2, 4), (3, 1), (25189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25189
  · decide +kernel

theorem prime_1312133 : Nat.Prime 1312133 := by
  apply nodeValid_prime [2, 223, 1471] ⟨1312133, 2, [(2, 2), (223, 1), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_1471
  · decide +kernel

theorem prime_1338349 : Nat.Prime 1338349 := by
  apply nodeValid_prime [2, 3, 11, 10139] ⟨1338349, 7, [(2, 2), (3, 1), (11, 1), (10139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_10139
  · decide +kernel

theorem prime_1368373 : Nat.Prime 1368373 := by
  apply nodeValid_prime [2, 3, 114031] ⟨1368373, 5, [(2, 2), (3, 1), (114031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_114031
  · decide +kernel

theorem prime_1416473 : Nat.Prime 1416473 := by
  apply nodeValid_prime [2, 59, 3001] ⟨1416473, 3, [(2, 3), (59, 1), (3001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_3001
  · decide +kernel

theorem prime_1579187 : Nat.Prime 1579187 := by
  apply nodeValid_prime [2, 7, 112799] ⟨1579187, 2, [(2, 1), (7, 1), (112799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_112799
  · decide +kernel

theorem prime_1780147 : Nat.Prime 1780147 := by
  apply nodeValid_prime [2, 3, 98897] ⟨1780147, 3, [(2, 1), (3, 2), (98897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_98897
  · decide +kernel

theorem prime_1885627 : Nat.Prime 1885627 := by
  apply nodeValid_prime [2, 3, 34919] ⟨1885627, 7, [(2, 1), (3, 3), (34919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34919
  · decide +kernel

theorem prime_1952053 : Nat.Prime 1952053 := by
  apply nodeValid_prime [2, 3, 162671] ⟨1952053, 5, [(2, 2), (3, 1), (162671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_162671
  · decide +kernel

theorem prime_2104909 : Nat.Prime 2104909 := by
  apply nodeValid_prime [2, 3, 13, 103, 131] ⟨2104909, 2, [(2, 2), (3, 1), (13, 1), (103, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
    · exact prime_131
  · decide +kernel

theorem prime_2457709 : Nat.Prime 2457709 := by
  apply nodeValid_prime [2, 3, 11, 43, 433] ⟨2457709, 2, [(2, 2), (3, 1), (11, 1), (43, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_433
  · decide +kernel

theorem prime_2541593 : Nat.Prime 2541593 := by
  apply nodeValid_prime [2, 19, 23, 727] ⟨2541593, 3, [(2, 3), (19, 1), (23, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_727
  · decide +kernel

theorem prime_2804437 : Nat.Prime 2804437 := by
  apply nodeValid_prime [2, 3, 23, 1129] ⟨2804437, 2, [(2, 2), (3, 3), (23, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1129
  · decide +kernel

theorem prime_3000869 : Nat.Prime 3000869 := by
  apply nodeValid_prime [2, 13, 57709] ⟨3000869, 2, [(2, 2), (13, 1), (57709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_57709
  · decide +kernel

theorem prime_3096103 : Nat.Prime 3096103 := by
  apply nodeValid_prime [2, 3, 516017] ⟨3096103, 3, [(2, 1), (3, 1), (516017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_516017
  · decide +kernel

theorem prime_3295741 : Nat.Prime 3295741 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 59] ⟨3295741, 10, [(2, 2), (3, 1), (5, 1), (7, 2), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_3805987 : Nat.Prime 3805987 := by
  apply nodeValid_prime [2, 3, 634331] ⟨3805987, 2, [(2, 1), (3, 1), (634331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_634331
  · decide +kernel

theorem prime_3968483 : Nat.Prime 3968483 := by
  apply nodeValid_prime [2, 7, 283463] ⟨3968483, 2, [(2, 1), (7, 1), (283463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_283463
  · decide +kernel

theorem prime_4078757 : Nat.Prime 4078757 := by
  apply nodeValid_prime [2, 11, 92699] ⟨4078757, 2, [(2, 2), (11, 1), (92699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_92699
  · decide +kernel

theorem prime_4842911 : Nat.Prime 4842911 := by
  apply nodeValid_prime [2, 5, 19, 71, 359] ⟨4842911, 13, [(2, 1), (5, 1), (19, 1), (71, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_71
    · exact prime_359
  · decide +kernel

theorem prime_5996633 : Nat.Prime 5996633 := by
  apply nodeValid_prime [2, 53, 14143] ⟨5996633, 3, [(2, 3), (53, 1), (14143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_14143
  · decide +kernel

theorem prime_6802493 : Nat.Prime 6802493 := by
  apply nodeValid_prime [2, 547, 3109] ⟨6802493, 2, [(2, 2), (547, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_547
    · exact prime_3109
  · decide +kernel

theorem prime_6813473 : Nat.Prime 6813473 := by
  apply nodeValid_prime [2, 149, 1429] ⟨6813473, 3, [(2, 5), (149, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_1429
  · decide +kernel

theorem prime_7277321 : Nat.Prime 7277321 := by
  apply nodeValid_prime [2, 5, 43, 4231] ⟨7277321, 3, [(2, 3), (5, 1), (43, 1), (4231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_4231
  · decide +kernel

theorem prime_7936967 : Nat.Prime 7936967 := by
  apply nodeValid_prime [2, 3968483] ⟨7936967, 5, [(2, 1), (3968483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3968483
  · decide +kernel

theorem prime_8579663 : Nat.Prime 8579663 := by
  apply nodeValid_prime [2, 7, 13, 17, 47, 59] ⟨8579663, 7, [(2, 1), (7, 1), (13, 1), (17, 1), (47, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_47
    · exact prime_59
  · decide +kernel

theorem prime_13203901 : Nat.Prime 13203901 := by
  apply nodeValid_prime [2, 3, 5, 17, 863] ⟨13203901, 6, [(2, 2), (3, 2), (5, 2), (17, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_863
  · decide +kernel

theorem prime_14483081 : Nat.Prime 14483081 := by
  apply nodeValid_prime [2, 5, 127, 2851] ⟨14483081, 6, [(2, 3), (5, 1), (127, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_2851
  · decide +kernel

theorem prime_16135451 : Nat.Prime 16135451 := by
  apply nodeValid_prime [2, 5, 322709] ⟨16135451, 2, [(2, 1), (5, 2), (322709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_322709
  · decide +kernel

theorem prime_16345697 : Nat.Prime 16345697 := by
  apply nodeValid_prime [2, 510803] ⟨16345697, 3, [(2, 5), (510803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_510803
  · decide +kernel

theorem prime_16513129 : Nat.Prime 16513129 := by
  apply nodeValid_prime [2, 3, 19, 12071] ⟨16513129, 7, [(2, 3), (3, 2), (19, 1), (12071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_12071
  · decide +kernel

theorem prime_17159327 : Nat.Prime 17159327 := by
  apply nodeValid_prime [2, 8579663] ⟨17159327, 5, [(2, 1), (8579663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8579663
  · decide +kernel

theorem prime_18305207 : Nat.Prime 18305207 := by
  apply nodeValid_prime [2, 29, 10883] ⟨18305207, 5, [(2, 1), (29, 2), (10883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_10883
  · decide +kernel

theorem prime_27681859 : Nat.Prime 27681859 := by
  apply nodeValid_prime [2, 3, 109, 4703] ⟨27681859, 2, [(2, 1), (3, 3), (109, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_4703
  · decide +kernel

theorem prime_30917563 : Nat.Prime 30917563 := by
  apply nodeValid_prime [2, 3, 13, 396379] ⟨30917563, 2, [(2, 1), (3, 1), (13, 1), (396379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_396379
  · decide +kernel

theorem prime_36449827 : Nat.Prime 36449827 := by
  apply nodeValid_prime [2, 3, 7, 123979] ⟨36449827, 3, [(2, 1), (3, 1), (7, 2), (123979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_123979
  · decide +kernel

theorem prime_39500641 : Nat.Prime 39500641 := by
  apply nodeValid_prime [2, 3, 5, 27431] ⟨39500641, 7, [(2, 5), (3, 2), (5, 1), (27431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27431
  · decide +kernel

theorem prime_39608339 : Nat.Prime 39608339 := by
  apply nodeValid_prime [2, 7, 11, 311, 827] ⟨39608339, 2, [(2, 1), (7, 1), (11, 1), (311, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_311
    · exact prime_827
  · decide +kernel

theorem prime_44414297 : Nat.Prime 44414297 := by
  apply nodeValid_prime [2, 83, 66889] ⟨44414297, 3, [(2, 3), (83, 1), (66889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_66889
  · decide +kernel

theorem prime_46849273 : Nat.Prime 46849273 := by
  apply nodeValid_prime [2, 3, 1952053] ⟨46849273, 5, [(2, 3), (3, 1), (1952053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1952053
  · decide +kernel

theorem prime_48569701 : Nat.Prime 48569701 := by
  apply nodeValid_prime [2, 3, 5, 19, 8521] ⟨48569701, 10, [(2, 2), (3, 1), (5, 2), (19, 1), (8521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_8521
  · decide +kernel

theorem prime_50213161 : Nat.Prime 50213161 := by
  apply nodeValid_prime [2, 3, 5, 101, 1381] ⟨50213161, 14, [(2, 3), (3, 2), (5, 1), (101, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_1381
  · decide +kernel

theorem prime_50831861 : Nat.Prime 50831861 := by
  apply nodeValid_prime [2, 5, 2541593] ⟨50831861, 2, [(2, 2), (5, 1), (2541593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2541593
  · decide +kernel

theorem prime_51245591 : Nat.Prime 51245591 := by
  apply nodeValid_prime [2, 5, 11, 103, 4523] ⟨51245591, 11, [(2, 1), (5, 1), (11, 1), (103, 1), (4523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_103
    · exact prime_4523
  · decide +kernel

theorem prime_58320281 : Nat.Prime 58320281 := by
  apply nodeValid_prime [2, 5, 97, 15031] ⟨58320281, 6, [(2, 3), (5, 1), (97, 1), (15031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_15031
  · decide +kernel

theorem prime_74197159 : Nat.Prime 74197159 := by
  apply nodeValid_prime [2, 3, 7, 829, 2131] ⟨74197159, 6, [(2, 1), (3, 1), (7, 1), (829, 1), (2131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_829
    · exact prime_2131
  · decide +kernel

theorem prime_81761677 : Nat.Prime 81761677 := by
  apply nodeValid_prime [2, 3, 6813473] ⟨81761677, 2, [(2, 2), (3, 1), (6813473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6813473
  · decide +kernel

theorem prime_86197039 : Nat.Prime 86197039 := by
  apply nodeValid_prime [2, 3, 17, 845069] ⟨86197039, 6, [(2, 1), (3, 1), (17, 1), (845069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_845069
  · decide +kernel

theorem prime_104819003 : Nat.Prime 104819003 := by
  apply nodeValid_prime [2, 37, 1416473] ⟨104819003, 2, [(2, 1), (37, 1), (1416473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1416473
  · decide +kernel

theorem prime_145799309 : Nat.Prime 145799309 := by
  apply nodeValid_prime [2, 36449827] ⟨145799309, 2, [(2, 2), (36449827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36449827
  · decide +kernel

theorem prime_163424629 : Nat.Prime 163424629 := by
  apply nodeValid_prime [2, 3, 29, 17393] ⟨163424629, 2, [(2, 2), (3, 4), (29, 1), (17393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_17393
  · decide +kernel

theorem prime_172503257 : Nat.Prime 172503257 := by
  apply nodeValid_prime [2, 59, 365473] ⟨172503257, 3, [(2, 3), (59, 1), (365473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_365473
  · decide +kernel

theorem prime_206361143 : Nat.Prime 206361143 := by
  apply nodeValid_prime [2, 13, 7936967] ⟨206361143, 5, [(2, 1), (13, 1), (7936967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_7936967
  · decide +kernel

theorem prime_256272899 : Nat.Prime 256272899 := by
  apply nodeValid_prime [2, 7, 18305207] ⟨256272899, 2, [(2, 1), (7, 1), (18305207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_18305207
  · decide +kernel

theorem prime_415916359 : Nat.Prime 415916359 := by
  apply nodeValid_prime [2, 3, 11, 13, 484751] ⟨415916359, 6, [(2, 1), (3, 1), (11, 1), (13, 1), (484751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_484751
  · decide +kernel

theorem prime_446858333 : Nat.Prime 446858333 := by
  apply nodeValid_prime [2, 29, 211, 18257] ⟨446858333, 2, [(2, 2), (29, 1), (211, 1), (18257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_211
    · exact prime_18257
  · decide +kernel

theorem prime_474605279 : Nat.Prime 474605279 := by
  apply nodeValid_prime [2, 7, 4842911] ⟨474605279, 7, [(2, 1), (7, 2), (4842911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4842911
  · decide +kernel

theorem prime_626437001 : Nat.Prime 626437001 := by
  apply nodeValid_prime [2, 5, 7, 89491] ⟨626437001, 3, [(2, 3), (5, 3), (7, 1), (89491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_89491
  · decide +kernel

theorem prime_718225723 : Nat.Prime 718225723 := by
  apply nodeValid_prime [2, 3, 37, 1078417] ⟨718225723, 3, [(2, 1), (3, 2), (37, 1), (1078417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1078417
  · decide +kernel

theorem prime_847281007 : Nat.Prime 847281007 := by
  apply nodeValid_prime [2, 3, 11, 13, 113, 971] ⟨847281007, 3, [(2, 1), (3, 3), (11, 1), (13, 1), (113, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_113
    · exact prime_971
  · decide +kernel

theorem prime_3591572141 : Nat.Prime 3591572141 := by
  apply nodeValid_prime [2, 5, 13, 167, 181, 457] ⟨3591572141, 2, [(2, 2), (5, 1), (13, 1), (167, 1), (181, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_167
    · exact prime_181
    · exact prime_457
  · decide +kernel

theorem prime_4637634451 : Nat.Prime 4637634451 := by
  apply nodeValid_prime [2, 3, 5, 30917563] ⟨4637634451, 10, [(2, 1), (3, 1), (5, 2), (30917563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_30917563
  · decide +kernel

theorem prime_5711986087 : Nat.Prime 5711986087 := by
  apply nodeValid_prime [2, 3, 6053, 157277] ⟨5711986087, 3, [(2, 1), (3, 1), (6053, 1), (157277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6053
    · exact prime_157277
  · decide +kernel

theorem prime_6020978857 : Nat.Prime 6020978857 := by
  apply nodeValid_prime [2, 3, 19, 13203901] ⟨6020978857, 5, [(2, 3), (3, 1), (19, 1), (13203901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_13203901
  · decide +kernel

theorem prime_10234962343 : Nat.Prime 10234962343 := by
  apply nodeValid_prime [2, 3, 11, 59, 876131] ⟨10234962343, 3, [(2, 1), (3, 2), (11, 1), (59, 1), (876131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_876131
  · decide +kernel

theorem prime_21923361557 : Nat.Prime 21923361557 := by
  apply nodeValid_prime [2, 1571, 1747, 1997] ⟨21923361557, 2, [(2, 2), (1571, 1), (1747, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1571
    · exact prime_1747
    · exact prime_1997
  · decide +kernel

theorem prime_33863917489 : Nat.Prime 33863917489 := by
  apply nodeValid_prime [2, 3, 7727, 91303] ⟨33863917489, 7, [(2, 4), (3, 1), (7727, 1), (91303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7727
    · exact prime_91303
  · decide +kernel

theorem prime_39770392873 : Nat.Prime 39770392873 := by
  apply nodeValid_prime [2, 3, 7, 173, 1368373] ⟨39770392873, 5, [(2, 3), (3, 1), (7, 1), (173, 1), (1368373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173
    · exact prime_1368373
  · decide +kernel

theorem prime_158871203873 : Nat.Prime 158871203873 := by
  apply nodeValid_prime [2, 157, 641, 49333] ⟨158871203873, 3, [(2, 5), (157, 1), (641, 1), (49333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_641
    · exact prime_49333
  · decide +kernel

theorem prime_159924927641 : Nat.Prime 159924927641 := by
  apply nodeValid_prime [2, 5, 233, 17159327] ⟨159924927641, 3, [(2, 3), (5, 1), (233, 1), (17159327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
    · exact prime_17159327
  · decide +kernel

theorem prime_243389724967 : Nat.Prime 243389724967 := by
  apply nodeValid_prime [2, 3, 43, 104819003] ⟨243389724967, 3, [(2, 1), (3, 3), (43, 1), (104819003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_104819003
  · decide +kernel

theorem prime_948189689693 : Nat.Prime 948189689693 := by
  apply nodeValid_prime [2, 7, 33863917489] ⟨948189689693, 3, [(2, 2), (7, 1), (33863917489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_33863917489
  · decide +kernel

theorem prime_948189690443 : Nat.Prime 948189690443 := by
  apply nodeValid_prime [2, 83, 5711986087] ⟨948189690443, 2, [(2, 1), (83, 1), (5711986087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_5711986087
  · decide +kernel

theorem prime_948189697459 : Nat.Prime 948189697459 := by
  apply nodeValid_prime [2, 3, 967, 163424629] ⟨948189697459, 2, [(2, 1), (3, 1), (967, 1), (163424629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
    · exact prime_163424629
  · decide +kernel

theorem prime_949447363649 : Nat.Prime 949447363649 := by
  apply nodeValid_prime [2, 7, 109, 349, 55711] ⟨949447363649, 3, [(2, 6), (7, 1), (109, 1), (349, 1), (55711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109
    · exact prime_349
    · exact prime_55711
  · decide +kernel

theorem prime_949447366619 : Nat.Prime 949447366619 := by
  apply nodeValid_prime [2, 10133, 46849273] ⟨949447366619, 2, [(2, 1), (10133, 1), (46849273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10133
    · exact prime_46849273
  · decide +kernel

theorem prime_949447381331 : Nat.Prime 949447381331 := by
  apply nodeValid_prime [2, 5, 7, 26177, 74021] ⟨949447381331, 2, [(2, 1), (5, 1), (7, 2), (26177, 1), (74021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_26177
    · exact prime_74021
  · decide +kernel

theorem prime_950706190631 : Nat.Prime 950706190631 := by
  apply nodeValid_prime [2, 5, 7, 47, 239, 1209073] ⟨950706190631, 7, [(2, 1), (5, 1), (7, 1), (47, 1), (239, 1), (1209073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_239
    · exact prime_1209073
  · decide +kernel

theorem prime_950706191231 : Nat.Prime 950706191231 := by
  apply nodeValid_prime [2, 5, 173, 6983, 78697] ⟨950706191231, 11, [(2, 1), (5, 1), (173, 1), (6983, 1), (78697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_6983
    · exact prime_78697
  · decide +kernel

theorem prime_950706195821 : Nat.Prime 950706195821 := by
  apply nodeValid_prime [2, 5, 7927, 5996633] ⟨950706195821, 2, [(2, 2), (5, 1), (7927, 1), (5996633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7927
    · exact prime_5996633
  · decide +kernel

theorem prime_951966139601 : Nat.Prime 951966139601 := by
  apply nodeValid_prime [2, 5, 7, 48569701] ⟨951966139601, 3, [(2, 4), (5, 2), (7, 2), (48569701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_48569701
  · decide +kernel

theorem prime_951966139651 : Nat.Prime 951966139651 := by
  apply nodeValid_prime [2, 3, 5, 31, 73, 2804437] ⟨951966139651, 2, [(2, 1), (3, 1), (5, 2), (31, 1), (73, 1), (2804437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_73
    · exact prime_2804437
  · decide +kernel

theorem prime_951966144341 : Nat.Prime 951966144341 := by
  apply nodeValid_prime [2, 5, 22613, 2104909] ⟨951966144341, 2, [(2, 2), (5, 1), (22613, 1), (2104909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22613
    · exact prime_2104909
  · decide +kernel

theorem prime_953227168507 : Nat.Prime 953227168507 := by
  apply nodeValid_prime [2, 3, 19, 383, 7277321] ⟨953227168507, 2, [(2, 1), (3, 2), (19, 1), (383, 1), (7277321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_383
    · exact prime_7277321
  · decide +kernel

theorem prime_953227169431 : Nat.Prime 953227169431 := by
  apply nodeValid_prime [2, 3, 5, 31, 311, 3295741] ⟨953227169431, 3, [(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (3295741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_311
    · exact prime_3295741
  · decide +kernel

theorem prime_953227223239 : Nat.Prime 953227223239 := by
  apply nodeValid_prime [2, 3, 158871203873] ⟨953227223239, 3, [(2, 1), (3, 1), (158871203873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_158871203873
  · decide +kernel

theorem prime_954489399289 : Nat.Prime 954489399289 := by
  apply nodeValid_prime [2, 3, 89, 446858333] ⟨954489399289, 14, [(2, 3), (3, 1), (89, 1), (446858333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_446858333
  · decide +kernel

theorem prime_954489399527 : Nat.Prime 954489399527 := by
  apply nodeValid_prime [2, 13, 37, 29347, 33809] ⟨954489399527, 5, [(2, 1), (13, 1), (37, 1), (29347, 1), (33809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_29347
    · exact prime_33809
  · decide +kernel

theorem prime_954489428953 : Nat.Prime 954489428953 := by
  apply nodeValid_prime [2, 3, 39770392873] ⟨954489428953, 5, [(2, 3), (3, 1), (39770392873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39770392873
  · decide +kernel

theorem prime_955752765029 : Nat.Prime 955752765029 := by
  apply nodeValid_prime [2, 17, 241, 58320281] ⟨955752765029, 2, [(2, 2), (17, 1), (241, 1), (58320281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_241
    · exact prime_58320281
  · decide +kernel

theorem prime_955752768433 : Nat.Prime 955752768433 := by
  apply nodeValid_prime [2, 3, 7, 11, 86197039] ⟨955752768433, 13, [(2, 4), (3, 2), (7, 1), (11, 1), (86197039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_86197039
  · decide +kernel

theorem prime_955752769549 : Nat.Prime 955752769549 := by
  apply nodeValid_prime [2, 3, 983, 3000869] ⟨955752769549, 2, [(2, 2), (3, 4), (983, 1), (3000869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_983
    · exact prime_3000869
  · decide +kernel

theorem prime_957017135383 : Nat.Prime 957017135383 := by
  apply nodeValid_prime [2, 3, 7, 11, 101, 491, 41771] ⟨957017135383, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (101, 1), (491, 1), (41771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_101
    · exact prime_491
    · exact prime_41771
  · decide +kernel

theorem prime_957017138347 : Nat.Prime 957017138347 := by
  apply nodeValid_prime [2, 3, 7211, 2457709] ⟨957017138347, 3, [(2, 1), (3, 3), (7211, 1), (2457709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7211
    · exact prime_2457709
  · decide +kernel

theorem prime_957017229349 : Nat.Prime 957017229349 := by
  apply nodeValid_prime [2, 3, 43, 67, 27681859] ⟨957017229349, 7, [(2, 2), (3, 1), (43, 1), (67, 1), (27681859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_67
    · exact prime_27681859
  · decide +kernel

theorem prime_958282832323 : Nat.Prime 958282832323 := by
  apply nodeValid_prime [2, 3, 3257, 16345697] ⟨958282832323, 3, [(2, 1), (3, 2), (3257, 1), (16345697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3257
    · exact prime_16345697
  · decide +kernel

theorem prime_958282872073 : Nat.Prime 958282872073 := by
  apply nodeValid_prime [2, 3, 29, 31, 44414297] ⟨958282872073, 17, [(2, 3), (3, 1), (29, 1), (31, 1), (44414297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
    · exact prime_44414297
  · decide +kernel

theorem prime_958282874047 : Nat.Prime 958282874047 := by
  apply nodeValid_prime [2, 3, 5521, 119047] ⟨958282874047, 3, [(2, 1), (3, 6), (5521, 1), (119047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5521
    · exact prime_119047
  · decide +kernel

theorem prime_959549565847 : Nat.Prime 959549565847 := by
  apply nodeValid_prime [2, 3, 159924927641] ⟨959549565847, 3, [(2, 1), (3, 1), (159924927641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_159924927641
  · decide +kernel

theorem prime_959549565929 : Nat.Prime 959549565929 := by
  apply nodeValid_prime [2, 167, 718225723] ⟨959549565929, 3, [(2, 3), (167, 1), (718225723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_718225723
  · decide +kernel

theorem prime_959549571173 : Nat.Prime 959549571173 := by
  apply nodeValid_prime [2, 6073, 39500641] ⟨959549571173, 2, [(2, 2), (6073, 1), (39500641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6073
    · exact prime_39500641
  · decide +kernel

theorem prime_960817446311 : Nat.Prime 960817446311 := by
  apply nodeValid_prime [2, 5, 659, 145799309] ⟨960817446311, 7, [(2, 1), (5, 1), (659, 1), (145799309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_659
    · exact prime_145799309
  · decide +kernel

theorem prime_960817481521 : Nat.Prime 960817481521 := by
  apply nodeValid_prime [2, 3, 5, 13, 41, 109, 68909] ⟨960817481521, 17, [(2, 4), (3, 1), (5, 1), (13, 1), (41, 1), (109, 1), (68909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_109
    · exact prime_68909
  · decide +kernel

theorem prime_960817481809 : Nat.Prime 960817481809 := by
  apply nodeValid_prime [2, 3, 97, 206361143] ⟨960817481809, 7, [(2, 4), (3, 1), (97, 1), (206361143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_206361143
  · decide +kernel

theorem prime_962086460243 : Nat.Prime 962086460243 := by
  apply nodeValid_prime [2, 47, 10234962343] ⟨962086460243, 2, [(2, 1), (47, 1), (10234962343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_10234962343
  · decide +kernel

theorem prime_962086553783 : Nat.Prime 962086553783 := by
  apply nodeValid_prime [2, 31, 41, 71, 659, 8089] ⟨962086553783, 5, [(2, 1), (31, 1), (41, 1), (71, 1), (659, 1), (8089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41
    · exact prime_71
    · exact prime_659
    · exact prime_8089
  · decide +kernel

theorem prime_962086554311 : Nat.Prime 962086554311 := by
  apply nodeValid_prime [2, 5, 7, 347, 39608339] ⟨962086554311, 7, [(2, 1), (5, 1), (7, 1), (347, 1), (39608339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_347
    · exact prime_39608339
  · decide +kernel

theorem prime_963356615797 : Nat.Prime 963356615797 := by
  apply nodeValid_prime [2, 3, 23, 241, 14483081] ⟨963356615797, 5, [(2, 2), (3, 1), (23, 1), (241, 1), (14483081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_241
    · exact prime_14483081
  · decide +kernel

theorem prime_963356617121 : Nat.Prime 963356617121 := by
  apply nodeValid_prime [2, 5, 6020978857] ⟨963356617121, 3, [(2, 5), (5, 1), (6020978857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6020978857
  · decide +kernel

theorem prime_963356619347 : Nat.Prime 963356619347 := by
  apply nodeValid_prime [2, 11, 59, 26681, 27817] ⟨963356619347, 2, [(2, 1), (11, 1), (59, 1), (26681, 1), (27817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_26681
    · exact prime_27817
  · decide +kernel

theorem prime_964627908509 : Nat.Prime 964627908509 := by
  apply nodeValid_prime [2, 11, 21923361557] ⟨964627908509, 2, [(2, 2), (11, 1), (21923361557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_21923361557
  · decide +kernel

theorem prime_964627965809 : Nat.Prime 964627965809 := by
  apply nodeValid_prime [2, 13, 4637634451] ⟨964627965809, 3, [(2, 4), (13, 1), (4637634451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4637634451
  · decide +kernel

theorem prime_964627966007 : Nat.Prime 964627966007 := by
  apply nodeValid_prime [2, 41, 58027, 202729] ⟨964627966007, 5, [(2, 1), (41, 1), (58027, 1), (202729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_58027
    · exact prime_202729
  · decide +kernel

theorem prime_965900347981 : Nat.Prime 965900347981 := by
  apply nodeValid_prime [2, 3, 5, 19, 847281007] ⟨965900347981, 29, [(2, 2), (3, 1), (5, 1), (19, 1), (847281007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_847281007
  · decide +kernel

theorem prime_965900364997 : Nat.Prime 965900364997 := by
  apply nodeValid_prime [2, 3, 7, 229, 50213161] ⟨965900364997, 6, [(2, 2), (3, 1), (7, 1), (229, 1), (50213161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_229
    · exact prime_50213161
  · decide +kernel

theorem prime_965900367763 : Nat.Prime 965900367763 := by
  apply nodeValid_prime [2, 3, 11, 907, 16135451] ⟨965900367763, 2, [(2, 1), (3, 1), (11, 1), (907, 1), (16135451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_907
    · exact prime_16135451
  · decide +kernel

theorem prime_967173920827 : Nat.Prime 967173920827 := by
  apply nodeValid_prime [2, 3, 17, 37, 256272899] ⟨967173920827, 2, [(2, 1), (3, 1), (17, 1), (37, 1), (256272899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_256272899
  · decide +kernel

theorem prime_967173965039 : Nat.Prime 967173965039 := by
  apply nodeValid_prime [2, 67, 5393, 1338349] ⟨967173965039, 7, [(2, 1), (67, 1), (5393, 1), (1338349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_5393
    · exact prime_1338349
  · decide +kernel

theorem prime_967173965531 : Nat.Prime 967173965531 := by
  apply nodeValid_prime [2, 5, 5857, 16513129] ⟨967173965531, 2, [(2, 1), (5, 1), (5857, 1), (16513129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5857
    · exact prime_16513129
  · decide +kernel

theorem prime_968448615773 : Nat.Prime 968448615773 := by
  apply nodeValid_prime [2, 11, 433, 50831861] ⟨968448615773, 2, [(2, 2), (11, 1), (433, 1), (50831861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_433
    · exact prime_50831861
  · decide +kernel

theorem prime_968448616099 : Nat.Prime 968448616099 := by
  apply nodeValid_prime [2, 3, 42409, 3805987] ⟨968448616099, 2, [(2, 1), (3, 1), (42409, 1), (3805987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42409
    · exact prime_3805987
  · decide +kernel

theorem prime_968448627577 : Nat.Prime 968448627577 := by
  apply nodeValid_prime [2, 3, 17, 67, 1312133] ⟨968448627577, 13, [(2, 3), (3, 4), (17, 1), (67, 1), (1312133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
    · exact prime_1312133
  · decide +kernel

theorem prime_969724473281 : Nat.Prime 969724473281 := by
  apply nodeValid_prime [2, 5, 6553, 462443] ⟨969724473281, 3, [(2, 6), (5, 1), (6553, 1), (462443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6553
    · exact prime_462443
  · decide +kernel

theorem prime_969724477549 : Nat.Prime 969724477549 := by
  apply nodeValid_prime [2, 3, 43, 626437001] ⟨969724477549, 2, [(2, 2), (3, 2), (43, 1), (626437001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_626437001
  · decide +kernel

theorem prime_969724478071 : Nat.Prime 969724478071 := by
  apply nodeValid_prime [2, 3, 5, 3591572141] ⟨969724478071, 3, [(2, 1), (3, 3), (5, 1), (3591572141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3591572141
  · decide +kernel

theorem prime_971001455807 : Nat.Prime 971001455807 := by
  apply nodeValid_prime [2, 149, 479, 6802493] ⟨971001455807, 5, [(2, 1), (149, 1), (479, 1), (6802493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_479
    · exact prime_6802493
  · decide +kernel

theorem prime_971001458057 : Nat.Prime 971001458057 := by
  apply nodeValid_prime [2, 7, 233, 3491, 21317] ⟨971001458057, 3, [(2, 3), (7, 1), (233, 1), (3491, 1), (21317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_233
    · exact prime_3491
    · exact prime_21317
  · decide +kernel

theorem prime_971001458269 : Nat.Prime 971001458269 := by
  apply nodeValid_prime [2, 3, 1579, 51245591] ⟨971001458269, 6, [(2, 2), (3, 1), (1579, 1), (51245591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1579
    · exact prime_51245591
  · decide +kernel

theorem prime_972279571537 : Nat.Prime 972279571537 := by
  apply nodeValid_prime [2, 3, 7, 13, 74197159] ⟨972279571537, 20, [(2, 4), (3, 2), (7, 1), (13, 1), (74197159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_74197159
  · decide +kernel

theorem prime_972279578057 : Nat.Prime 972279578057 := by
  apply nodeValid_prime [2, 181, 11443, 58679] ⟨972279578057, 3, [(2, 3), (181, 1), (11443, 1), (58679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_11443
    · exact prime_58679
  · decide +kernel

theorem prime_972279578329 : Nat.Prime 972279578329 := by
  apply nodeValid_prime [2, 3, 71, 113, 829, 6091] ⟨972279578329, 13, [(2, 3), (3, 1), (71, 1), (113, 1), (829, 1), (6091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_113
    · exact prime_829
    · exact prime_6091
  · decide +kernel

theorem prime_973558834007 : Nat.Prime 973558834007 := by
  apply nodeValid_prime [2, 11, 24859, 1780147] ⟨973558834007, 5, [(2, 1), (11, 1), (24859, 1), (1780147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_24859
    · exact prime_1780147
  · decide +kernel

theorem prime_973558899629 : Nat.Prime 973558899629 := by
  apply nodeValid_prime [2, 7, 4751, 1045493] ⟨973558899629, 2, [(2, 2), (7, 2), (4751, 1), (1045493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4751
    · exact prime_1045493
  · decide +kernel

theorem prime_973558899869 : Nat.Prime 973558899869 := by
  apply nodeValid_prime [2, 243389724967] ⟨973558899869, 2, [(2, 2), (243389724967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_243389724967
  · decide +kernel

theorem prime_974839238029 : Nat.Prime 974839238029 := by
  apply nodeValid_prime [2, 3, 2213, 4078757] ⟨974839238029, 7, [(2, 2), (3, 3), (2213, 1), (4078757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2213
    · exact prime_4078757
  · decide +kernel

theorem prime_974839239401 : Nat.Prime 974839239401 := by
  apply nodeValid_prime [2, 5, 13, 2273, 164953] ⟨974839239401, 3, [(2, 3), (5, 2), (13, 1), (2273, 1), (164953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2273
    · exact prime_164953
  · decide +kernel

theorem prime_974839243067 : Nat.Prime 974839243067 := by
  apply nodeValid_prime [2, 13, 79, 474605279] ⟨974839243067, 2, [(2, 1), (13, 1), (79, 1), (474605279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_474605279
  · decide +kernel

theorem prime_976120751693 : Nat.Prime 976120751693 := by
  apply nodeValid_prime [2, 41, 3769, 1579187] ⟨976120751693, 2, [(2, 2), (41, 1), (3769, 1), (1579187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_3769
    · exact prime_1579187
  · decide +kernel

theorem prime_976120752137 : Nat.Prime 976120752137 := by
  apply nodeValid_prime [2, 163, 8389, 89231] ⟨976120752137, 3, [(2, 3), (163, 1), (8389, 1), (89231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_8389
    · exact prime_89231
  · decide +kernel

theorem prime_976120777223 : Nat.Prime 976120777223 := by
  apply nodeValid_prime [2, 157637, 3096103] ⟨976120777223, 5, [(2, 1), (157637, 1), (3096103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157637
    · exact prime_3096103
  · decide +kernel

theorem prime_977403441689 : Nat.Prime 977403441689 := by
  apply nodeValid_prime [2, 64793, 1885627] ⟨977403441689, 3, [(2, 3), (64793, 1), (1885627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_64793
    · exact prime_1885627
  · decide +kernel

theorem prime_977403443651 : Nat.Prime 977403443651 := by
  apply nodeValid_prime [2, 5, 47, 415916359] ⟨977403443651, 2, [(2, 1), (5, 2), (47, 1), (415916359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_415916359
  · decide +kernel

theorem prime_977403454163 : Nat.Prime 977403454163 := by
  apply nodeValid_prime [2, 2833, 172503257] ⟨977403454163, 2, [(2, 1), (2833, 1), (172503257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2833
    · exact prime_172503257
  · decide +kernel

theorem prime_978687264193 : Nat.Prime 978687264193 := by
  apply nodeValid_prime [2, 3, 11, 829, 558979] ⟨978687264193, 13, [(2, 6), (3, 1), (11, 1), (829, 1), (558979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_829
    · exact prime_558979
  · decide +kernel

theorem prime_978687264391 : Nat.Prime 978687264391 := by
  apply nodeValid_prime [2, 3, 5, 11, 6547, 452989] ⟨978687264391, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (6547, 1), (452989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_6547
    · exact prime_452989
  · decide +kernel

theorem prime_978687273691 : Nat.Prime 978687273691 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 81761677] ⟨978687273691, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (81761677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_81761677
  · decide +kernel

end Sude.Lucas.Generated
