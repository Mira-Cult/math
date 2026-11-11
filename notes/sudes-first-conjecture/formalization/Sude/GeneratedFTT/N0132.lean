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
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0129

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_12613 : Nat.Prime 12613 := by
  apply nodeValid_prime [2, 3, 1051] ⟨12613, 2, [(2, 2), (3, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1051
  · decide +kernel

theorem prime_15061 : Nat.Prime 15061 := by
  apply nodeValid_prime [2, 3, 5, 251] ⟨15061, 2, [(2, 2), (3, 1), (5, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_251
  · decide +kernel

theorem prime_18013 : Nat.Prime 18013 := by
  apply nodeValid_prime [2, 3, 19, 79] ⟨18013, 2, [(2, 2), (3, 1), (19, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_79
  · decide +kernel

theorem prime_18617 : Nat.Prime 18617 := by
  apply nodeValid_prime [2, 13, 179] ⟨18617, 3, [(2, 3), (13, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_179
  · decide +kernel

theorem prime_21997 : Nat.Prime 21997 := by
  apply nodeValid_prime [2, 3, 13, 47] ⟨21997, 7, [(2, 2), (3, 2), (13, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_25841 : Nat.Prime 25841 := by
  apply nodeValid_prime [2, 5, 17, 19] ⟨25841, 3, [(2, 4), (5, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_27701 : Nat.Prime 27701 := by
  apply nodeValid_prime [2, 5, 277] ⟨27701, 2, [(2, 2), (5, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_277
  · decide +kernel

theorem prime_30869 : Nat.Prime 30869 := by
  apply nodeValid_prime [2, 7717] ⟨30869, 2, [(2, 2), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7717
  · decide +kernel

theorem prime_39979 : Nat.Prime 39979 := by
  apply nodeValid_prime [2, 3, 2221] ⟨39979, 3, [(2, 1), (3, 2), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2221
  · decide +kernel

theorem prime_40471 : Nat.Prime 40471 := by
  apply nodeValid_prime [2, 3, 5, 19, 71] ⟨40471, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_44053 : Nat.Prime 44053 := by
  apply nodeValid_prime [2, 3, 3671] ⟨44053, 2, [(2, 2), (3, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3671
  · decide +kernel

theorem prime_51593 : Nat.Prime 51593 := by
  apply nodeValid_prime [2, 6449] ⟨51593, 3, [(2, 3), (6449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6449
  · decide +kernel

theorem prime_58613 : Nat.Prime 58613 := by
  apply nodeValid_prime [2, 14653] ⟨58613, 2, [(2, 2), (14653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14653
  · decide +kernel

theorem prime_62213 : Nat.Prime 62213 := by
  apply nodeValid_prime [2, 103, 151] ⟨62213, 2, [(2, 2), (103, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_151
  · decide +kernel

theorem prime_62819 : Nat.Prime 62819 := by
  apply nodeValid_prime [2, 7, 641] ⟨62819, 2, [(2, 1), (7, 2), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_641
  · decide +kernel

theorem prime_74471 : Nat.Prime 74471 := by
  apply nodeValid_prime [2, 5, 11, 677] ⟨74471, 11, [(2, 1), (5, 1), (11, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_677
  · decide +kernel

theorem prime_75211 : Nat.Prime 75211 := by
  apply nodeValid_prime [2, 3, 5, 23, 109] ⟨75211, 2, [(2, 1), (3, 1), (5, 1), (23, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_109
  · decide +kernel

theorem prime_76943 : Nat.Prime 76943 := by
  apply nodeValid_prime [2, 17, 31, 73] ⟨76943, 10, [(2, 1), (17, 1), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_79697 : Nat.Prime 79697 := by
  apply nodeValid_prime [2, 17, 293] ⟨79697, 3, [(2, 4), (17, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_293
  · decide +kernel

theorem prime_79699 : Nat.Prime 79699 := by
  apply nodeValid_prime [2, 3, 37, 359] ⟨79699, 2, [(2, 1), (3, 1), (37, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_359
  · decide +kernel

theorem prime_82507 : Nat.Prime 82507 := by
  apply nodeValid_prime [2, 3, 13751] ⟨82507, 2, [(2, 1), (3, 1), (13751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13751
  · decide +kernel

theorem prime_86711 : Nat.Prime 86711 := by
  apply nodeValid_prime [2, 5, 13, 23, 29] ⟨86711, 7, [(2, 1), (5, 1), (13, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_94201 : Nat.Prime 94201 := by
  apply nodeValid_prime [2, 3, 5, 157] ⟨94201, 11, [(2, 3), (3, 1), (5, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
  · decide +kernel

theorem prime_150881 : Nat.Prime 150881 := by
  apply nodeValid_prime [2, 5, 23, 41] ⟨150881, 6, [(2, 5), (5, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_155047 : Nat.Prime 155047 := by
  apply nodeValid_prime [2, 3, 25841] ⟨155047, 5, [(2, 1), (3, 1), (25841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25841
  · decide +kernel

theorem prime_185131 : Nat.Prime 185131 := by
  apply nodeValid_prime [2, 3, 5, 11, 17] ⟨185131, 7, [(2, 1), (3, 2), (5, 1), (11, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_198409 : Nat.Prime 198409 := by
  apply nodeValid_prime [2, 3, 7, 1181] ⟨198409, 11, [(2, 3), (3, 1), (7, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1181
  · decide +kernel

theorem prime_198859 : Nat.Prime 198859 := by
  apply nodeValid_prime [2, 3, 11, 23, 131] ⟨198859, 2, [(2, 1), (3, 1), (11, 1), (23, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_131
  · decide +kernel

theorem prime_289607 : Nat.Prime 289607 := by
  apply nodeValid_prime [2, 89, 1627] ⟨289607, 5, [(2, 1), (89, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1627
  · decide +kernel

theorem prime_304033 : Nat.Prime 304033 := by
  apply nodeValid_prime [2, 3, 3167] ⟨304033, 5, [(2, 5), (3, 1), (3167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3167
  · decide +kernel

theorem prime_355783 : Nat.Prime 355783 := by
  apply nodeValid_prime [2, 3, 7, 43, 197] ⟨355783, 3, [(2, 1), (3, 1), (7, 1), (43, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_197
  · decide +kernel

theorem prime_366607 : Nat.Prime 366607 := by
  apply nodeValid_prime [2, 3, 31, 73] ⟨366607, 3, [(2, 1), (3, 4), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_368447 : Nat.Prime 368447 := by
  apply nodeValid_prime [2, 13, 37, 383] ⟨368447, 5, [(2, 1), (13, 1), (37, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_383
  · decide +kernel

theorem prime_375251 : Nat.Prime 375251 := by
  apply nodeValid_prime [2, 5, 19, 79] ⟨375251, 2, [(2, 1), (5, 3), (19, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_79
  · decide +kernel

theorem prime_388253 : Nat.Prime 388253 := by
  apply nodeValid_prime [2, 29, 3347] ⟨388253, 2, [(2, 2), (29, 1), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3347
  · decide +kernel

theorem prime_434683 : Nat.Prime 434683 := by
  apply nodeValid_prime [2, 3, 19, 31, 41] ⟨434683, 2, [(2, 1), (3, 2), (19, 1), (31, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_41
  · decide +kernel

theorem prime_450529 : Nat.Prime 450529 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨450529, 23, [(2, 5), (3, 1), (13, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_463363 : Nat.Prime 463363 := by
  apply nodeValid_prime [2, 3, 29, 2663] ⟨463363, 3, [(2, 1), (3, 1), (29, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2663
  · decide +kernel

theorem prime_502001 : Nat.Prime 502001 := by
  apply nodeValid_prime [2, 5, 251] ⟨502001, 3, [(2, 4), (5, 3), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
  · decide +kernel

theorem prime_565207 : Nat.Prime 565207 := by
  apply nodeValid_prime [2, 3, 94201] ⟨565207, 3, [(2, 1), (3, 1), (94201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_94201
  · decide +kernel

theorem prime_619117 : Nat.Prime 619117 := by
  apply nodeValid_prime [2, 3, 51593] ⟨619117, 2, [(2, 2), (3, 1), (51593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51593
  · decide +kernel

theorem prime_740687 : Nat.Prime 740687 := by
  apply nodeValid_prime [2, 59, 6277] ⟨740687, 5, [(2, 1), (59, 1), (6277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_6277
  · decide +kernel

theorem prime_745033 : Nat.Prime 745033 := by
  apply nodeValid_prime [2, 3, 37, 839] ⟨745033, 10, [(2, 3), (3, 1), (37, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_839
  · decide +kernel

theorem prime_777479 : Nat.Prime 777479 := by
  apply nodeValid_prime [2, 13, 17, 1759] ⟨777479, 29, [(2, 1), (13, 1), (17, 1), (1759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_1759
  · decide +kernel

theorem prime_835859 : Nat.Prime 835859 := by
  apply nodeValid_prime [2, 181, 2309] ⟨835859, 2, [(2, 1), (181, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_2309
  · decide +kernel

theorem prime_885107 : Nat.Prime 885107 := by
  apply nodeValid_prime [2, 311, 1423] ⟨885107, 2, [(2, 1), (311, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_1423
  · decide +kernel

theorem prime_956909 : Nat.Prime 956909 := by
  apply nodeValid_prime [2, 31, 7717] ⟨956909, 2, [(2, 2), (31, 1), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_7717
  · decide +kernel

theorem prime_1199371 : Nat.Prime 1199371 := by
  apply nodeValid_prime [2, 3, 5, 39979] ⟨1199371, 14, [(2, 1), (3, 1), (5, 1), (39979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_39979
  · decide +kernel

theorem prime_1802117 : Nat.Prime 1802117 := by
  apply nodeValid_prime [2, 450529] ⟨1802117, 2, [(2, 2), (450529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_450529
  · decide +kernel

theorem prime_1840537 : Nat.Prime 1840537 := by
  apply nodeValid_prime [2, 3, 8521] ⟨1840537, 5, [(2, 3), (3, 3), (8521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8521
  · decide +kernel

theorem prime_1913819 : Nat.Prime 1913819 := by
  apply nodeValid_prime [2, 956909] ⟨1913819, 2, [(2, 1), (956909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_956909
  · decide +kernel

theorem prime_1917961 : Nat.Prime 1917961 := by
  apply nodeValid_prime [2, 3, 5, 11, 1453] ⟨1917961, 7, [(2, 3), (3, 1), (5, 1), (11, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1453
  · decide +kernel

theorem prime_1984091 : Nat.Prime 1984091 := by
  apply nodeValid_prime [2, 5, 198409] ⟨1984091, 2, [(2, 1), (5, 1), (198409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_198409
  · decide +kernel

theorem prime_2251507 : Nat.Prime 2251507 := by
  apply nodeValid_prime [2, 3, 375251] ⟨2251507, 2, [(2, 1), (3, 1), (375251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_375251
  · decide +kernel

theorem prime_2256367 : Nat.Prime 2256367 := by
  apply nodeValid_prime [2, 3, 7, 31, 1733] ⟨2256367, 3, [(2, 1), (3, 1), (7, 1), (31, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_1733
  · decide +kernel

theorem prime_2431441 : Nat.Prime 2431441 := by
  apply nodeValid_prime [2, 3, 5, 11, 307] ⟨2431441, 23, [(2, 4), (3, 2), (5, 1), (11, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_307
  · decide +kernel

theorem prime_2755981 : Nat.Prime 2755981 := by
  apply nodeValid_prime [2, 3, 5, 61, 251] ⟨2755981, 6, [(2, 2), (3, 2), (5, 1), (61, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_251
  · decide +kernel

theorem prime_4831441 : Nat.Prime 4831441 := by
  apply nodeValid_prime [2, 3, 5, 41, 491] ⟨4831441, 14, [(2, 4), (3, 1), (5, 1), (41, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_491
  · decide +kernel

theorem prime_4864529 : Nat.Prime 4864529 := by
  apply nodeValid_prime [2, 304033] ⟨4864529, 3, [(2, 4), (304033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_304033
  · decide +kernel

theorem prime_5264771 : Nat.Prime 5264771 := by
  apply nodeValid_prime [2, 5, 7, 75211] ⟨5264771, 2, [(2, 1), (5, 1), (7, 1), (75211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_75211
  · decide +kernel

theorem prime_5467513 : Nat.Prime 5467513 := by
  apply nodeValid_prime [2, 3, 409, 557] ⟨5467513, 11, [(2, 3), (3, 1), (409, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_409
    · exact prime_557
  · decide +kernel

theorem prime_5883439 : Nat.Prime 5883439 := by
  apply nodeValid_prime [2, 3, 11, 97, 919] ⟨5883439, 3, [(2, 1), (3, 1), (11, 1), (97, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_919
  · decide +kernel

theorem prime_6022759 : Nat.Prime 6022759 := by
  apply nodeValid_prime [2, 3, 7, 193, 743] ⟨6022759, 6, [(2, 1), (3, 1), (7, 1), (193, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_193
    · exact prime_743
  · decide +kernel

theorem prime_6201289 : Nat.Prime 6201289 := by
  apply nodeValid_prime [2, 3, 43, 2003] ⟨6201289, 7, [(2, 3), (3, 2), (43, 1), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_2003
  · decide +kernel

theorem prime_7631677 : Nat.Prime 7631677 := by
  apply nodeValid_prime [2, 3, 13, 23, 709] ⟨7631677, 5, [(2, 2), (3, 2), (13, 1), (23, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_709
  · decide +kernel

theorem prime_8352079 : Nat.Prime 8352079 := by
  apply nodeValid_prime [2, 3, 7, 198859] ⟨8352079, 3, [(2, 1), (3, 1), (7, 1), (198859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_198859
  · decide +kernel

theorem prime_8373917 : Nat.Prime 8373917 := by
  apply nodeValid_prime [2, 139, 15061] ⟨8373917, 2, [(2, 2), (139, 1), (15061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_15061
  · decide +kernel

theorem prime_8541359 : Nat.Prime 8541359 := by
  apply nodeValid_prime [2, 7, 433, 1409] ⟨8541359, 7, [(2, 1), (7, 1), (433, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_433
    · exact prime_1409
  · decide +kernel

theorem prime_10176679 : Nat.Prime 10176679 := by
  apply nodeValid_prime [2, 3, 62819] ⟨10176679, 6, [(2, 1), (3, 4), (62819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62819
  · decide +kernel

theorem prime_11185177 : Nat.Prime 11185177 := by
  apply nodeValid_prime [2, 3, 23, 881] ⟨11185177, 5, [(2, 3), (3, 1), (23, 2), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_881
  · decide +kernel

theorem prime_11523067 : Nat.Prime 11523067 := by
  apply nodeValid_prime [2, 3, 367, 5233] ⟨11523067, 2, [(2, 1), (3, 1), (367, 1), (5233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_5233
  · decide +kernel

theorem prime_15607981 : Nat.Prime 15607981 := by
  apply nodeValid_prime [2, 3, 5, 86711] ⟨15607981, 2, [(2, 2), (3, 2), (5, 1), (86711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_86711
  · decide +kernel

theorem prime_17032039 : Nat.Prime 17032039 := by
  apply nodeValid_prime [2, 3, 113, 25121] ⟨17032039, 15, [(2, 1), (3, 1), (113, 1), (25121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_25121
  · decide +kernel

theorem prime_17082719 : Nat.Prime 17082719 := by
  apply nodeValid_prime [2, 8541359] ⟨17082719, 11, [(2, 1), (8541359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8541359
  · decide +kernel

theorem prime_17776489 : Nat.Prime 17776489 := by
  apply nodeValid_prime [2, 3, 740687] ⟨17776489, 14, [(2, 3), (3, 1), (740687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_740687
  · decide +kernel

theorem prime_18907129 : Nat.Prime 18907129 := by
  apply nodeValid_prime [2, 3, 17, 19, 271] ⟨18907129, 7, [(2, 3), (3, 3), (17, 1), (19, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_271
  · decide +kernel

theorem prime_21110737 : Nat.Prime 21110737 := by
  apply nodeValid_prime [2, 3, 17, 41, 631] ⟨21110737, 10, [(2, 4), (3, 1), (17, 1), (41, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_631
  · decide +kernel

theorem prime_21625993 : Nat.Prime 21625993 := by
  apply nodeValid_prime [2, 3, 67, 4483] ⟨21625993, 19, [(2, 3), (3, 2), (67, 1), (4483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_4483
  · decide +kernel

theorem prime_21870053 : Nat.Prime 21870053 := by
  apply nodeValid_prime [2, 5467513] ⟨21870053, 2, [(2, 2), (5467513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5467513
  · decide +kernel

theorem prime_40706717 : Nat.Prime 40706717 := by
  apply nodeValid_prime [2, 10176679] ⟨40706717, 2, [(2, 2), (10176679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10176679
  · decide +kernel

theorem prime_57058769 : Nat.Prime 57058769 := by
  apply nodeValid_prime [2, 13, 23, 11927] ⟨57058769, 3, [(2, 4), (13, 1), (23, 1), (11927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_11927
  · decide +kernel

theorem prime_61554401 : Nat.Prime 61554401 := by
  apply nodeValid_prime [2, 5, 76943] ⟨61554401, 3, [(2, 5), (5, 2), (76943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_76943
  · decide +kernel

theorem prime_61724987 : Nat.Prime 61724987 := by
  apply nodeValid_prime [2, 71, 434683] ⟨61724987, 2, [(2, 1), (71, 1), (434683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_434683
  · decide +kernel

theorem prime_70280141 : Nat.Prime 70280141 := by
  apply nodeValid_prime [2, 5, 7, 502001] ⟨70280141, 2, [(2, 2), (5, 1), (7, 1), (502001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_502001
  · decide +kernel

theorem prime_74213561 : Nat.Prime 74213561 := by
  apply nodeValid_prime [2, 5, 103, 18013] ⟨74213561, 3, [(2, 3), (5, 1), (103, 1), (18013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_18013
  · decide +kernel

theorem prime_74713921 : Nat.Prime 74713921 := by
  apply nodeValid_prime [2, 3, 5, 223, 349] ⟨74713921, 11, [(2, 6), (3, 1), (5, 1), (223, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
    · exact prime_349
  · decide +kernel

theorem prime_115230671 : Nat.Prime 115230671 := by
  apply nodeValid_prime [2, 5, 11523067] ⟨115230671, 23, [(2, 1), (5, 1), (11523067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11523067
  · decide +kernel

theorem prime_116232931 : Nat.Prime 116232931 := by
  apply nodeValid_prime [2, 3, 5, 11, 113, 1039] ⟨116232931, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (113, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_113
    · exact prime_1039
  · decide +kernel

theorem prime_130824217 : Nat.Prime 130824217 := by
  apply nodeValid_prime [2, 3, 31, 58613] ⟨130824217, 7, [(2, 3), (3, 2), (31, 1), (58613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_58613
  · decide +kernel

theorem prime_141374171 : Nat.Prime 141374171 := by
  apply nodeValid_prime [2, 5, 7, 683, 2957] ⟨141374171, 2, [(2, 1), (5, 1), (7, 1), (683, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_683
    · exact prime_2957
  · decide +kernel

theorem prime_143024767 : Nat.Prime 143024767 := by
  apply nodeValid_prime [2, 3, 67, 355783] ⟨143024767, 3, [(2, 1), (3, 1), (67, 1), (355783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_355783
  · decide +kernel

theorem prime_145638797 : Nat.Prime 145638797 := by
  apply nodeValid_prime [2, 17, 73, 29339] ⟨145638797, 2, [(2, 2), (17, 1), (73, 1), (29339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_73
    · exact prime_29339
  · decide +kernel

theorem prime_151063271 : Nat.Prime 151063271 := by
  apply nodeValid_prime [2, 5, 41, 368447] ⟨151063271, 7, [(2, 1), (5, 1), (41, 1), (368447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_368447
  · decide +kernel

theorem prime_189944407 : Nat.Prime 189944407 := by
  apply nodeValid_prime [2, 3, 19, 185131] ⟨189944407, 3, [(2, 1), (3, 3), (19, 1), (185131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_185131
  · decide +kernel

theorem prime_282748343 : Nat.Prime 282748343 := by
  apply nodeValid_prime [2, 141374171] ⟨282748343, 5, [(2, 1), (141374171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_141374171
  · decide +kernel

theorem prime_391082759 : Nat.Prime 391082759 := by
  apply nodeValid_prime [2, 11, 17776489] ⟨391082759, 7, [(2, 1), (11, 1), (17776489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17776489
  · decide +kernel

theorem prime_392385529 : Nat.Prime 392385529 := by
  apply nodeValid_prime [2, 3, 1571, 3469] ⟨392385529, 11, [(2, 3), (3, 2), (1571, 1), (3469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1571
    · exact prime_3469
  · decide +kernel

theorem prime_493006469 : Nat.Prime 493006469 := by
  apply nodeValid_prime [2, 41, 839, 3583] ⟨493006469, 2, [(2, 2), (41, 1), (839, 1), (3583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_839
    · exact prime_3583
  · decide +kernel

theorem prime_847006177 : Nat.Prime 847006177 := by
  apply nodeValid_prime [2, 3, 47, 131, 1433] ⟨847006177, 5, [(2, 5), (3, 1), (47, 1), (131, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_131
    · exact prime_1433
  · decide +kernel

theorem prime_2414103067 : Nat.Prime 2414103067 := by
  apply nodeValid_prime [2, 3, 149, 181, 4973] ⟨2414103067, 3, [(2, 1), (3, 2), (149, 1), (181, 1), (4973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_181
    · exact prime_4973
  · decide +kernel

theorem prime_3245938379 : Nat.Prime 3245938379 := by
  apply nodeValid_prime [2, 19, 233, 366607] ⟨3245938379, 2, [(2, 1), (19, 1), (233, 1), (366607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_233
    · exact prime_366607
  · decide +kernel

theorem prime_4878086371 : Nat.Prime 4878086371 := by
  apply nodeValid_prime [2, 3, 5, 59, 2755981] ⟨4878086371, 2, [(2, 1), (3, 1), (5, 1), (59, 1), (2755981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_2755981
  · decide +kernel

theorem prime_4910811637 : Nat.Prime 4910811637 := by
  apply nodeValid_prime [2, 3, 181, 887, 2549] ⟨4910811637, 2, [(2, 2), (3, 1), (181, 1), (887, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_887
    · exact prime_2549
  · decide +kernel

theorem prime_5167080431 : Nat.Prime 5167080431 := by
  apply nodeValid_prime [2, 5, 229, 2256367] ⟨5167080431, 7, [(2, 1), (5, 1), (229, 1), (2256367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_2256367
  · decide +kernel

theorem prime_7849453021 : Nat.Prime 7849453021 := by
  apply nodeValid_prime [2, 3, 5, 130824217] ⟨7849453021, 2, [(2, 2), (3, 1), (5, 1), (130824217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_130824217
  · decide +kernel

theorem prime_10909478617 : Nat.Prime 10909478617 := by
  apply nodeValid_prime [2, 3, 379, 1199371] ⟨10909478617, 5, [(2, 3), (3, 1), (379, 1), (1199371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_1199371
  · decide +kernel

theorem prime_11152765571 : Nat.Prime 11152765571 := by
  apply nodeValid_prime [2, 5, 3851, 289607] ⟨11152765571, 2, [(2, 1), (5, 1), (3851, 1), (289607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3851
    · exact prime_289607
  · decide +kernel

theorem prime_18216343291 : Nat.Prime 18216343291 := by
  apply nodeValid_prime [2, 3, 5, 19, 401, 79697] ⟨18216343291, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (401, 1), (79697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_401
    · exact prime_79697
  · decide +kernel

theorem prime_18734245823 : Nat.Prime 18734245823 := by
  apply nodeValid_prime [2, 19, 493006469] ⟨18734245823, 5, [(2, 1), (19, 1), (493006469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_493006469
  · decide +kernel

theorem prime_19549336019 : Nat.Prime 19549336019 := by
  apply nodeValid_prime [2, 19, 3191, 161221] ⟨19549336019, 2, [(2, 1), (19, 1), (3191, 1), (161221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3191
    · exact prime_161221
  · decide +kernel

theorem prime_20595566569 : Nat.Prime 20595566569 := by
  apply nodeValid_prime [2, 3, 23, 47, 109, 7283] ⟨20595566569, 11, [(2, 3), (3, 1), (23, 1), (47, 1), (109, 1), (7283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47
    · exact prime_109
    · exact prime_7283
  · decide +kernel

theorem prime_48859734881 : Nat.Prime 48859734881 := by
  apply nodeValid_prime [2, 5, 11, 31, 71, 12613] ⟨48859734881, 3, [(2, 5), (5, 1), (11, 1), (31, 1), (71, 1), (12613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_71
    · exact prime_12613
  · decide +kernel

theorem prime_56549668601 : Nat.Prime 56549668601 := by
  apply nodeValid_prime [2, 5, 282748343] ⟨56549668601, 3, [(2, 3), (5, 2), (282748343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_282748343
  · decide +kernel

theorem prime_88394609467 : Nat.Prime 88394609467 := by
  apply nodeValid_prime [2, 3, 4910811637] ⟨88394609467, 2, [(2, 1), (3, 2), (4910811637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4910811637
  · decide +kernel

theorem prime_102977832241 : Nat.Prime 102977832241 := by
  apply nodeValid_prime [2, 3, 5, 143024767] ⟨102977832241, 13, [(2, 4), (3, 2), (5, 1), (143024767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_143024767
  · decide +kernel

theorem prime_141137326367 : Nat.Prime 141137326367 := by
  apply nodeValid_prime [2, 53, 59, 2417, 9337] ⟨141137326367, 5, [(2, 1), (53, 1), (59, 1), (2417, 1), (9337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_59
    · exact prime_2417
    · exact prime_9337
  · decide +kernel

theorem prime_203726813879 : Nat.Prime 203726813879 := by
  apply nodeValid_prime [2, 7, 1301, 11185177] ⟨203726813879, 7, [(2, 1), (7, 1), (1301, 1), (11185177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1301
    · exact prime_11185177
  · decide +kernel

theorem prime_386726416567 : Nat.Prime 386726416567 := by
  apply nodeValid_prime [2, 3, 7, 487, 18907129] ⟨386726416567, 3, [(2, 1), (3, 1), (7, 1), (487, 1), (18907129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_487
    · exact prime_18907129
  · decide +kernel

theorem prime_1017154367681 : Nat.Prime 1017154367681 := by
  apply nodeValid_prime [2, 5, 11, 157, 1840537] ⟨1017154367681, 17, [(2, 6), (5, 1), (11, 1), (157, 1), (1840537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_157
    · exact prime_1840537
  · decide +kernel

theorem prime_1031270418943 : Nat.Prime 1031270418943 := by
  apply nodeValid_prime [2, 3, 89, 397, 4864529] ⟨1031270418943, 3, [(2, 1), (3, 1), (89, 1), (397, 1), (4864529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_397
    · exact prime_4864529
  · decide +kernel

theorem prime_3064793625791 : Nat.Prime 3064793625791 := by
  apply nodeValid_prime [2, 5, 13, 383, 61554401] ⟨3064793625791, 7, [(2, 1), (5, 1), (13, 1), (383, 1), (61554401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_383
    · exact prime_61554401
  · decide +kernel

theorem prime_3067019100419 : Nat.Prime 3067019100419 := by
  apply nodeValid_prime [2, 7, 13, 20161, 835859] ⟨3067019100419, 2, [(2, 1), (7, 1), (13, 1), (20161, 1), (835859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_20161
    · exact prime_835859
  · decide +kernel

theorem prime_3080395513493 : Nat.Prime 3080395513493 := by
  apply nodeValid_prime [2, 11, 29, 2414103067] ⟨3080395513493, 5, [(2, 2), (11, 1), (29, 1), (2414103067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_2414103067
  · decide +kernel

theorem prime_6102926206087 : Nat.Prime 6102926206087 := by
  apply nodeValid_prime [2, 3, 1017154367681] ⟨6102926206087, 3, [(2, 1), (3, 1), (1017154367681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1017154367681
  · decide +kernel

theorem prime_6102926275087 : Nat.Prime 6102926275087 := by
  apply nodeValid_prime [2, 3, 2917, 116232931] ⟨6102926275087, 5, [(2, 1), (3, 2), (2917, 1), (116232931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2917
    · exact prime_116232931
  · decide +kernel

theorem prime_6102926275141 : Nat.Prime 6102926275141 := by
  apply nodeValid_prime [2, 3, 5, 19, 241, 277, 26731] ⟨6102926275141, 6, [(2, 2), (3, 2), (5, 1), (19, 1), (241, 1), (277, 1), (26731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_241
    · exact prime_277
    · exact prime_26731
  · decide +kernel

theorem prime_6107364136493 : Nat.Prime 6107364136493 := by
  apply nodeValid_prime [2, 313, 4878086371] ⟨6107364136493, 2, [(2, 2), (313, 1), (4878086371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_4878086371
  · decide +kernel

theorem prime_6107364138299 : Nat.Prime 6107364138299 := by
  apply nodeValid_prime [2, 163, 18734245823] ⟨6107364138299, 2, [(2, 1), (163, 1), (18734245823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_18734245823
  · decide +kernel

theorem prime_6107364208909 : Nat.Prime 6107364208909 := by
  apply nodeValid_prime [2, 3, 56549668601] ⟨6107364208909, 2, [(2, 2), (3, 3), (56549668601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56549668601
  · decide +kernel

theorem prime_6111804399731 : Nat.Prime 6111804399731 := by
  apply nodeValid_prime [2, 5, 67, 1471, 6201289] ⟨6111804399731, 2, [(2, 1), (5, 1), (67, 1), (1471, 1), (6201289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_1471
    · exact prime_6201289
  · decide +kernel

theorem prime_6111804415943 : Nat.Prime 6111804415943 := by
  apply nodeValid_prime [2, 195791, 15607981] ⟨6111804415943, 5, [(2, 1), (195791, 1), (15607981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_195791
    · exact prime_15607981
  · decide +kernel

theorem prime_6111804416371 : Nat.Prime 6111804416371 := by
  apply nodeValid_prime [2, 3, 5, 203726813879] ⟨6111804416371, 2, [(2, 1), (3, 1), (5, 1), (203726813879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_203726813879
  · decide +kernel

theorem prime_6116246779367 : Nat.Prime 6116246779367 := by
  apply nodeValid_prime [2, 109, 5807, 4831441] ⟨6116246779367, 5, [(2, 1), (109, 1), (5807, 1), (4831441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_5807
    · exact prime_4831441
  · decide +kernel

theorem prime_6116246917873 : Nat.Prime 6116246917873 := by
  apply nodeValid_prime [2, 3, 7, 13, 1801, 777479] ⟨6116246917873, 5, [(2, 4), (3, 1), (7, 1), (13, 1), (1801, 1), (777479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1801
    · exact prime_777479
  · decide +kernel

theorem prime_6116246918813 : Nat.Prime 6116246918813 := by
  apply nodeValid_prime [2, 10499, 145638797] ⟨6116246918813, 2, [(2, 2), (10499, 1), (145638797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10499
    · exact prime_145638797
  · decide +kernel

theorem prime_6120691345777 : Nat.Prime 6120691345777 := by
  apply nodeValid_prime [2, 3, 7, 18216343291] ⟨6120691345777, 5, [(2, 4), (3, 1), (7, 1), (18216343291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18216343291
  · decide +kernel

theorem prime_6120691369433 : Nat.Prime 6120691369433 := by
  apply nodeValid_prime [2, 41, 191, 499, 195791] ⟨6120691369433, 3, [(2, 3), (41, 1), (191, 1), (499, 1), (195791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_191
    · exact prime_499
    · exact prime_195791
  · decide +kernel

theorem prime_6120691370723 : Nat.Prime 6120691370723 := by
  apply nodeValid_prime [2, 17, 521, 6269, 55117] ⟨6120691370723, 2, [(2, 1), (17, 1), (521, 1), (6269, 1), (55117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_521
    · exact prime_6269
    · exact prime_55117
  · decide +kernel

theorem prime_6125138107691 : Nat.Prime 6125138107691 := by
  apply nodeValid_prime [2, 5, 7, 223, 392385529] ⟨6125138107691, 6, [(2, 1), (5, 1), (7, 1), (223, 1), (392385529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_223
    · exact prime_392385529
  · decide +kernel

theorem prime_6125138170139 : Nat.Prime 6125138170139 := by
  apply nodeValid_prime [2, 13, 30869, 7631677] ⟨6125138170139, 2, [(2, 1), (13, 1), (30869, 1), (7631677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_30869
    · exact prime_7631677
  · decide +kernel

theorem prime_6125138171459 : Nat.Prime 6125138171459 := by
  apply nodeValid_prime [2, 41, 191, 391082759] ⟨6125138171459, 2, [(2, 1), (41, 1), (191, 1), (391082759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_191
    · exact prime_391082759
  · decide +kernel

theorem prime_6129587066143 : Nat.Prime 6129587066143 := by
  apply nodeValid_prime [2, 3, 79, 757, 17082719] ⟨6129587066143, 3, [(2, 1), (3, 1), (79, 1), (757, 1), (17082719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_757
    · exact prime_17082719
  · decide +kernel

theorem prime_6129587251583 : Nat.Prime 6129587251583 := by
  apply nodeValid_prime [2, 3064793625791] ⟨6129587251583, 5, [(2, 1), (3064793625791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3064793625791
  · decide +kernel

theorem prime_6129587251751 : Nat.Prime 6129587251751 := by
  apply nodeValid_prime [2, 5, 27701, 885107] ⟨6129587251751, 13, [(2, 1), (5, 3), (27701, 1), (885107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_27701
    · exact prime_885107
  · decide +kernel

theorem prime_6134038200767 : Nat.Prime 6134038200767 := by
  apply nodeValid_prime [2, 7, 74471, 5883439] ⟨6134038200767, 7, [(2, 1), (7, 1), (74471, 1), (5883439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_74471
    · exact prime_5883439
  · decide +kernel

theorem prime_6134038200839 : Nat.Prime 6134038200839 := by
  apply nodeValid_prime [2, 3067019100419] ⟨6134038200839, 29, [(2, 1), (3067019100419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3067019100419
  · decide +kernel

theorem prime_6134038213889 : Nat.Prime 6134038213889 := by
  apply nodeValid_prime [2, 13, 31, 1917961] ⟨6134038213889, 3, [(2, 8), (13, 1), (31, 2), (1917961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_1917961
  · decide +kernel

theorem prime_6138491509967 : Nat.Prime 6138491509967 := by
  apply nodeValid_prime [2, 157, 19549336019] ⟨6138491509967, 5, [(2, 1), (157, 1), (19549336019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_19549336019
  · decide +kernel

theorem prime_6138491510167 : Nat.Prime 6138491510167 := by
  apply nodeValid_prime [2, 3, 41, 613, 40706717] ⟨6138491510167, 5, [(2, 1), (3, 1), (41, 1), (613, 1), (40706717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_613
    · exact prime_40706717
  · decide +kernel

theorem prime_6138491552029 : Nat.Prime 6138491552029 := by
  apply nodeValid_prime [2, 3, 11, 5167080431] ⟨6138491552029, 2, [(2, 2), (3, 3), (11, 1), (5167080431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5167080431
  · decide +kernel

theorem prime_6142947070541 : Nat.Prime 6142947070541 := by
  apply nodeValid_prime [2, 5, 7, 769, 57058769] ⟨6142947070541, 3, [(2, 2), (5, 1), (7, 1), (769, 1), (57058769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_769
    · exact prime_57058769
  · decide +kernel

theorem prime_6142947071011 : Nat.Prime 6142947071011 := by
  apply nodeValid_prime [2, 3, 5, 1777, 115230671] ⟨6142947071011, 3, [(2, 1), (3, 1), (5, 1), (1777, 1), (115230671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1777
    · exact prime_115230671
  · decide +kernel

theorem prime_6142947071161 : Nat.Prime 6142947071161 := by
  apply nodeValid_prime [2, 3, 5, 53, 12119, 79699] ⟨6142947071161, 14, [(2, 3), (3, 1), (5, 1), (53, 1), (12119, 1), (79699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_12119
    · exact prime_79699
  · decide +kernel

theorem prime_6147404770181 : Nat.Prime 6147404770181 := by
  apply nodeValid_prime [2, 5, 61, 233, 21625993] ⟨6147404770181, 2, [(2, 2), (5, 1), (61, 1), (233, 1), (21625993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_233
    · exact prime_21625993
  · decide +kernel

theorem prime_6147404803201 : Nat.Prime 6147404803201 := by
  apply nodeValid_prime [2, 3, 5, 43, 677, 21997] ⟨6147404803201, 22, [(2, 7), (3, 1), (5, 2), (43, 1), (677, 1), (21997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_677
    · exact prime_21997
  · decide +kernel

theorem prime_6147404803367 : Nat.Prime 6147404803367 := by
  apply nodeValid_prime [2, 67, 23971, 1913819] ⟨6147404803367, 5, [(2, 1), (67, 1), (23971, 1), (1913819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_23971
    · exact prime_1913819
  · decide +kernel

theorem prime_6151864628383 : Nat.Prime 6151864628383 := by
  apply nodeValid_prime [2, 3, 11, 11131, 8373917] ⟨6151864628383, 3, [(2, 1), (3, 1), (11, 1), (11131, 1), (8373917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_11131
    · exact prime_8373917
  · decide +kernel

theorem prime_6151864628647 : Nat.Prime 6151864628647 := by
  apply nodeValid_prime [2, 3, 11, 66797, 155047] ⟨6151864628647, 11, [(2, 1), (3, 3), (11, 1), (66797, 1), (155047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_66797
    · exact prime_155047
  · decide +kernel

theorem prime_6151864662637 : Nat.Prime 6151864662637 := by
  apply nodeValid_prime [2, 3, 7, 11, 181, 1193, 2803] ⟨6151864662637, 5, [(2, 2), (3, 1), (7, 1), (11, 2), (181, 1), (1193, 1), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_181
    · exact prime_1193
    · exact prime_2803
  · decide +kernel

theorem prime_6156326595007 : Nat.Prime 6156326595007 := by
  apply nodeValid_prime [2, 3, 7, 48859734881] ⟨6156326595007, 5, [(2, 1), (3, 2), (7, 1), (48859734881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_48859734881
  · decide +kernel

theorem prime_6156326595193 : Nat.Prime 6156326595193 := by
  apply nodeValid_prime [2, 3, 23, 11152765571] ⟨6156326595193, 5, [(2, 3), (3, 1), (23, 1), (11152765571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_11152765571
  · decide +kernel

theorem prime_6156326753407 : Nat.Prime 6156326753407 := by
  apply nodeValid_prime [2, 3, 1847, 61724987] ⟨6156326753407, 3, [(2, 1), (3, 3), (1847, 1), (61724987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1847
    · exact prime_61724987
  · decide +kernel

theorem prime_6160791026987 : Nat.Prime 6160791026987 := by
  apply nodeValid_prime [2, 3080395513493] ⟨6160791026987, 2, [(2, 1), (3080395513493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3080395513493
  · decide +kernel

theorem prime_6160791042661 : Nat.Prime 6160791042661 := by
  apply nodeValid_prime [2, 3, 5, 19, 107, 109, 463363] ⟨6160791042661, 7, [(2, 2), (3, 1), (5, 1), (19, 1), (107, 1), (109, 1), (463363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_107
    · exact prime_109
    · exact prime_463363
  · decide +kernel

theorem prime_6160791043343 : Nat.Prime 6160791043343 := by
  apply nodeValid_prime [2, 13, 73, 3245938379] ⟨6160791043343, 10, [(2, 1), (13, 1), (73, 1), (3245938379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_3245938379
  · decide +kernel

theorem prime_6165257477083 : Nat.Prime 6165257477083 := by
  apply nodeValid_prime [2, 3, 11, 150881, 619117] ⟨6165257477083, 2, [(2, 1), (3, 1), (11, 1), (150881, 1), (619117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_150881
    · exact prime_619117
  · decide +kernel

theorem prime_6165257477221 : Nat.Prime 6165257477221 := by
  apply nodeValid_prime [2, 3, 5, 2011, 17032039] ⟨6165257477221, 6, [(2, 2), (3, 2), (5, 1), (2011, 1), (17032039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2011
    · exact prime_17032039
  · decide +kernel

theorem prime_6165257477941 : Nat.Prime 6165257477941 := by
  apply nodeValid_prime [2, 3, 5, 11, 47, 6022759] ⟨6165257477941, 2, [(2, 2), (3, 2), (5, 1), (11, 2), (47, 1), (6022759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_47
    · exact prime_6022759
  · decide +kernel

theorem prime_6169726114183 : Nat.Prime 6169726114183 := by
  apply nodeValid_prime [2, 3, 2269, 151063271] ⟨6169726114183, 5, [(2, 1), (3, 2), (2269, 1), (151063271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2269
    · exact prime_151063271
  · decide +kernel

theorem prime_6169726168339 : Nat.Prime 6169726168339 := by
  apply nodeValid_prime [2, 3, 13763, 74713921] ⟨6169726168339, 2, [(2, 1), (3, 1), (13763, 1), (74713921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13763
    · exact prime_74713921
  · decide +kernel

theorem prime_6169726169557 : Nat.Prime 6169726169557 := by
  apply nodeValid_prime [2, 3, 137, 179, 337, 62213] ⟨6169726169557, 5, [(2, 2), (3, 1), (137, 1), (179, 1), (337, 1), (62213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_179
    · exact prime_337
    · exact prime_62213
  · decide +kernel

theorem prime_6174196934431 : Nat.Prime 6174196934431 := by
  apply nodeValid_prime [2, 3, 5, 7, 197, 1523, 13999] ⟨6174196934431, 3, [(2, 1), (3, 1), (5, 1), (7, 2), (197, 1), (1523, 1), (13999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_197
    · exact prime_1523
    · exact prime_13999
  · decide +kernel

theorem prime_6174197011361 : Nat.Prime 6174197011361 := by
  apply nodeValid_prime [2, 5, 7, 19, 23, 1802117] ⟨6174197011361, 3, [(2, 5), (5, 1), (7, 2), (19, 1), (23, 1), (1802117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_1802117
  · decide +kernel

theorem prime_6174197012999 : Nat.Prime 6174197012999 := by
  apply nodeValid_prime [2, 7, 211, 397, 5264771] ⟨6174197012999, 7, [(2, 1), (7, 1), (211, 1), (397, 1), (5264771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
    · exact prime_397
    · exact prime_5264771
  · decide +kernel

theorem prime_6178669934461 : Nat.Prime 6178669934461 := by
  apply nodeValid_prime [2, 3, 5, 102977832241] ⟨6178669934461, 2, [(2, 2), (3, 1), (5, 1), (102977832241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_102977832241
  · decide +kernel

theorem prime_6178669970659 : Nat.Prime 6178669970659 := by
  apply nodeValid_prime [2, 3, 191, 9539, 565207] ⟨6178669970659, 2, [(2, 1), (3, 1), (191, 1), (9539, 1), (565207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_9539
    · exact prime_565207
  · decide +kernel

theorem prime_6178669970701 : Nat.Prime 6178669970701 := by
  apply nodeValid_prime [2, 3, 5, 20595566569] ⟨6178669970701, 6, [(2, 2), (3, 1), (5, 2), (20595566569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20595566569
  · decide +kernel

theorem prime_6183145092101 : Nat.Prime 6183145092101 := by
  apply nodeValid_prime [2, 5, 73, 847006177] ⟨6183145092101, 2, [(2, 2), (5, 2), (73, 1), (847006177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_847006177
  · decide +kernel

theorem prime_6183145092149 : Nat.Prime 6183145092149 := by
  apply nodeValid_prime [2, 67, 173, 179, 745033] ⟨6183145092149, 2, [(2, 2), (67, 1), (173, 1), (179, 1), (745033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_173
    · exact prime_179
    · exact prime_745033
  · decide +kernel

theorem prime_6183145124267 : Nat.Prime 6183145124267 := by
  apply nodeValid_prime [2, 11, 71, 181, 21870053] ⟨6183145124267, 2, [(2, 1), (11, 1), (71, 1), (181, 1), (21870053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_181
    · exact prime_21870053
  · decide +kernel

theorem prime_6187622513659 : Nat.Prime 6187622513659 := by
  apply nodeValid_prime [2, 3, 1031270418943] ⟨6187622513659, 2, [(2, 1), (3, 1), (1031270418943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1031270418943
  · decide +kernel

theorem prime_6187622662691 : Nat.Prime 6187622662691 := by
  apply nodeValid_prime [2, 5, 7, 88394609467] ⟨6187622662691, 2, [(2, 1), (5, 1), (7, 1), (88394609467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_88394609467
  · decide +kernel

theorem prime_6187622665073 : Nat.Prime 6187622665073 := by
  apply nodeValid_prime [2, 386726416567] ⟨6187622665073, 3, [(2, 4), (386726416567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_386726416567
  · decide +kernel

theorem prime_6192102102947 : Nat.Prime 6192102102947 := by
  apply nodeValid_prime [2, 44053, 70280141] ⟨6192102102947, 2, [(2, 1), (44053, 1), (70280141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_44053
    · exact prime_70280141
  · decide +kernel

theorem prime_6192102165881 : Nat.Prime 6192102165881 := by
  apply nodeValid_prime [2, 5, 63667, 2431441] ⟨6192102165881, 3, [(2, 3), (5, 1), (63667, 1), (2431441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_63667
    · exact prime_2431441
  · decide +kernel

theorem prime_6192102165913 : Nat.Prime 6192102165913 := by
  apply nodeValid_prime [2, 3, 13, 59, 151, 82507] ⟨6192102165913, 5, [(2, 3), (3, 4), (13, 1), (59, 1), (151, 1), (82507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_151
    · exact prime_82507
  · decide +kernel

theorem prime_6196583853527 : Nat.Prime 6196583853527 := by
  apply nodeValid_prime [2, 11, 29, 21817, 40471] ⟨6196583853527, 5, [(2, 1), (11, 2), (29, 1), (21817, 1), (40471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_21817
    · exact prime_40471
  · decide +kernel

theorem prime_6196583854457 : Nat.Prime 6196583854457 := by
  apply nodeValid_prime [2, 71, 10909478617] ⟨6196583854457, 3, [(2, 3), (71, 1), (10909478617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_10909478617
  · decide +kernel

theorem prime_6196583883011 : Nat.Prime 6196583883011 := by
  apply nodeValid_prime [2, 5, 1069, 1493, 388253] ⟨6196583883011, 2, [(2, 1), (5, 1), (1069, 1), (1493, 1), (388253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1069
    · exact prime_1493
    · exact prime_388253
  · decide +kernel

theorem prime_6201067870183 : Nat.Prime 6201067870183 := by
  apply nodeValid_prime [2, 3, 17, 29, 251, 8352079] ⟨6201067870183, 3, [(2, 1), (3, 1), (17, 1), (29, 1), (251, 1), (8352079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_251
    · exact prime_8352079
  · decide +kernel

theorem prime_6201067886381 : Nat.Prime 6201067886381 := by
  apply nodeValid_prime [2, 5, 19, 773, 21110737] ⟨6201067886381, 3, [(2, 2), (5, 1), (19, 1), (773, 1), (21110737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_773
    · exact prime_21110737
  · decide +kernel

theorem prime_6201067886591 : Nat.Prime 6201067886591 := by
  apply nodeValid_prime [2, 5, 79, 7849453021] ⟨6201067886591, 14, [(2, 1), (5, 1), (79, 1), (7849453021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_7849453021
  · decide +kernel

theorem prime_6205554060247 : Nat.Prime 6205554060247 := by
  apply nodeValid_prime [2, 3, 19, 8059, 2251507] ⟨6205554060247, 3, [(2, 1), (3, 2), (19, 1), (8059, 1), (2251507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_8059
    · exact prime_2251507
  · decide +kernel

theorem prime_6205554120697 : Nat.Prime 6205554120697 := by
  apply nodeValid_prime [2, 3, 7, 18617, 1984091] ⟨6205554120697, 5, [(2, 3), (3, 1), (7, 1), (18617, 1), (1984091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18617
    · exact prime_1984091
  · decide +kernel

theorem prime_6205554121771 : Nat.Prime 6205554121771 := by
  apply nodeValid_prime [2, 3, 5, 743, 1777, 52223] ⟨6205554121771, 2, [(2, 1), (3, 2), (5, 1), (743, 1), (1777, 1), (52223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_743
    · exact prime_1777
    · exact prime_52223
  · decide +kernel

theorem prime_6210042357359 : Nat.Prime 6210042357359 := by
  apply nodeValid_prime [2, 7, 43, 139, 74213561] ⟨6210042357359, 7, [(2, 1), (7, 1), (43, 1), (139, 1), (74213561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_139
    · exact prime_74213561
  · decide +kernel

theorem prime_6210042360149 : Nat.Prime 6210042360149 := by
  apply nodeValid_prime [2, 11, 141137326367] ⟨6210042360149, 2, [(2, 2), (11, 1), (141137326367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_141137326367
  · decide +kernel

theorem prime_6210042442459 : Nat.Prime 6210042442459 := by
  apply nodeValid_prime [2, 3, 5449, 189944407] ⟨6210042442459, 2, [(2, 1), (3, 1), (5449, 1), (189944407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5449
    · exact prime_189944407
  · decide +kernel

end Sude.Lucas.Generated
