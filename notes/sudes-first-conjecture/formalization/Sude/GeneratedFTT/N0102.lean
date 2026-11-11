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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0090

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5237 : Nat.Prime 5237 := by
  apply nodeValid_prime [2, 7, 11, 17] ⟨5237, 3, [(2, 2), (7, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_6359 : Nat.Prime 6359 := by
  apply nodeValid_prime [2, 11, 17] ⟨6359, 13, [(2, 1), (11, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_12379 : Nat.Prime 12379 := by
  apply nodeValid_prime [2, 3, 2063] ⟨12379, 2, [(2, 1), (3, 1), (2063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2063
  · decide +kernel

theorem prime_18439 : Nat.Prime 18439 := by
  apply nodeValid_prime [2, 3, 7, 439] ⟨18439, 3, [(2, 1), (3, 1), (7, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_439
  · decide +kernel

theorem prime_28463 : Nat.Prime 28463 := by
  apply nodeValid_prime [2, 7, 19, 107] ⟨28463, 5, [(2, 1), (7, 1), (19, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_107
  · decide +kernel

theorem prime_31327 : Nat.Prime 31327 := by
  apply nodeValid_prime [2, 3, 23, 227] ⟨31327, 6, [(2, 1), (3, 1), (23, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_227
  · decide +kernel

theorem prime_34537 : Nat.Prime 34537 := by
  apply nodeValid_prime [2, 3, 1439] ⟨34537, 5, [(2, 3), (3, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1439
  · decide +kernel

theorem prime_36653 : Nat.Prime 36653 := by
  apply nodeValid_prime [2, 7, 11, 17] ⟨36653, 2, [(2, 2), (7, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_41141 : Nat.Prime 41141 := by
  apply nodeValid_prime [2, 5, 11, 17] ⟨41141, 2, [(2, 2), (5, 1), (11, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_47591 : Nat.Prime 47591 := by
  apply nodeValid_prime [2, 5, 4759] ⟨47591, 11, [(2, 1), (5, 1), (4759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4759
  · decide +kernel

theorem prime_56209 : Nat.Prime 56209 := by
  apply nodeValid_prime [2, 3, 1171] ⟨56209, 7, [(2, 4), (3, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1171
  · decide +kernel

theorem prime_60169 : Nat.Prime 60169 := by
  apply nodeValid_prime [2, 3, 23, 109] ⟨60169, 11, [(2, 3), (3, 1), (23, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_109
  · decide +kernel

theorem prime_62539 : Nat.Prime 62539 := by
  apply nodeValid_prime [2, 3, 7, 1489] ⟨62539, 2, [(2, 1), (3, 1), (7, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1489
  · decide +kernel

theorem prime_74831 : Nat.Prime 74831 := by
  apply nodeValid_prime [2, 5, 7, 1069] ⟨74831, 7, [(2, 1), (5, 1), (7, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1069
  · decide +kernel

theorem prime_77711 : Nat.Prime 77711 := by
  apply nodeValid_prime [2, 5, 19, 409] ⟨77711, 14, [(2, 1), (5, 1), (19, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_409
  · decide +kernel

theorem prime_83399 : Nat.Prime 83399 := by
  apply nodeValid_prime [2, 7, 23, 37] ⟨83399, 7, [(2, 1), (7, 2), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_143999 : Nat.Prime 143999 := by
  apply nodeValid_prime [2, 71999] ⟨143999, 7, [(2, 1), (71999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71999
  · decide +kernel

theorem prime_152617 : Nat.Prime 152617 := by
  apply nodeValid_prime [2, 3, 6359] ⟨152617, 7, [(2, 3), (3, 1), (6359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6359
  · decide +kernel

theorem prime_155371 : Nat.Prime 155371 := by
  apply nodeValid_prime [2, 3, 5, 5179] ⟨155371, 2, [(2, 1), (3, 1), (5, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5179
  · decide +kernel

theorem prime_161503 : Nat.Prime 161503 := by
  apply nodeValid_prime [2, 3, 11, 2447] ⟨161503, 3, [(2, 1), (3, 1), (11, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2447
  · decide +kernel

theorem prime_166799 : Nat.Prime 166799 := by
  apply nodeValid_prime [2, 83399] ⟨166799, 17, [(2, 1), (83399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_83399
  · decide +kernel

theorem prime_222823 : Nat.Prime 222823 := by
  apply nodeValid_prime [2, 3, 12379] ⟨222823, 3, [(2, 1), (3, 2), (12379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12379
  · decide +kernel

theorem prime_240677 : Nat.Prime 240677 := by
  apply nodeValid_prime [2, 60169] ⟨240677, 2, [(2, 2), (60169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60169
  · decide +kernel

theorem prime_244843 : Nat.Prime 244843 := by
  apply nodeValid_prime [2, 3, 13, 43, 73] ⟨244843, 3, [(2, 1), (3, 1), (13, 1), (43, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_73
  · decide +kernel

theorem prime_281291 : Nat.Prime 281291 := by
  apply nodeValid_prime [2, 5, 23, 1223] ⟨281291, 2, [(2, 1), (5, 1), (23, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1223
  · decide +kernel

theorem prime_288539 : Nat.Prime 288539 := by
  apply nodeValid_prime [2, 89, 1621] ⟨288539, 2, [(2, 1), (89, 1), (1621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1621
  · decide +kernel

theorem prime_318503 : Nat.Prime 318503 := by
  apply nodeValid_prime [2, 163, 977] ⟨318503, 5, [(2, 1), (163, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_977
  · decide +kernel

theorem prime_339637 : Nat.Prime 339637 := by
  apply nodeValid_prime [2, 3, 11, 31, 83] ⟨339637, 2, [(2, 2), (3, 1), (11, 1), (31, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_83
  · decide +kernel

theorem prime_405529 : Nat.Prime 405529 := by
  apply nodeValid_prime [2, 3, 61, 277] ⟨405529, 13, [(2, 3), (3, 1), (61, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_277
  · decide +kernel

theorem prime_539267 : Nat.Prime 539267 := by
  apply nodeValid_prime [2, 7, 13, 2963] ⟨539267, 2, [(2, 1), (7, 1), (13, 1), (2963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_2963
  · decide +kernel

theorem prime_553171 : Nat.Prime 553171 := by
  apply nodeValid_prime [2, 3, 5, 18439] ⟨553171, 11, [(2, 1), (3, 1), (5, 1), (18439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18439
  · decide +kernel

theorem prime_574727 : Nat.Prime 574727 := by
  apply nodeValid_prime [2, 67, 4289] ⟨574727, 5, [(2, 1), (67, 1), (4289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_4289
  · decide +kernel

theorem prime_660593 : Nat.Prime 660593 := by
  apply nodeValid_prime [2, 19, 41, 53] ⟨660593, 3, [(2, 4), (19, 1), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_678179 : Nat.Prime 678179 := by
  apply nodeValid_prime [2, 23, 641] ⟨678179, 2, [(2, 1), (23, 2), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_641
  · decide +kernel

theorem prime_687521 : Nat.Prime 687521 := by
  apply nodeValid_prime [2, 5, 4297] ⟨687521, 3, [(2, 5), (5, 1), (4297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4297
  · decide +kernel

theorem prime_700643 : Nat.Prime 700643 := by
  apply nodeValid_prime [2, 43, 8147] ⟨700643, 2, [(2, 1), (43, 1), (8147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_8147
  · decide +kernel

theorem prime_737921 : Nat.Prime 737921 := by
  apply nodeValid_prime [2, 5, 1153] ⟨737921, 6, [(2, 7), (5, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1153
  · decide +kernel

theorem prime_790961 : Nat.Prime 790961 := by
  apply nodeValid_prime [2, 5, 9887] ⟨790961, 3, [(2, 4), (5, 1), (9887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9887
  · decide +kernel

theorem prime_879673 : Nat.Prime 879673 := by
  apply nodeValid_prime [2, 3, 36653] ⟨879673, 10, [(2, 3), (3, 1), (36653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36653
  · decide +kernel

theorem prime_979373 : Nat.Prime 979373 := by
  apply nodeValid_prime [2, 244843] ⟨979373, 2, [(2, 2), (244843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_244843
  · decide +kernel

theorem prime_1058821 : Nat.Prime 1058821 := by
  apply nodeValid_prime [2, 3, 5, 7, 2521] ⟨1058821, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (2521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2521
  · decide +kernel

theorem prime_1190201 : Nat.Prime 1190201 := by
  apply nodeValid_prime [2, 5, 11, 541] ⟨1190201, 6, [(2, 3), (5, 2), (11, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_541
  · decide +kernel

theorem prime_1235137 : Nat.Prime 1235137 := by
  apply nodeValid_prime [2, 3, 7, 919] ⟨1235137, 5, [(2, 6), (3, 1), (7, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_919
  · decide +kernel

theorem prime_1289731 : Nat.Prime 1289731 := by
  apply nodeValid_prime [2, 3, 5, 13, 3307] ⟨1289731, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_3307
  · decide +kernel

theorem prime_1401131 : Nat.Prime 1401131 := by
  apply nodeValid_prime [2, 5, 167, 839] ⟨1401131, 2, [(2, 1), (5, 1), (167, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_839
  · decide +kernel

theorem prime_1416161 : Nat.Prime 1416161 := by
  apply nodeValid_prime [2, 5, 53, 167] ⟨1416161, 3, [(2, 5), (5, 1), (53, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_167
  · decide +kernel

theorem prime_1475843 : Nat.Prime 1475843 := by
  apply nodeValid_prime [2, 737921] ⟨1475843, 2, [(2, 1), (737921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_737921
  · decide +kernel

theorem prime_1479271 : Nat.Prime 1479271 := by
  apply nodeValid_prime [2, 3, 5, 13, 3793] ⟨1479271, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_3793
  · decide +kernel

theorem prime_1670891 : Nat.Prime 1670891 := by
  apply nodeValid_prime [2, 5, 13, 12853] ⟨1670891, 14, [(2, 1), (5, 1), (13, 1), (12853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_12853
  · decide +kernel

theorem prime_1685549 : Nat.Prime 1685549 := by
  apply nodeValid_prime [2, 283, 1489] ⟨1685549, 2, [(2, 2), (283, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_1489
  · decide +kernel

theorem prime_2673523 : Nat.Prime 2673523 := by
  apply nodeValid_prime [2, 3, 17, 8737] ⟨2673523, 2, [(2, 1), (3, 2), (17, 1), (8737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8737
  · decide +kernel

theorem prime_3518693 : Nat.Prime 3518693 := by
  apply nodeValid_prime [2, 879673] ⟨3518693, 2, [(2, 2), (879673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_879673
  · decide +kernel

theorem prime_3791371 : Nat.Prime 3791371 := by
  apply nodeValid_prime [2, 3, 5, 11, 11489] ⟨3791371, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (11489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_11489
  · decide +kernel

theorem prime_3899243 : Nat.Prime 3899243 := by
  apply nodeValid_prime [2, 31, 61, 1031] ⟨3899243, 2, [(2, 1), (31, 1), (61, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_61
    · exact prime_1031
  · decide +kernel

theorem prime_4223563 : Nat.Prime 4223563 := by
  apply nodeValid_prime [2, 3, 7, 227, 443] ⟨4223563, 2, [(2, 1), (3, 1), (7, 1), (227, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_227
    · exact prime_443
  · decide +kernel

theorem prime_4289977 : Nat.Prime 4289977 := by
  apply nodeValid_prime [2, 3, 19861] ⟨4289977, 5, [(2, 3), (3, 3), (19861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19861
  · decide +kernel

theorem prime_5134079 : Nat.Prime 5134079 := by
  apply nodeValid_prime [2, 179, 14341] ⟨5134079, 11, [(2, 1), (179, 1), (14341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_14341
  · decide +kernel

theorem prime_6370061 : Nat.Prime 6370061 := by
  apply nodeValid_prime [2, 5, 318503] ⟨6370061, 2, [(2, 2), (5, 1), (318503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_318503
  · decide +kernel

theorem prime_6843559 : Nat.Prime 6843559 := by
  apply nodeValid_prime [2, 3, 23, 101, 491] ⟨6843559, 3, [(2, 1), (3, 1), (23, 1), (101, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_101
    · exact prime_491
  · decide +kernel

theorem prime_10901831 : Nat.Prime 10901831 := by
  apply nodeValid_prime [2, 5, 97, 11239] ⟨10901831, 13, [(2, 1), (5, 1), (97, 1), (11239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_11239
  · decide +kernel

theorem prime_16276297 : Nat.Prime 16276297 := by
  apply nodeValid_prime [2, 3, 678179] ⟨16276297, 5, [(2, 3), (3, 1), (678179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_678179
  · decide +kernel

theorem prime_16849867 : Nat.Prime 16849867 := by
  apply nodeValid_prime [2, 3, 11, 53, 4817] ⟨16849867, 2, [(2, 1), (3, 1), (11, 1), (53, 1), (4817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_4817
  · decide +kernel

theorem prime_19086091 : Nat.Prime 19086091 := by
  apply nodeValid_prime [2, 3, 5, 23, 139, 199] ⟨19086091, 2, [(2, 1), (3, 1), (5, 1), (23, 1), (139, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_139
    · exact prime_199
  · decide +kernel

theorem prime_22055491 : Nat.Prime 22055491 := by
  apply nodeValid_prime [2, 3, 5, 73, 373] ⟨22055491, 12, [(2, 1), (3, 4), (5, 1), (73, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_373
  · decide +kernel

theorem prime_26358193 : Nat.Prime 26358193 := by
  apply nodeValid_prime [2, 3, 7, 79, 331] ⟨26358193, 5, [(2, 4), (3, 2), (7, 1), (79, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_331
  · decide +kernel

theorem prime_30185339 : Nat.Prime 30185339 := by
  apply nodeValid_prime [2, 19, 23, 34537] ⟨30185339, 2, [(2, 1), (19, 1), (23, 1), (34537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_34537
  · decide +kernel

theorem prime_35706031 : Nat.Prime 35706031 := by
  apply nodeValid_prime [2, 3, 5, 1190201] ⟨35706031, 3, [(2, 1), (3, 1), (5, 1), (1190201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1190201
  · decide +kernel

theorem prime_38382499 : Nat.Prime 38382499 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 181] ⟨38382499, 3, [(2, 1), (3, 4), (7, 1), (11, 1), (17, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_181
  · decide +kernel

theorem prime_47883431 : Nat.Prime 47883431 := by
  apply nodeValid_prime [2, 5, 7, 157, 4357] ⟨47883431, 17, [(2, 1), (5, 1), (7, 1), (157, 1), (4357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_157
    · exact prime_4357
  · decide +kernel

theorem prime_55702861 : Nat.Prime 55702861 := by
  apply nodeValid_prime [2, 3, 5, 139, 6679] ⟨55702861, 6, [(2, 2), (3, 1), (5, 1), (139, 1), (6679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_6679
  · decide +kernel

theorem prime_60370679 : Nat.Prime 60370679 := by
  apply nodeValid_prime [2, 30185339] ⟨60370679, 13, [(2, 1), (30185339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30185339
  · decide +kernel

theorem prime_69656843 : Nat.Prime 69656843 := by
  apply nodeValid_prime [2, 1979, 17599] ⟨69656843, 2, [(2, 1), (1979, 1), (17599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1979
    · exact prime_17599
  · decide +kernel

theorem prime_72289909 : Nat.Prime 72289909 := by
  apply nodeValid_prime [2, 3, 19, 11743] ⟨72289909, 10, [(2, 2), (3, 4), (19, 1), (11743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11743
  · decide +kernel

theorem prime_72652199 : Nat.Prime 72652199 := by
  apply nodeValid_prime [2, 43, 191, 4423] ⟨72652199, 7, [(2, 1), (43, 1), (191, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_191
    · exact prime_4423
  · decide +kernel

theorem prime_81459181 : Nat.Prime 81459181 := by
  apply nodeValid_prime [2, 3, 5, 11, 41141] ⟨81459181, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (41141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41141
  · decide +kernel

theorem prime_92413423 : Nat.Prime 92413423 := by
  apply nodeValid_prime [2, 3, 5134079] ⟨92413423, 3, [(2, 1), (3, 2), (5134079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5134079
  · decide +kernel

theorem prime_105432773 : Nat.Prime 105432773 := by
  apply nodeValid_prime [2, 26358193] ⟨105432773, 2, [(2, 2), (26358193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26358193
  · decide +kernel

theorem prime_143948521 : Nat.Prime 143948521 := by
  apply nodeValid_prime [2, 3, 5, 17, 43, 547] ⟨143948521, 7, [(2, 3), (3, 2), (5, 1), (17, 1), (43, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_43
    · exact prime_547
  · decide +kernel

theorem prime_196047913 : Nat.Prime 196047913 := by
  apply nodeValid_prime [2, 3, 421, 19403] ⟨196047913, 5, [(2, 3), (3, 1), (421, 1), (19403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
    · exact prime_19403
  · decide +kernel

theorem prime_203453359 : Nat.Prime 203453359 := by
  apply nodeValid_prime [2, 3, 59, 574727] ⟨203453359, 3, [(2, 1), (3, 1), (59, 1), (574727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_574727
  · decide +kernel

theorem prime_210464557 : Nat.Prime 210464557 := by
  apply nodeValid_prime [2, 3, 17, 197, 5237] ⟨210464557, 5, [(2, 2), (3, 1), (17, 1), (197, 1), (5237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_197
    · exact prime_5237
  · decide +kernel

theorem prime_257398621 : Nat.Prime 257398621 := by
  apply nodeValid_prime [2, 3, 5, 4289977] ⟨257398621, 14, [(2, 2), (3, 1), (5, 1), (4289977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4289977
  · decide +kernel

theorem prime_267542563 : Nat.Prime 267542563 := by
  apply nodeValid_prime [2, 3, 7, 6370061] ⟨267542563, 2, [(2, 1), (3, 1), (7, 1), (6370061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6370061
  · decide +kernel

theorem prime_397387139 : Nat.Prime 397387139 := by
  apply nodeValid_prime [2, 17, 687521] ⟨397387139, 2, [(2, 1), (17, 2), (687521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_687521
  · decide +kernel

theorem prime_505468937 : Nat.Prime 505468937 := by
  apply nodeValid_prime [2, 7, 61, 73, 2027] ⟨505468937, 3, [(2, 3), (7, 1), (61, 1), (73, 1), (2027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_73
    · exact prime_2027
  · decide +kernel

theorem prime_679971251 : Nat.Prime 679971251 := by
  apply nodeValid_prime [2, 5, 7, 77711] ⟨679971251, 2, [(2, 1), (5, 4), (7, 1), (77711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_77711
  · decide +kernel

theorem prime_742188409 : Nat.Prime 742188409 := by
  apply nodeValid_prime [2, 3, 13, 1427, 1667] ⟨742188409, 11, [(2, 3), (3, 1), (13, 1), (1427, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1427
    · exact prime_1667
  · decide +kernel

theorem prime_835254817 : Nat.Prime 835254817 := by
  apply nodeValid_prime [2, 3, 11, 790961] ⟨835254817, 7, [(2, 5), (3, 1), (11, 1), (790961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_790961
  · decide +kernel

theorem prime_863227087 : Nat.Prime 863227087 := by
  apply nodeValid_prime [2, 3, 401, 499, 719] ⟨863227087, 5, [(2, 1), (3, 1), (401, 1), (499, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_499
    · exact prime_719
  · decide +kernel

theorem prime_883227677 : Nat.Prime 883227677 := by
  apply nodeValid_prime [2, 131, 1685549] ⟨883227677, 2, [(2, 2), (131, 1), (1685549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_1685549
  · decide +kernel

theorem prime_1032246181 : Nat.Prime 1032246181 := by
  apply nodeValid_prime [2, 3, 5, 7, 227, 401] ⟨1032246181, 2, [(2, 2), (3, 4), (5, 1), (7, 1), (227, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_227
    · exact prime_401
  · decide +kernel

theorem prime_1183245337 : Nat.Prime 1183245337 := by
  apply nodeValid_prime [2, 3, 7, 13, 25799] ⟨1183245337, 10, [(2, 3), (3, 2), (7, 2), (13, 1), (25799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_25799
  · decide +kernel

theorem prime_2792639881 : Nat.Prime 2792639881 := by
  apply nodeValid_prime [2, 3, 5, 163, 47591] ⟨2792639881, 13, [(2, 3), (3, 2), (5, 1), (163, 1), (47591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_163
    · exact prime_47591
  · decide +kernel

theorem prime_3994875809 : Nat.Prime 3994875809 := by
  apply nodeValid_prime [2, 7, 11, 607, 2671] ⟨3994875809, 13, [(2, 5), (7, 1), (11, 1), (607, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_607
    · exact prime_2671
  · decide +kernel

theorem prime_6313936711 : Nat.Prime 6313936711 := by
  apply nodeValid_prime [2, 3, 5, 210464557] ⟨6313936711, 6, [(2, 1), (3, 1), (5, 1), (210464557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_210464557
  · decide +kernel

theorem prime_7233635191 : Nat.Prime 7233635191 := by
  apply nodeValid_prime [2, 3, 5, 163, 1479271] ⟨7233635191, 6, [(2, 1), (3, 1), (5, 1), (163, 1), (1479271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_163
    · exact prime_1479271
  · decide +kernel

theorem prime_8257478657 : Nat.Prime 8257478657 := by
  apply nodeValid_prime [2, 7, 143999] ⟨8257478657, 3, [(2, 13), (7, 1), (143999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_143999
  · decide +kernel

theorem prime_8894118407 : Nat.Prime 8894118407 := by
  apply nodeValid_prime [2, 233, 19086091] ⟨8894118407, 5, [(2, 1), (233, 1), (19086091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_19086091
  · decide +kernel

theorem prime_14954445251 : Nat.Prime 14954445251 := by
  apply nodeValid_prime [2, 5, 17, 3518693] ⟨14954445251, 7, [(2, 1), (5, 3), (17, 1), (3518693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_3518693
  · decide +kernel

theorem prime_18138943013 : Nat.Prime 18138943013 := by
  apply nodeValid_prime [2, 43, 6217, 16963] ⟨18138943013, 2, [(2, 2), (43, 1), (6217, 1), (16963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_6217
    · exact prime_16963
  · decide +kernel

theorem prime_18352252423 : Nat.Prime 18352252423 := by
  apply nodeValid_prime [2, 3, 7, 1021, 142657] ⟨18352252423, 5, [(2, 1), (3, 2), (7, 1), (1021, 1), (142657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1021
    · exact prime_142657
  · decide +kernel

theorem prime_19441160839 : Nat.Prime 19441160839 := by
  apply nodeValid_prime [2, 3, 11, 4133, 7919] ⟨19441160839, 6, [(2, 1), (3, 3), (11, 1), (4133, 1), (7919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4133
    · exact prime_7919
  · decide +kernel

theorem prime_19958899481 : Nat.Prime 19958899481 := by
  apply nodeValid_prime [2, 5, 13, 38382499] ⟨19958899481, 3, [(2, 3), (5, 1), (13, 1), (38382499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_38382499
  · decide +kernel

theorem prime_23843228341 : Nat.Prime 23843228341 := by
  apply nodeValid_prime [2, 3, 5, 397387139] ⟨23843228341, 2, [(2, 2), (3, 1), (5, 1), (397387139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_397387139
  · decide +kernel

theorem prime_33976617973 : Nat.Prime 33976617973 := by
  apply nodeValid_prime [2, 3, 11, 257398621] ⟨33976617973, 2, [(2, 2), (3, 1), (11, 1), (257398621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_257398621
  · decide +kernel

theorem prime_42396207437 : Nat.Prime 42396207437 := by
  apply nodeValid_prime [2, 11, 2837, 339637] ⟨42396207437, 2, [(2, 2), (11, 1), (2837, 1), (339637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2837
    · exact prime_339637
  · decide +kernel

theorem prime_93635385247 : Nat.Prime 93635385247 := by
  apply nodeValid_prime [2, 3, 13, 17, 53, 127, 269] ⟨93635385247, 3, [(2, 1), (3, 2), (13, 2), (17, 1), (53, 1), (127, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_53
    · exact prime_127
    · exact prime_269
  · decide +kernel

theorem prime_119753396887 : Nat.Prime 119753396887 := by
  apply nodeValid_prime [2, 3, 19958899481] ⟨119753396887, 3, [(2, 1), (3, 1), (19958899481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19958899481
  · decide +kernel

theorem prime_153356515693 : Nat.Prime 153356515693 := by
  apply nodeValid_prime [2, 3, 53, 12637, 19081] ⟨153356515693, 2, [(2, 2), (3, 1), (53, 1), (12637, 1), (19081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_12637
    · exact prime_19081
  · decide +kernel

theorem prime_187765967899 : Nat.Prime 187765967899 := by
  apply nodeValid_prime [2, 3, 62539, 166799] ⟨187765967899, 2, [(2, 1), (3, 2), (62539, 1), (166799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62539
    · exact prime_166799
  · decide +kernel

theorem prime_285132814931 : Nat.Prime 285132814931 := by
  apply nodeValid_prime [2, 5, 23, 8123, 152617] ⟨285132814931, 2, [(2, 1), (5, 1), (23, 1), (8123, 1), (152617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_8123
    · exact prime_152617
  · decide +kernel

theorem prime_564289737101 : Nat.Prime 564289737101 := by
  apply nodeValid_prime [2, 5, 101, 553171] ⟨564289737101, 3, [(2, 2), (5, 2), (101, 2), (553171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_553171
  · decide +kernel

theorem prime_564786102211 : Nat.Prime 564786102211 := by
  apply nodeValid_prime [2, 3, 5, 11, 1327, 1289731] ⟨564786102211, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (1327, 1), (1289731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1327
    · exact prime_1289731
  · decide +kernel

theorem prime_848669574133 : Nat.Prime 848669574133 := by
  apply nodeValid_prime [2, 3, 43, 1949, 281291] ⟨848669574133, 5, [(2, 2), (3, 2), (43, 1), (1949, 1), (281291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1949
    · exact prime_281291
  · decide +kernel

theorem prime_1679507170241 : Nat.Prime 1679507170241 := by
  apply nodeValid_prime [2, 5, 23, 233, 979373] ⟨1679507170241, 3, [(2, 6), (5, 1), (23, 1), (233, 1), (979373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_233
    · exact prime_979373
  · decide +kernel

theorem prime_1700323537631 : Nat.Prime 1700323537631 := by
  apply nodeValid_prime [2, 5, 2441, 69656843] ⟨1700323537631, 11, [(2, 1), (5, 1), (2441, 1), (69656843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2441
    · exact prime_69656843
  · decide +kernel

theorem prime_3350138186149 : Nat.Prime 3350138186149 := by
  apply nodeValid_prime [2, 3, 13, 1637, 3607, 3637] ⟨3350138186149, 2, [(2, 2), (3, 1), (13, 1), (1637, 1), (3607, 1), (3637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1637
    · exact prime_3607
    · exact prime_3637
  · decide +kernel

theorem prime_3350138200289 : Nat.Prime 3350138200289 := by
  apply nodeValid_prime [2, 11, 131, 72652199] ⟨3350138200289, 3, [(2, 5), (11, 1), (131, 1), (72652199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_131
    · exact prime_72652199
  · decide +kernel

theorem prime_3350138200841 : Nat.Prime 3350138200841 := by
  apply nodeValid_prime [2, 5, 31327, 2673523] ⟨3350138200841, 3, [(2, 3), (5, 1), (31327, 1), (2673523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31327
    · exact prime_2673523
  · decide +kernel

theorem prime_3353095112827 : Nat.Prime 3353095112827 := by
  apply nodeValid_prime [2, 3, 307, 431, 4223563] ⟨3353095112827, 3, [(2, 1), (3, 1), (307, 1), (431, 1), (4223563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_431
    · exact prime_4223563
  · decide +kernel

theorem prime_3353095112837 : Nat.Prime 3353095112837 := by
  apply nodeValid_prime [2, 7, 119753396887] ⟨3353095112837, 2, [(2, 2), (7, 1), (119753396887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_119753396887
  · decide +kernel

theorem prime_3353095139057 : Nat.Prime 3353095139057 := by
  apply nodeValid_prime [2, 13, 223, 72289909] ⟨3353095139057, 3, [(2, 4), (13, 1), (223, 1), (72289909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_223
    · exact prime_72289909
  · decide +kernel

theorem prime_3356053854707 : Nat.Prime 3356053854707 := by
  apply nodeValid_prime [2, 7, 41, 835254817] ⟨3356053854707, 2, [(2, 1), (7, 2), (41, 1), (835254817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_835254817
  · decide +kernel

theorem prime_3356053910273 : Nat.Prime 3356053910273 := by
  apply nodeValid_prime [2, 7, 267542563] ⟨3356053910273, 3, [(2, 8), (7, 2), (267542563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_267542563
  · decide +kernel

theorem prime_3356053911929 : Nat.Prime 3356053911929 := by
  apply nodeValid_prime [2, 8761, 47883431] ⟨3356053911929, 3, [(2, 3), (8761, 1), (47883431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8761
    · exact prime_47883431
  · decide +kernel

theorem prime_3359014328611 : Nat.Prime 3359014328611 := by
  apply nodeValid_prime [2, 3, 5, 101, 349, 1058821] ⟨3359014328611, 12, [(2, 1), (3, 2), (5, 1), (101, 1), (349, 1), (1058821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_349
    · exact prime_1058821
  · decide +kernel

theorem prime_3359014330253 : Nat.Prime 3359014330253 := by
  apply nodeValid_prime [2, 7, 19, 6313936711] ⟨3359014330253, 2, [(2, 2), (7, 1), (19, 1), (6313936711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_6313936711
  · decide +kernel

theorem prime_3359014340483 : Nat.Prime 3359014340483 := by
  apply nodeValid_prime [2, 1679507170241] ⟨3359014340483, 2, [(2, 1), (1679507170241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1679507170241
  · decide +kernel

theorem prime_3361976597593 : Nat.Prime 3361976597593 := by
  apply nodeValid_prime [2, 3, 367, 571, 222823] ⟨3361976597593, 7, [(2, 3), (3, 2), (367, 1), (571, 1), (222823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_571
    · exact prime_222823
  · decide +kernel

theorem prime_3361976757847 : Nat.Prime 3361976757847 := by
  apply nodeValid_prime [2, 3, 7, 8894118407] ⟨3361976757847, 5, [(2, 1), (3, 3), (7, 1), (8894118407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8894118407
  · decide +kernel

theorem prime_3361976762509 : Nat.Prime 3361976762509 := by
  apply nodeValid_prime [2, 3, 7, 13, 257, 619, 6451] ⟨3361976762509, 2, [(2, 2), (3, 2), (7, 1), (13, 1), (257, 1), (619, 1), (6451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_257
    · exact prime_619
    · exact prime_6451
  · decide +kernel

theorem prime_3364940543201 : Nat.Prime 3364940543201 := by
  apply nodeValid_prime [2, 5, 56209, 74831] ⟨3364940543201, 3, [(2, 5), (5, 2), (56209, 1), (74831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_56209
    · exact prime_74831
  · decide +kernel

theorem prime_3364940545403 : Nat.Prime 3364940545403 := by
  apply nodeValid_prime [2, 109, 12497, 1235137] ⟨3364940545403, 2, [(2, 1), (109, 1), (12497, 1), (1235137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_12497
    · exact prime_1235137
  · decide +kernel

theorem prime_3364940626897 : Nat.Prime 3364940626897 := by
  apply nodeValid_prime [2, 3, 487, 143948521] ⟨3364940626897, 7, [(2, 4), (3, 1), (487, 1), (143948521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
    · exact prime_143948521
  · decide +kernel

theorem prime_3367906379729 : Nat.Prime 3367906379729 := by
  apply nodeValid_prime [2, 11, 17, 19, 4229, 14009] ⟨3367906379729, 3, [(2, 4), (11, 1), (17, 1), (19, 1), (4229, 1), (14009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_4229
    · exact prime_14009
  · decide +kernel

theorem prime_3367906381783 : Nat.Prime 3367906381783 := by
  apply nodeValid_prime [2, 3, 3359, 55702861] ⟨3367906381783, 3, [(2, 1), (3, 2), (3359, 1), (55702861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3359
    · exact prime_55702861
  · decide +kernel

theorem prime_3367906427959 : Nat.Prime 3367906427959 := by
  apply nodeValid_prime [2, 3, 4513, 5153, 24137] ⟨3367906427959, 3, [(2, 1), (3, 1), (4513, 1), (5153, 1), (24137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4513
    · exact prime_5153
    · exact prime_24137
  · decide +kernel

theorem prime_3370873866691 : Nat.Prime 3370873866691 := by
  apply nodeValid_prime [2, 3, 5, 11, 7213, 1416161] ⟨3370873866691, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (7213, 1), (1416161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_7213
    · exact prime_1416161
  · decide +kernel

theorem prime_3370873868893 : Nat.Prime 3370873868893 := by
  apply nodeValid_prime [2, 3, 93635385247] ⟨3370873868893, 2, [(2, 2), (3, 2), (93635385247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_93635385247
  · decide +kernel

theorem prime_3370873999007 : Nat.Prime 3370873999007 := by
  apply nodeValid_prime [2, 233, 7233635191] ⟨3370873999007, 5, [(2, 1), (233, 1), (7233635191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_7233635191
  · decide +kernel

theorem prime_3373843345247 : Nat.Prime 3373843345247 := by
  apply nodeValid_prime [2, 11, 153356515693] ⟨3373843345247, 5, [(2, 1), (11, 1), (153356515693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_153356515693
  · decide +kernel

theorem prime_3373843400419 : Nat.Prime 3373843400419 := by
  apply nodeValid_prime [2, 3, 31, 18138943013] ⟨3373843400419, 2, [(2, 1), (3, 1), (31, 1), (18138943013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_18138943013
  · decide +kernel

theorem prime_3373843401209 : Nat.Prime 3373843401209 := by
  apply nodeValid_prime [2, 7, 15451, 3899243] ⟨3373843401209, 3, [(2, 3), (7, 1), (15451, 1), (3899243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15451
    · exact prime_3899243
  · decide +kernel

theorem prime_3376814445833 : Nat.Prime 3376814445833 := by
  apply nodeValid_prime [2, 23, 18352252423] ⟨3376814445833, 3, [(2, 3), (23, 1), (18352252423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_18352252423
  · decide +kernel

theorem prime_3376814446003 : Nat.Prime 3376814446003 := by
  apply nodeValid_prime [2, 3, 127, 263, 16849867] ⟨3376814446003, 3, [(2, 1), (3, 1), (127, 1), (263, 1), (16849867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_263
    · exact prime_16849867
  · decide +kernel

theorem prime_3376814456621 : Nat.Prime 3376814456621 := by
  apply nodeValid_prime [2, 5, 11, 28463, 539267] ⟨3376814456621, 2, [(2, 2), (5, 1), (11, 1), (28463, 1), (539267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_28463
    · exact prime_539267
  · decide +kernel

theorem prime_3379787346983 : Nat.Prime 3379787346983 := by
  apply nodeValid_prime [2, 19, 23459, 3791371] ⟨3379787346983, 5, [(2, 1), (19, 1), (23459, 1), (3791371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23459
    · exact prime_3791371
  · decide +kernel

theorem prime_3379787421977 : Nat.Prime 3379787421977 := by
  apply nodeValid_prime [2, 7, 8819, 6843559] ⟨3379787421977, 3, [(2, 3), (7, 1), (8819, 1), (6843559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8819
    · exact prime_6843559
  · decide +kernel

theorem prime_3379787422183 : Nat.Prime 3379787422183 := by
  apply nodeValid_prime [2, 3, 187765967899] ⟨3379787422183, 3, [(2, 1), (3, 2), (187765967899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_187765967899
  · decide +kernel

theorem prime_3382761985987 : Nat.Prime 3382761985987 := by
  apply nodeValid_prime [2, 3, 29, 19441160839] ⟨3382761985987, 3, [(2, 1), (3, 1), (29, 1), (19441160839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_19441160839
  · decide +kernel

theorem prime_3382761986641 : Nat.Prime 3382761986641 := by
  apply nodeValid_prime [2, 3, 5, 19, 857, 288539] ⟨3382761986641, 26, [(2, 4), (3, 2), (5, 1), (19, 1), (857, 1), (288539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_857
    · exact prime_288539
  · decide +kernel

theorem prime_3382762002911 : Nat.Prime 3382762002911 := by
  apply nodeValid_prime [2, 5, 383, 883227677] ⟨3382762002911, 7, [(2, 1), (5, 1), (383, 1), (883227677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_383
    · exact prime_883227677
  · decide +kernel

theorem prime_3385738422607 : Nat.Prime 3385738422607 := by
  apply nodeValid_prime [2, 3, 564289737101] ⟨3385738422607, 5, [(2, 1), (3, 1), (564289737101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_564289737101
  · decide +kernel

theorem prime_3385738423411 : Nat.Prime 3385738423411 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 43, 22055491] ⟨3385738423411, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (43, 1), (22055491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_22055491
  · decide +kernel

theorem prime_3385738424423 : Nat.Prime 3385738424423 := by
  apply nodeValid_prime [2, 71, 23843228341] ⟨3385738424423, 5, [(2, 1), (71, 1), (23843228341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_23843228341
  · decide +kernel

theorem prime_3388716577331 : Nat.Prime 3388716577331 := by
  apply nodeValid_prime [2, 5, 7, 19, 29, 660593] ⟨3388716577331, 2, [(2, 1), (5, 1), (7, 2), (19, 2), (29, 1), (660593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_29
    · exact prime_660593
  · decide +kernel

theorem prime_3388716578087 : Nat.Prime 3388716578087 := by
  apply nodeValid_prime [2, 7, 6779, 35706031] ⟨3388716578087, 5, [(2, 1), (7, 1), (6779, 1), (35706031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6779
    · exact prime_35706031
  · decide +kernel

theorem prime_3388716613267 : Nat.Prime 3388716613267 := by
  apply nodeValid_prime [2, 3, 564786102211] ⟨3388716613267, 2, [(2, 1), (3, 1), (564786102211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_564786102211
  · decide +kernel

theorem prime_3391696567271 : Nat.Prime 3391696567271 := by
  apply nodeValid_prime [2, 5, 11, 61, 505468937] ⟨3391696567271, 11, [(2, 1), (5, 1), (11, 1), (61, 1), (505468937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_61
    · exact prime_505468937
  · decide +kernel

theorem prime_3391696594961 : Nat.Prime 3391696594961 := by
  apply nodeValid_prime [2, 5, 42396207437] ⟨3391696594961, 3, [(2, 4), (5, 1), (42396207437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_42396207437
  · decide +kernel

theorem prime_3391696599989 : Nat.Prime 3391696599989 := by
  apply nodeValid_prime [2, 29, 43, 679971251] ⟨3391696599989, 2, [(2, 2), (29, 1), (43, 1), (679971251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_43
    · exact prime_679971251
  · decide +kernel

theorem prime_3394678296533 : Nat.Prime 3394678296533 := by
  apply nodeValid_prime [2, 848669574133] ⟨3394678296533, 2, [(2, 2), (848669574133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_848669574133
  · decide +kernel

theorem prime_3394678392653 : Nat.Prime 3394678392653 := by
  apply nodeValid_prime [2, 23, 90989, 405529] ⟨3394678392653, 2, [(2, 2), (23, 1), (90989, 1), (405529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_90989
    · exact prime_405529
  · decide +kernel

theorem prime_3394678392871 : Nat.Prime 3394678392871 := by
  apply nodeValid_prime [2, 3, 5, 161503, 700643] ⟨3394678392871, 3, [(2, 1), (3, 1), (5, 1), (161503, 1), (700643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_161503
    · exact prime_700643
  · decide +kernel

theorem prime_3397661797301 : Nat.Prime 3397661797301 := by
  apply nodeValid_prime [2, 5, 33976617973] ⟨3397661797301, 2, [(2, 2), (5, 2), (33976617973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33976617973
  · decide +kernel

theorem prime_3397661814121 : Nat.Prime 3397661814121 := by
  apply nodeValid_prime [2, 3, 5, 7, 67, 60370679] ⟨3397661814121, 37, [(2, 3), (3, 1), (5, 1), (7, 1), (67, 1), (60370679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_67
    · exact prime_60370679
  · decide +kernel

theorem prime_3397661814433 : Nat.Prime 3397661814433 := by
  apply nodeValid_prime [2, 3, 41, 863227087] ⟨3397661814433, 7, [(2, 5), (3, 1), (41, 1), (863227087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_863227087
  · decide +kernel

theorem prime_3400647075263 : Nat.Prime 3400647075263 := by
  apply nodeValid_prime [2, 1700323537631] ⟨3400647075263, 5, [(2, 1), (1700323537631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1700323537631
  · decide +kernel

theorem prime_3400647098539 : Nat.Prime 3400647098539 := by
  apply nodeValid_prime [2, 3, 479, 1183245337] ⟨3400647098539, 10, [(2, 1), (3, 1), (479, 1), (1183245337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
    · exact prime_1183245337
  · decide +kernel

theorem prime_3400647098899 : Nat.Prime 3400647098899 := by
  apply nodeValid_prime [2, 3, 7, 59, 196047913] ⟨3400647098899, 3, [(2, 1), (3, 1), (7, 2), (59, 1), (196047913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_196047913
  · decide +kernel

theorem prime_3403634123453 : Nat.Prime 3403634123453 := by
  apply nodeValid_prime [2, 23, 2273, 16276297] ⟨3403634123453, 2, [(2, 2), (23, 1), (2273, 1), (16276297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2273
    · exact prime_16276297
  · decide +kernel

theorem prime_3403634189269 : Nat.Prime 3403634189269 := by
  apply nodeValid_prime [2, 3, 71, 3994875809] ⟨3403634189269, 2, [(2, 2), (3, 1), (71, 1), (3994875809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_3994875809
  · decide +kernel

theorem prime_3403634190017 : Nat.Prime 3403634190017 := by
  apply nodeValid_prime [2, 101, 3389, 155371] ⟨3403634190017, 3, [(2, 6), (101, 1), (3389, 1), (155371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_3389
    · exact prime_155371
  · decide +kernel

theorem prime_3406622949421 : Nat.Prime 3406622949421 := by
  apply nodeValid_prime [2, 3, 5, 17, 41, 81459181] ⟨3406622949421, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (41, 1), (81459181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_41
    · exact prime_81459181
  · decide +kernel

theorem prime_3406623043097 : Nat.Prime 3406623043097 := by
  apply nodeValid_prime [2, 7, 13, 23, 203453359] ⟨3406623043097, 3, [(2, 3), (7, 1), (13, 1), (23, 1), (203453359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_203453359
  · decide +kernel

theorem prime_3406623043279 : Nat.Prime 3406623043279 := by
  apply nodeValid_prime [2, 3, 7, 13, 61, 73, 1401131] ⟨3406623043279, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (61, 1), (73, 1), (1401131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_73
    · exact prime_1401131
  · decide +kernel

theorem prime_3409613517229 : Nat.Prime 3409613517229 := by
  apply nodeValid_prime [2, 3, 19, 14954445251] ⟨3409613517229, 2, [(2, 2), (3, 1), (19, 1), (14954445251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_14954445251
  · decide +kernel

theorem prime_3409613517727 : Nat.Prime 3409613517727 := by
  apply nodeValid_prime [2, 3, 13, 1097, 1475843] ⟨3409613517727, 3, [(2, 1), (3, 4), (13, 1), (1097, 1), (1475843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1097
    · exact prime_1475843
  · decide +kernel

theorem prime_3409613550947 : Nat.Prime 3409613550947 := by
  apply nodeValid_prime [2, 2297, 742188409] ⟨3409613550947, 2, [(2, 1), (2297, 1), (742188409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2297
    · exact prime_742188409
  · decide +kernel

theorem prime_3412605874339 : Nat.Prime 3412605874339 := by
  apply nodeValid_prime [2, 3, 41, 19213, 240677] ⟨3412605874339, 3, [(2, 1), (3, 2), (41, 1), (19213, 1), (240677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_19213
    · exact prime_240677
  · decide +kernel

theorem prime_3412605874387 : Nat.Prime 3412605874387 := by
  apply nodeValid_prime [2, 3, 19, 29, 1032246181] ⟨3412605874387, 5, [(2, 1), (3, 1), (19, 1), (29, 1), (1032246181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_1032246181
  · decide +kernel

theorem prime_3412605934583 : Nat.Prime 3412605934583 := by
  apply nodeValid_prime [2, 13, 47, 2792639881] ⟨3412605934583, 10, [(2, 1), (13, 1), (47, 1), (2792639881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_2792639881
  · decide +kernel

theorem prime_3415600095601 : Nat.Prime 3415600095601 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 71, 74377] ⟨3415600095601, 23, [(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (71, 1), (74377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_71
    · exact prime_74377
  · decide +kernel

theorem prime_3415600114081 : Nat.Prime 3415600114081 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 92413423] ⟨3415600114081, 37, [(2, 5), (3, 1), (5, 1), (7, 1), (11, 1), (92413423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_92413423
  · decide +kernel

theorem prime_3415600114109 : Nat.Prime 3415600114109 := by
  apply nodeValid_prime [2, 7, 13, 89, 105432773] ⟨3415600114109, 2, [(2, 2), (7, 1), (13, 1), (89, 1), (105432773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_89
    · exact prime_105432773
  · decide +kernel

theorem prime_3418596034327 : Nat.Prime 3418596034327 := by
  apply nodeValid_prime [2, 3, 11, 73, 3919, 20117] ⟨3418596034327, 3, [(2, 1), (3, 3), (11, 1), (73, 1), (3919, 1), (20117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_3919
    · exact prime_20117
  · decide +kernel

theorem prime_3418596163999 : Nat.Prime 3418596163999 := by
  apply nodeValid_prime [2, 3, 23, 8257478657] ⟨3418596163999, 3, [(2, 1), (3, 2), (23, 1), (8257478657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_8257478657
  · decide +kernel

theorem prime_3418596164981 : Nat.Prime 3418596164981 := by
  apply nodeValid_prime [2, 5, 15679, 10901831] ⟨3418596164981, 2, [(2, 2), (5, 1), (15679, 1), (10901831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15679
    · exact prime_10901831
  · decide +kernel

theorem prime_3421593753601 : Nat.Prime 3421593753601 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 139, 857] ⟨3421593753601, 23, [(2, 11), (3, 1), (5, 2), (11, 1), (17, 1), (139, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_139
    · exact prime_857
  · decide +kernel

theorem prime_3421593779173 : Nat.Prime 3421593779173 := by
  apply nodeValid_prime [2, 3, 285132814931] ⟨3421593779173, 2, [(2, 2), (3, 1), (285132814931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_285132814931
  · decide +kernel

theorem prime_3421593779507 : Nat.Prime 3421593779507 := by
  apply nodeValid_prime [2, 7, 107, 1367, 1670891] ⟨3421593779507, 2, [(2, 1), (7, 1), (107, 1), (1367, 1), (1670891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
    · exact prime_1367
    · exact prime_1670891
  · decide +kernel

end Sude.Lucas.Generated
