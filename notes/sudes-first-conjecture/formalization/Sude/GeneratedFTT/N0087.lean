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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0081

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7757 : Nat.Prime 7757 := by
  apply nodeValid_prime [2, 7, 277] ⟨7757, 2, [(2, 2), (7, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_8419 : Nat.Prime 8419 := by
  apply nodeValid_prime [2, 3, 23, 61] ⟨8419, 3, [(2, 1), (3, 1), (23, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_61
  · decide +kernel

theorem prime_9803 : Nat.Prime 9803 := by
  apply nodeValid_prime [2, 13, 29] ⟨9803, 2, [(2, 1), (13, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_11437 : Nat.Prime 11437 := by
  apply nodeValid_prime [2, 3, 953] ⟨11437, 2, [(2, 2), (3, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_953
  · decide +kernel

theorem prime_11867 : Nat.Prime 11867 := by
  apply nodeValid_prime [2, 17, 349] ⟨11867, 2, [(2, 1), (17, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_349
  · decide +kernel

theorem prime_12373 : Nat.Prime 12373 := by
  apply nodeValid_prime [2, 3, 1031] ⟨12373, 2, [(2, 2), (3, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1031
  · decide +kernel

theorem prime_16477 : Nat.Prime 16477 := by
  apply nodeValid_prime [2, 3, 1373] ⟨16477, 2, [(2, 2), (3, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1373
  · decide +kernel

theorem prime_17191 : Nat.Prime 17191 := by
  apply nodeValid_prime [2, 3, 5, 191] ⟨17191, 3, [(2, 1), (3, 2), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_19249 : Nat.Prime 19249 := by
  apply nodeValid_prime [2, 3, 401] ⟨19249, 7, [(2, 4), (3, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
  · decide +kernel

theorem prime_19441 : Nat.Prime 19441 := by
  apply nodeValid_prime [2, 3, 5] ⟨19441, 13, [(2, 4), (3, 5), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_19501 : Nat.Prime 19501 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨19501, 2, [(2, 2), (3, 1), (5, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_24223 : Nat.Prime 24223 := by
  apply nodeValid_prime [2, 3, 11, 367] ⟨24223, 3, [(2, 1), (3, 1), (11, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_367
  · decide +kernel

theorem prime_26113 : Nat.Prime 26113 := by
  apply nodeValid_prime [2, 3, 17] ⟨26113, 7, [(2, 9), (3, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_26449 : Nat.Prime 26449 := by
  apply nodeValid_prime [2, 3, 19, 29] ⟨26449, 7, [(2, 4), (3, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_30727 : Nat.Prime 30727 := by
  apply nodeValid_prime [2, 3, 569] ⟨30727, 3, [(2, 1), (3, 3), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
  · decide +kernel

theorem prime_38993 : Nat.Prime 38993 := by
  apply nodeValid_prime [2, 2437] ⟨38993, 3, [(2, 4), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2437
  · decide +kernel

theorem prime_42751 : Nat.Prime 42751 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨42751, 6, [(2, 1), (3, 2), (5, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_47123 : Nat.Prime 47123 := by
  apply nodeValid_prime [2, 23561] ⟨47123, 2, [(2, 1), (23561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23561
  · decide +kernel

theorem prime_60887 : Nat.Prime 60887 := by
  apply nodeValid_prime [2, 7, 4349] ⟨60887, 7, [(2, 1), (7, 1), (4349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4349
  · decide +kernel

theorem prime_65809 : Nat.Prime 65809 := by
  apply nodeValid_prime [2, 3, 457] ⟨65809, 11, [(2, 4), (3, 2), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_457
  · decide +kernel

theorem prime_79181 : Nat.Prime 79181 := by
  apply nodeValid_prime [2, 5, 37, 107] ⟨79181, 2, [(2, 2), (5, 1), (37, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_107
  · decide +kernel

theorem prime_85061 : Nat.Prime 85061 := by
  apply nodeValid_prime [2, 5, 4253] ⟨85061, 2, [(2, 2), (5, 1), (4253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4253
  · decide +kernel

theorem prime_89363 : Nat.Prime 89363 := by
  apply nodeValid_prime [2, 7, 13, 491] ⟨89363, 5, [(2, 1), (7, 1), (13, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_491
  · decide +kernel

theorem prime_89513 : Nat.Prime 89513 := by
  apply nodeValid_prime [2, 67, 167] ⟨89513, 3, [(2, 3), (67, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_167
  · decide +kernel

theorem prime_119549 : Nat.Prime 119549 := by
  apply nodeValid_prime [2, 11, 13, 19] ⟨119549, 2, [(2, 2), (11, 2), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_137777 : Nat.Prime 137777 := by
  apply nodeValid_prime [2, 79, 109] ⟨137777, 3, [(2, 4), (79, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_109
  · decide +kernel

theorem prime_144569 : Nat.Prime 144569 := by
  apply nodeValid_prime [2, 17, 1063] ⟨144569, 3, [(2, 3), (17, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1063
  · decide +kernel

theorem prime_150901 : Nat.Prime 150901 := by
  apply nodeValid_prime [2, 3, 5, 503] ⟨150901, 2, [(2, 2), (3, 1), (5, 2), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_503
  · decide +kernel

theorem prime_151553 : Nat.Prime 151553 := by
  apply nodeValid_prime [2, 37] ⟨151553, 3, [(2, 12), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37
  · decide +kernel

theorem prime_156679 : Nat.Prime 156679 := by
  apply nodeValid_prime [2, 3, 26113] ⟨156679, 3, [(2, 1), (3, 1), (26113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26113
  · decide +kernel

theorem prime_182333 : Nat.Prime 182333 := by
  apply nodeValid_prime [2, 79, 577] ⟨182333, 2, [(2, 2), (79, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_577
  · decide +kernel

theorem prime_230861 : Nat.Prime 230861 := by
  apply nodeValid_prime [2, 5, 7, 17, 97] ⟨230861, 2, [(2, 2), (5, 1), (7, 1), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_238481 : Nat.Prime 238481 := by
  apply nodeValid_prime [2, 5, 11, 271] ⟨238481, 3, [(2, 4), (5, 1), (11, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_271
  · decide +kernel

theorem prime_290677 : Nat.Prime 290677 := by
  apply nodeValid_prime [2, 3, 24223] ⟨290677, 5, [(2, 2), (3, 1), (24223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24223
  · decide +kernel

theorem prime_303959 : Nat.Prime 303959 := by
  apply nodeValid_prime [2, 379, 401] ⟨303959, 13, [(2, 1), (379, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_401
  · decide +kernel

theorem prime_350249 : Nat.Prime 350249 := by
  apply nodeValid_prime [2, 43781] ⟨350249, 3, [(2, 3), (43781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43781
  · decide +kernel

theorem prime_451331 : Nat.Prime 451331 := by
  apply nodeValid_prime [2, 5, 11, 373] ⟨451331, 2, [(2, 1), (5, 1), (11, 2), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_373
  · decide +kernel

theorem prime_516457 : Nat.Prime 516457 := by
  apply nodeValid_prime [2, 3, 797] ⟨516457, 5, [(2, 3), (3, 4), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_797
  · decide +kernel

theorem prime_537079 : Nat.Prime 537079 := by
  apply nodeValid_prime [2, 3, 89513] ⟨537079, 3, [(2, 1), (3, 1), (89513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89513
  · decide +kernel

theorem prime_599341 : Nat.Prime 599341 := by
  apply nodeValid_prime [2, 3, 5, 7, 1427] ⟨599341, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1427
  · decide +kernel

theorem prime_624577 : Nat.Prime 624577 := by
  apply nodeValid_prime [2, 3, 3253] ⟨624577, 10, [(2, 6), (3, 1), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3253
  · decide +kernel

theorem prime_694997 : Nat.Prime 694997 := by
  apply nodeValid_prime [2, 293, 593] ⟨694997, 2, [(2, 2), (293, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_593
  · decide +kernel

theorem prime_700499 : Nat.Prime 700499 := by
  apply nodeValid_prime [2, 350249] ⟨700499, 2, [(2, 1), (350249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_350249
  · decide +kernel

theorem prime_710557 : Nat.Prime 710557 := by
  apply nodeValid_prime [2, 3, 7, 11, 769] ⟨710557, 15, [(2, 2), (3, 1), (7, 1), (11, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_769
  · decide +kernel

theorem prime_815401 : Nat.Prime 815401 := by
  apply nodeValid_prime [2, 3, 5, 151] ⟨815401, 13, [(2, 3), (3, 3), (5, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
  · decide +kernel

theorem prime_818603 : Nat.Prime 818603 := by
  apply nodeValid_prime [2, 563, 727] ⟨818603, 2, [(2, 1), (563, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_727
  · decide +kernel

theorem prime_913327 : Nat.Prime 913327 := by
  apply nodeValid_prime [2, 3, 29, 181] ⟨913327, 5, [(2, 1), (3, 1), (29, 2), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_181
  · decide +kernel

theorem prime_922487 : Nat.Prime 922487 := by
  apply nodeValid_prime [2, 379, 1217] ⟨922487, 5, [(2, 1), (379, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_1217
  · decide +kernel

theorem prime_1020247 : Nat.Prime 1020247 := by
  apply nodeValid_prime [2, 3, 97, 1753] ⟨1020247, 5, [(2, 1), (3, 1), (97, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1753
  · decide +kernel

theorem prime_1093999 : Nat.Prime 1093999 := by
  apply nodeValid_prime [2, 3, 182333] ⟨1093999, 6, [(2, 1), (3, 1), (182333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_182333
  · decide +kernel

theorem prime_1125581 : Nat.Prime 1125581 := by
  apply nodeValid_prime [2, 5, 167, 337] ⟨1125581, 2, [(2, 2), (5, 1), (167, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_337
  · decide +kernel

theorem prime_1329073 : Nat.Prime 1329073 := by
  apply nodeValid_prime [2, 3, 27689] ⟨1329073, 10, [(2, 4), (3, 1), (27689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27689
  · decide +kernel

theorem prime_1413443 : Nat.Prime 1413443 := by
  apply nodeValid_prime [2, 23, 30727] ⟨1413443, 2, [(2, 1), (23, 1), (30727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_30727
  · decide +kernel

theorem prime_1430887 : Nat.Prime 1430887 := by
  apply nodeValid_prime [2, 3, 238481] ⟨1430887, 3, [(2, 1), (3, 1), (238481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_238481
  · decide +kernel

theorem prime_1491629 : Nat.Prime 1491629 := by
  apply nodeValid_prime [2, 257, 1451] ⟨1491629, 2, [(2, 2), (257, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_1451
  · decide +kernel

theorem prime_1513819 : Nat.Prime 1513819 := by
  apply nodeValid_prime [2, 3, 37, 2273] ⟨1513819, 2, [(2, 1), (3, 2), (37, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2273
  · decide +kernel

theorem prime_1586339 : Nat.Prime 1586339 := by
  apply nodeValid_prime [2, 13, 17, 37, 97] ⟨1586339, 2, [(2, 1), (13, 1), (17, 1), (37, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_37
    · exact prime_97
  · decide +kernel

theorem prime_1733701 : Nat.Prime 1733701 := by
  apply nodeValid_prime [2, 3, 5, 5779] ⟨1733701, 6, [(2, 2), (3, 1), (5, 2), (5779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5779
  · decide +kernel

theorem prime_1757071 : Nat.Prime 1757071 := by
  apply nodeValid_prime [2, 3, 5, 7, 2789] ⟨1757071, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2789
  · decide +kernel

theorem prime_2449567 : Nat.Prime 2449567 := by
  apply nodeValid_prime [2, 3, 7, 19441] ⟨2449567, 6, [(2, 1), (3, 2), (7, 1), (19441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19441
  · decide +kernel

theorem prime_2758169 : Nat.Prime 2758169 := by
  apply nodeValid_prime [2, 7, 49253] ⟨2758169, 3, [(2, 3), (7, 1), (49253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_49253
  · decide +kernel

theorem prime_3517361 : Nat.Prime 3517361 := by
  apply nodeValid_prime [2, 5, 7, 11, 571] ⟨3517361, 3, [(2, 4), (5, 1), (7, 1), (11, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_571
  · decide +kernel

theorem prime_3666703 : Nat.Prime 3666703 := by
  apply nodeValid_prime [2, 3, 13, 29, 1621] ⟨3666703, 3, [(2, 1), (3, 1), (13, 1), (29, 1), (1621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_1621
  · decide +kernel

theorem prime_4083769 : Nat.Prime 4083769 := by
  apply nodeValid_prime [2, 3, 13, 4363] ⟨4083769, 17, [(2, 3), (3, 2), (13, 1), (4363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4363
  · decide +kernel

theorem prime_4375997 : Nat.Prime 4375997 := by
  apply nodeValid_prime [2, 1093999] ⟨4375997, 2, [(2, 2), (1093999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1093999
  · decide +kernel

theorem prime_5822273 : Nat.Prime 5822273 := by
  apply nodeValid_prime [2, 29, 3137] ⟨5822273, 3, [(2, 6), (29, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3137
  · decide +kernel

theorem prime_6176119 : Nat.Prime 6176119 := by
  apply nodeValid_prime [2, 3, 13, 79181] ⟨6176119, 3, [(2, 1), (3, 1), (13, 1), (79181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_79181
  · decide +kernel

theorem prime_7034723 : Nat.Prime 7034723 := by
  apply nodeValid_prime [2, 3517361] ⟨7034723, 2, [(2, 1), (3517361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3517361
  · decide +kernel

theorem prime_9993233 : Nat.Prime 9993233 := by
  apply nodeValid_prime [2, 624577] ⟨9993233, 3, [(2, 4), (624577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_624577
  · decide +kernel

theorem prime_10402207 : Nat.Prime 10402207 := by
  apply nodeValid_prime [2, 3, 1733701] ⟨10402207, 5, [(2, 1), (3, 1), (1733701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1733701
  · decide +kernel

theorem prime_11644547 : Nat.Prime 11644547 := by
  apply nodeValid_prime [2, 5822273] ⟨11644547, 2, [(2, 1), (5822273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5822273
  · decide +kernel

theorem prime_11996279 : Nat.Prime 11996279 := by
  apply nodeValid_prime [2, 7, 167, 733] ⟨11996279, 7, [(2, 1), (7, 2), (167, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_167
    · exact prime_733
  · decide +kernel

theorem prime_12524293 : Nat.Prime 12524293 := by
  apply nodeValid_prime [2, 3, 11, 31627] ⟨12524293, 2, [(2, 2), (3, 2), (11, 1), (31627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31627
  · decide +kernel

theorem prime_13028731 : Nat.Prime 13028731 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 3037] ⟨13028731, 12, [(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_3037
  · decide +kernel

theorem prime_14144729 : Nat.Prime 14144729 := by
  apply nodeValid_prime [2, 13, 277, 491] ⟨14144729, 3, [(2, 3), (13, 1), (277, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_277
    · exact prime_491
  · decide +kernel

theorem prime_14975087 : Nat.Prime 14975087 := by
  apply nodeValid_prime [2, 7, 41, 3727] ⟨14975087, 5, [(2, 1), (7, 2), (41, 1), (3727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_3727
  · decide +kernel

theorem prime_19083109 : Nat.Prime 19083109 := by
  apply nodeValid_prime [2, 3, 11, 144569] ⟨19083109, 6, [(2, 2), (3, 1), (11, 1), (144569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_144569
  · decide +kernel

theorem prime_21283679 : Nat.Prime 21283679 := by
  apply nodeValid_prime [2, 13, 818603] ⟨21283679, 7, [(2, 1), (13, 1), (818603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_818603
  · decide +kernel

theorem prime_23037841 : Nat.Prime 23037841 := by
  apply nodeValid_prime [2, 3, 5, 7, 653] ⟨23037841, 11, [(2, 4), (3, 2), (5, 1), (7, 2), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_653
  · decide +kernel

theorem prime_25274537 : Nat.Prime 25274537 := by
  apply nodeValid_prime [2, 7, 451331] ⟨25274537, 3, [(2, 3), (7, 1), (451331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_451331
  · decide +kernel

theorem prime_28422281 : Nat.Prime 28422281 := by
  apply nodeValid_prime [2, 5, 710557] ⟨28422281, 3, [(2, 3), (5, 1), (710557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_710557
  · decide +kernel

theorem prime_48864493 : Nat.Prime 48864493 := by
  apply nodeValid_prime [2, 3, 373, 1213] ⟨48864493, 6, [(2, 2), (3, 3), (373, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_1213
  · decide +kernel

theorem prime_60092251 : Nat.Prime 60092251 := by
  apply nodeValid_prime [2, 3, 5, 19, 4217] ⟨60092251, 2, [(2, 1), (3, 1), (5, 3), (19, 1), (4217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_4217
  · decide +kernel

theorem prime_64639513 : Nat.Prime 64639513 := by
  apply nodeValid_prime [2, 3, 7, 42751] ⟨64639513, 10, [(2, 3), (3, 3), (7, 1), (42751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_42751
  · decide +kernel

theorem prime_69181127 : Nat.Prime 69181127 := by
  apply nodeValid_prime [2, 7, 17, 290677] ⟨69181127, 5, [(2, 1), (7, 1), (17, 1), (290677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_290677
  · decide +kernel

theorem prime_70021277 : Nat.Prime 70021277 := by
  apply nodeValid_prime [2, 13, 41, 32843] ⟨70021277, 2, [(2, 2), (13, 1), (41, 1), (32843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_32843
  · decide +kernel

theorem prime_117688387 : Nat.Prime 117688387 := by
  apply nodeValid_prime [2, 3, 1019, 19249] ⟨117688387, 3, [(2, 1), (3, 1), (1019, 1), (19249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1019
    · exact prime_19249
  · decide +kernel

theorem prime_198026207 : Nat.Prime 198026207 := by
  apply nodeValid_prime [2, 7, 14144729] ⟨198026207, 5, [(2, 1), (7, 1), (14144729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_14144729
  · decide +kernel

theorem prime_247753241 : Nat.Prime 247753241 := by
  apply nodeValid_prime [2, 5, 7, 17, 23, 31, 73] ⟨247753241, 11, [(2, 3), (5, 1), (7, 1), (17, 1), (23, 1), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_276454093 : Nat.Prime 276454093 := by
  apply nodeValid_prime [2, 3, 23037841] ⟨276454093, 2, [(2, 2), (3, 1), (23037841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23037841
  · decide +kernel

theorem prime_295458367 : Nat.Prime 295458367 := by
  apply nodeValid_prime [2, 3, 7, 7034723] ⟨295458367, 6, [(2, 1), (3, 1), (7, 1), (7034723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7034723
  · decide +kernel

theorem prime_305063749 : Nat.Prime 305063749 := by
  apply nodeValid_prime [2, 3, 11, 59, 1187] ⟨305063749, 6, [(2, 2), (3, 2), (11, 2), (59, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_1187
  · decide +kernel

theorem prime_311827279 : Nat.Prime 311827279 := by
  apply nodeValid_prime [2, 3, 7, 19, 55823] ⟨311827279, 6, [(2, 1), (3, 1), (7, 2), (19, 1), (55823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_55823
  · decide +kernel

theorem prime_390753751 : Nat.Prime 390753751 := by
  apply nodeValid_prime [2, 3, 5, 79, 1319] ⟨390753751, 11, [(2, 1), (3, 1), (5, 4), (79, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_1319
  · decide +kernel

theorem prime_463582451 : Nat.Prime 463582451 := by
  apply nodeValid_prime [2, 5, 109, 85061] ⟨463582451, 2, [(2, 1), (5, 2), (109, 1), (85061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_85061
  · decide +kernel

theorem prime_495506483 : Nat.Prime 495506483 := by
  apply nodeValid_prime [2, 247753241] ⟨495506483, 2, [(2, 1), (247753241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_247753241
  · decide +kernel

theorem prime_799497821 : Nat.Prime 799497821 := by
  apply nodeValid_prime [2, 5, 11, 101, 3271] ⟨799497821, 2, [(2, 2), (5, 1), (11, 2), (101, 1), (3271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_101
    · exact prime_3271
  · decide +kernel

theorem prime_979632097 : Nat.Prime 979632097 := by
  apply nodeValid_prime [2, 3, 19, 537079] ⟨979632097, 5, [(2, 5), (3, 1), (19, 1), (537079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_537079
  · decide +kernel

theorem prime_1349430529 : Nat.Prime 1349430529 := by
  apply nodeValid_prime [2, 3, 1757071] ⟨1349430529, 11, [(2, 8), (3, 1), (1757071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1757071
  · decide +kernel

theorem prime_1422069287 : Nat.Prime 1422069287 := by
  apply nodeValid_prime [2, 11, 64639513] ⟨1422069287, 5, [(2, 1), (11, 1), (64639513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_64639513
  · decide +kernel

theorem prime_1584209657 : Nat.Prime 1584209657 := by
  apply nodeValid_prime [2, 198026207] ⟨1584209657, 3, [(2, 3), (198026207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_198026207
  · decide +kernel

theorem prime_1650557297 : Nat.Prime 1650557297 := by
  apply nodeValid_prime [2, 8693, 11867] ⟨1650557297, 3, [(2, 4), (8693, 1), (11867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8693
    · exact prime_11867
  · decide +kernel

theorem prime_2178021583 : Nat.Prime 2178021583 := by
  apply nodeValid_prime [2, 3, 11, 3666703] ⟨2178021583, 5, [(2, 1), (3, 3), (11, 1), (3666703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3666703
  · decide +kernel

theorem prime_2432705059 : Nat.Prime 2432705059 := by
  apply nodeValid_prime [2, 3, 7, 2758169] ⟨2432705059, 2, [(2, 1), (3, 2), (7, 2), (2758169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2758169
  · decide +kernel

theorem prime_3993561389 : Nat.Prime 3993561389 := by
  apply nodeValid_prime [2, 887, 1125581] ⟨3993561389, 2, [(2, 2), (887, 1), (1125581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_887
    · exact prime_1125581
  · decide +kernel

theorem prime_5397722117 : Nat.Prime 5397722117 := by
  apply nodeValid_prime [2, 1349430529] ⟨5397722117, 2, [(2, 2), (1349430529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1349430529
  · decide +kernel

theorem prime_8805351157 : Nat.Prime 8805351157 := by
  apply nodeValid_prime [2, 3, 7, 14975087] ⟨8805351157, 2, [(2, 2), (3, 1), (7, 2), (14975087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14975087
  · decide +kernel

theorem prime_11331830309 : Nat.Prime 11331830309 := by
  apply nodeValid_prime [2, 37, 83, 922487] ⟨11331830309, 2, [(2, 2), (37, 1), (83, 1), (922487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_83
    · exact prime_922487
  · decide +kernel

theorem prime_11376554297 : Nat.Prime 11376554297 := by
  apply nodeValid_prime [2, 1422069287] ⟨11376554297, 3, [(2, 3), (1422069287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1422069287
  · decide +kernel

theorem prime_14347024859 : Nat.Prime 14347024859 := by
  apply nodeValid_prime [2, 11969, 599341] ⟨14347024859, 2, [(2, 1), (11969, 1), (599341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11969
    · exact prime_599341
  · decide +kernel

theorem prime_15989956421 : Nat.Prime 15989956421 := by
  apply nodeValid_prime [2, 5, 799497821] ⟨15989956421, 2, [(2, 2), (5, 1), (799497821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_799497821
  · decide +kernel

theorem prime_22251957649 : Nat.Prime 22251957649 := by
  apply nodeValid_prime [2, 3, 463582451] ⟨22251957649, 7, [(2, 4), (3, 1), (463582451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463582451
  · decide +kernel

theorem prime_23353235663 : Nat.Prime 23353235663 := by
  apply nodeValid_prime [2, 79, 211, 700499] ⟨23353235663, 5, [(2, 1), (79, 1), (211, 1), (700499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_211
    · exact prime_700499
  · decide +kernel

theorem prime_23609753953 : Nat.Prime 23609753953 := by
  apply nodeValid_prime [2, 3, 17, 307, 47123] ⟨23609753953, 5, [(2, 5), (3, 1), (17, 1), (307, 1), (47123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_307
    · exact prime_47123
  · decide +kernel

theorem prime_29192460709 : Nat.Prime 29192460709 := by
  apply nodeValid_prime [2, 3, 2432705059] ⟨29192460709, 2, [(2, 2), (3, 1), (2432705059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2432705059
  · decide +kernel

theorem prime_30099196187 : Nat.Prime 30099196187 := by
  apply nodeValid_prime [2, 53, 179, 1586339] ⟨30099196187, 2, [(2, 1), (53, 1), (179, 1), (1586339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_179
    · exact prime_1586339
  · decide +kernel

theorem prime_33116350079 : Nat.Prime 33116350079 := by
  apply nodeValid_prime [2, 7, 383, 6176119] ⟨33116350079, 7, [(2, 1), (7, 1), (383, 1), (6176119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_383
    · exact prime_6176119
  · decide +kernel

theorem prime_53764620271 : Nat.Prime 53764620271 := by
  apply nodeValid_prime [2, 3, 5, 463, 499, 7757] ⟨53764620271, 3, [(2, 1), (3, 1), (5, 1), (463, 1), (499, 1), (7757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_463
    · exact prime_499
    · exact prime_7757
  · decide +kernel

theorem prime_69577743889 : Nat.Prime 69577743889 := by
  apply nodeValid_prime [2, 3, 17, 28422281] ⟨69577743889, 7, [(2, 4), (3, 2), (17, 1), (28422281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_28422281
  · decide +kernel

theorem prime_92249746991 : Nat.Prime 92249746991 := by
  apply nodeValid_prime [2, 5, 31, 1289, 230861] ⟨92249746991, 17, [(2, 1), (5, 1), (31, 1), (1289, 1), (230861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1289
    · exact prime_230861
  · decide +kernel

theorem prime_92431208633 : Nat.Prime 92431208633 := by
  apply nodeValid_prime [2, 7, 1650557297] ⟨92431208633, 3, [(2, 3), (7, 1), (1650557297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1650557297
  · decide +kernel

theorem prime_118984217201 : Nat.Prime 118984217201 := by
  apply nodeValid_prime [2, 5, 17, 127, 137777] ⟨118984217201, 3, [(2, 4), (5, 2), (17, 1), (127, 1), (137777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_127
    · exact prime_137777
  · decide +kernel

theorem prime_196942394951 : Nat.Prime 196942394951 := by
  apply nodeValid_prime [2, 5, 7, 7103, 11317] ⟨196942394951, 7, [(2, 1), (5, 2), (7, 2), (7103, 1), (11317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7103
    · exact prime_11317
  · decide +kernel

theorem prime_239613676747 : Nat.Prime 239613676747 := by
  apply nodeValid_prime [2, 3, 3329, 11996279] ⟨239613676747, 2, [(2, 1), (3, 1), (3329, 1), (11996279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3329
    · exact prime_11996279
  · decide +kernel

theorem prime_295413573787 : Nat.Prime 295413573787 := by
  apply nodeValid_prime [2, 3, 307, 2437, 65809] ⟨295413573787, 5, [(2, 1), (3, 1), (307, 1), (2437, 1), (65809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_2437
    · exact prime_65809
  · decide +kernel

theorem prime_395442796013 : Nat.Prime 395442796013 := by
  apply nodeValid_prime [2, 11, 23, 390753751] ⟨395442796013, 2, [(2, 2), (11, 1), (23, 1), (390753751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_390753751
  · decide +kernel

theorem prime_594335063977 : Nat.Prime 594335063977 := by
  apply nodeValid_prime [2, 3, 97, 2659, 96013] ⟨594335063977, 10, [(2, 3), (3, 1), (97, 1), (2659, 1), (96013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_2659
    · exact prime_96013
  · decide +kernel

theorem prime_1181654295149 : Nat.Prime 1181654295149 := by
  apply nodeValid_prime [2, 295413573787] ⟨1181654295149, 2, [(2, 2), (295413573787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_295413573787
  · decide +kernel

theorem prime_1182821645963 : Nat.Prime 1182821645963 := by
  apply nodeValid_prime [2, 11, 53764620271] ⟨1182821645963, 2, [(2, 1), (11, 1), (53764620271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53764620271
  · decide +kernel

theorem prime_1193362984193 : Nat.Prime 1193362984193 := by
  apply nodeValid_prime [2, 38993, 119549] ⟨1193362984193, 3, [(2, 8), (38993, 1), (119549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_38993
    · exact prime_119549
  · decide +kernel

theorem prime_1202786388341 : Nat.Prime 1202786388341 := by
  apply nodeValid_prime [2, 5, 24551, 2449567] ⟨1202786388341, 2, [(2, 2), (5, 1), (24551, 1), (2449567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_24551
    · exact prime_2449567
  · decide +kernel

theorem prime_1208701518341 : Nat.Prime 1208701518341 := by
  apply nodeValid_prime [2, 5, 137, 541, 815401] ⟨1208701518341, 2, [(2, 2), (5, 1), (137, 1), (541, 1), (815401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_541
    · exact prime_815401
  · decide +kernel

theorem prime_2360975395301 : Nat.Prime 2360975395301 := by
  apply nodeValid_prime [2, 5, 23609753953] ⟨2360975395301, 2, [(2, 2), (5, 2), (23609753953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23609753953
  · decide +kernel

theorem prime_2360975395973 : Nat.Prime 2360975395973 := by
  apply nodeValid_prime [2, 271, 2178021583] ⟨2360975395973, 2, [(2, 2), (271, 1), (2178021583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_2178021583
  · decide +kernel

theorem prime_2360975440283 : Nat.Prime 2360975440283 := by
  apply nodeValid_prime [2, 19, 47, 2593, 10847] ⟨2360975440283, 2, [(2, 1), (19, 1), (47, 2), (2593, 1), (10847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_2593
    · exact prime_10847
  · decide +kernel

theorem prime_2363308590299 : Nat.Prime 2363308590299 := by
  apply nodeValid_prime [2, 1181654295149] ⟨2363308590299, 2, [(2, 1), (1181654295149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1181654295149
  · decide +kernel

theorem prime_2363308739413 : Nat.Prime 2363308739413 := by
  apply nodeValid_prime [2, 3, 196942394951] ⟨2363308739413, 2, [(2, 2), (3, 1), (196942394951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_196942394951
  · decide +kernel

theorem prime_2363308740161 : Nat.Prime 2363308740161 := by
  apply nodeValid_prime [2, 5, 23, 6101, 52631] ⟨2363308740161, 6, [(2, 6), (5, 1), (23, 1), (6101, 1), (52631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_6101
    · exact prime_52631
  · decide +kernel

theorem prime_2365643291927 : Nat.Prime 2365643291927 := by
  apply nodeValid_prime [2, 1182821645963] ⟨2365643291927, 5, [(2, 1), (1182821645963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1182821645963
  · decide +kernel

theorem prime_2365643292227 : Nat.Prime 2365643292227 := by
  apply nodeValid_prime [2, 17, 69577743889] ⟨2365643292227, 2, [(2, 1), (17, 1), (69577743889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_69577743889
  · decide +kernel

theorem prime_2365643298547 : Nat.Prime 2365643298547 := by
  apply nodeValid_prime [2, 3, 11, 17191, 694997] ⟨2365643298547, 3, [(2, 1), (3, 2), (11, 1), (17191, 1), (694997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17191
    · exact prime_694997
  · decide +kernel

theorem prime_2367979557623 : Nat.Prime 2367979557623 := by
  apply nodeValid_prime [2, 7, 701, 12373, 19501] ⟨2367979557623, 5, [(2, 1), (7, 1), (701, 1), (12373, 1), (19501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_701
    · exact prime_12373
    · exact prime_19501
  · decide +kernel

theorem prime_2367979558183 : Nat.Prime 2367979558183 := by
  apply nodeValid_prime [2, 3, 7, 883, 21283679] ⟨2367979558183, 3, [(2, 1), (3, 2), (7, 1), (883, 1), (21283679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_883
    · exact prime_21283679
  · decide +kernel

theorem prime_2367979566493 : Nat.Prime 2367979566493 := by
  apply nodeValid_prime [2, 3, 17, 43, 11437, 23603] ⟨2367979566493, 2, [(2, 2), (3, 1), (17, 1), (43, 1), (11437, 1), (23603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_11437
    · exact prime_23603
  · decide +kernel

theorem prime_2370317393383 : Nat.Prime 2370317393383 := by
  apply nodeValid_prime [2, 3, 1429, 276454093] ⟨2370317393383, 5, [(2, 1), (3, 1), (1429, 1), (276454093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1429
    · exact prime_276454093
  · decide +kernel

theorem prime_2370317409133 : Nat.Prime 2370317409133 := by
  apply nodeValid_prime [2, 3, 16963, 11644547] ⟨2370317409133, 2, [(2, 2), (3, 1), (16963, 1), (11644547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16963
    · exact prime_11644547
  · decide +kernel

theorem prime_2370317409667 : Nat.Prime 2370317409667 := by
  apply nodeValid_prime [2, 3, 337, 383, 1020247] ⟨2370317409667, 2, [(2, 1), (3, 2), (337, 1), (383, 1), (1020247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
    · exact prime_383
    · exact prime_1020247
  · decide +kernel

theorem prime_2372656776079 : Nat.Prime 2372656776079 := by
  apply nodeValid_prime [2, 3, 395442796013] ⟨2372656776079, 3, [(2, 1), (3, 1), (395442796013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_395442796013
  · decide +kernel

theorem prime_2372656821407 : Nat.Prime 2372656821407 := by
  apply nodeValid_prime [2, 17, 37, 431, 4375997] ⟨2372656821407, 5, [(2, 1), (17, 1), (37, 1), (431, 1), (4375997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_431
    · exact prime_4375997
  · decide +kernel

theorem prime_2374997689697 : Nat.Prime 2374997689697 := by
  apply nodeValid_prime [2, 51869, 1430887] ⟨2374997689697, 3, [(2, 5), (51869, 1), (1430887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_51869
    · exact prime_1430887
  · decide +kernel

theorem prime_2374997692817 : Nat.Prime 2374997692817 := by
  apply nodeValid_prime [2, 7, 839, 25274537] ⟨2374997692817, 3, [(2, 4), (7, 1), (839, 1), (25274537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_839
    · exact prime_25274537
  · decide +kernel

theorem prime_2374997731481 : Nat.Prime 2374997731481 := by
  apply nodeValid_prime [2, 5, 11, 5397722117] ⟨2374997731481, 6, [(2, 3), (5, 1), (11, 1), (5397722117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_5397722117
  · decide +kernel

theorem prime_2377340248229 : Nat.Prime 2377340248229 := by
  apply nodeValid_prime [2, 11, 71, 69181127] ⟨2377340248229, 3, [(2, 2), (11, 2), (71, 1), (69181127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_69181127
  · decide +kernel

theorem prime_2377340250587 : Nat.Prime 2377340250587 := by
  apply nodeValid_prime [2, 7, 2659, 3361, 19001] ⟨2377340250587, 5, [(2, 1), (7, 1), (2659, 1), (3361, 1), (19001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2659
    · exact prime_3361
    · exact prime_19001
  · decide +kernel

theorem prime_2377340255909 : Nat.Prime 2377340255909 := by
  apply nodeValid_prime [2, 594335063977] ⟨2377340255909, 2, [(2, 2), (594335063977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_594335063977
  · decide +kernel

theorem prime_2379684344021 : Nat.Prime 2379684344021 := by
  apply nodeValid_prime [2, 5, 118984217201] ⟨2379684344021, 2, [(2, 2), (5, 1), (118984217201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_118984217201
  · decide +kernel

theorem prime_2379684364879 : Nat.Prime 2379684364879 := by
  apply nodeValid_prime [2, 3, 139, 157, 1103, 16477] ⟨2379684364879, 15, [(2, 1), (3, 1), (139, 1), (157, 1), (1103, 1), (16477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_157
    · exact prime_1103
    · exact prime_16477
  · decide +kernel

theorem prime_2379684364891 : Nat.Prime 2379684364891 := by
  apply nodeValid_prime [2, 3, 5, 7, 11331830309] ⟨2379684364891, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (11331830309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11331830309
  · decide +kernel

theorem prime_2382029997817 : Nat.Prime 2382029997817 := by
  apply nodeValid_prime [2, 3, 7, 743, 19083109] ⟨2382029997817, 10, [(2, 3), (3, 1), (7, 1), (743, 1), (19083109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_743
    · exact prime_19083109
  · decide +kernel

theorem prime_2382030037627 : Nat.Prime 2382030037627 := by
  apply nodeValid_prime [2, 3, 17, 23353235663] ⟨2382030037627, 2, [(2, 1), (3, 1), (17, 1), (23353235663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23353235663
  · decide +kernel

theorem prime_2382030038761 : Nat.Prime 2382030038761 := by
  apply nodeValid_prime [2, 3, 5, 19, 3413, 16111] ⟨2382030038761, 11, [(2, 3), (3, 1), (5, 1), (19, 2), (3413, 1), (16111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_3413
    · exact prime_16111
  · decide +kernel

theorem prime_2384377195817 : Nat.Prime 2384377195817 := by
  apply nodeValid_prime [2, 7, 11, 29, 7549, 17681] ⟨2384377195817, 5, [(2, 3), (7, 1), (11, 1), (29, 1), (7549, 1), (17681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_7549
    · exact prime_17681
  · decide +kernel

theorem prime_2384377196197 : Nat.Prime 2384377196197 := by
  apply nodeValid_prime [2, 3, 401, 495506483] ⟨2384377196197, 2, [(2, 2), (3, 1), (401, 1), (495506483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_495506483
  · decide +kernel

theorem prime_2384377205689 : Nat.Prime 2384377205689 := by
  apply nodeValid_prime [2, 3, 33116350079] ⟨2384377205689, 7, [(2, 3), (3, 2), (33116350079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33116350079
  · decide +kernel

theorem prime_2386725968303 : Nat.Prime 2386725968303 := by
  apply nodeValid_prime [2, 13, 23, 26449, 150901] ⟨2386725968303, 5, [(2, 1), (13, 1), (23, 1), (26449, 1), (150901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_26449
    · exact prime_150901
  · decide +kernel

theorem prime_2386725968387 : Nat.Prime 2386725968387 := by
  apply nodeValid_prime [2, 1193362984193] ⟨2386725968387, 2, [(2, 1), (1193362984193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1193362984193
  · decide +kernel

theorem prime_2386725993467 : Nat.Prime 2386725993467 := by
  apply nodeValid_prime [2, 43, 89, 311827279] ⟨2386725993467, 5, [(2, 1), (43, 1), (89, 1), (311827279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_89
    · exact prime_311827279
  · decide +kernel

theorem prime_2389076355563 : Nat.Prime 2389076355563 := by
  apply nodeValid_prime [2, 13, 311, 295458367] ⟨2389076355563, 2, [(2, 1), (13, 1), (311, 1), (295458367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_311
    · exact prime_295458367
  · decide +kernel

theorem prime_2389076401577 : Nat.Prime 2389076401577 := by
  apply nodeValid_prime [2, 31, 41, 773, 303959] ⟨2389076401577, 3, [(2, 3), (31, 1), (41, 1), (773, 1), (303959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41
    · exact prime_773
    · exact prime_303959
  · decide +kernel

theorem prime_2389076402371 : Nat.Prime 2389076402371 := by
  apply nodeValid_prime [2, 3, 5, 7, 11376554297] ⟨2389076402371, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (11376554297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11376554297
  · decide +kernel

theorem prime_2391428287421 : Nat.Prime 2391428287421 := by
  apply nodeValid_prime [2, 5, 2447, 48864493] ⟨2391428287421, 2, [(2, 2), (5, 1), (2447, 1), (48864493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2447
    · exact prime_48864493
  · decide +kernel

theorem prime_2391428315651 : Nat.Prime 2391428315651 := by
  apply nodeValid_prime [2, 5, 11, 8419, 516457] ⟨2391428315651, 2, [(2, 1), (5, 2), (11, 1), (8419, 1), (516457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_8419
    · exact prime_516457
  · decide +kernel

theorem prime_2391428316509 : Nat.Prime 2391428316509 := by
  apply nodeValid_prime [2, 7, 11, 23, 223, 1513819] ⟨2391428316509, 2, [(2, 2), (7, 1), (11, 1), (23, 1), (223, 1), (1513819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_223
    · exact prime_1513819
  · decide +kernel

theorem prime_2393781778139 : Nat.Prime 2393781778139 := by
  apply nodeValid_prime [2, 41, 29192460709] ⟨2393781778139, 2, [(2, 1), (41, 1), (29192460709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_29192460709
  · decide +kernel

theorem prime_2393781791581 : Nat.Prime 2393781791581 := by
  apply nodeValid_prime [2, 3, 5, 113, 117688387] ⟨2393781791581, 2, [(2, 2), (3, 2), (5, 1), (113, 1), (117688387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_117688387
  · decide +kernel

theorem prime_2393781793211 : Nat.Prime 2393781793211 := by
  apply nodeValid_prime [2, 5, 23, 563, 1997, 9257] ⟨2393781793211, 2, [(2, 1), (5, 1), (23, 1), (563, 1), (1997, 1), (9257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_563
    · exact prime_1997
    · exact prime_9257
  · decide +kernel

theorem prime_2396136766487 : Nat.Prime 2396136766487 := by
  apply nodeValid_prime [2, 17, 19, 41507, 89363] ⟨2396136766487, 5, [(2, 1), (17, 1), (19, 1), (41507, 1), (89363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_41507
    · exact prime_89363
  · decide +kernel

theorem prime_2396136767471 : Nat.Prime 2396136767471 := by
  apply nodeValid_prime [2, 5, 239613676747] ⟨2396136767471, 13, [(2, 1), (5, 1), (239613676747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239613676747
  · decide +kernel

theorem prime_2396136833401 : Nat.Prime 2396136833401 := by
  apply nodeValid_prime [2, 3, 5, 3993561389] ⟨2396136833401, 14, [(2, 3), (3, 1), (5, 2), (3993561389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3993561389
  · decide +kernel

theorem prime_2398493420699 : Nat.Prime 2398493420699 := by
  apply nodeValid_prime [2, 757, 1584209657] ⟨2398493420699, 2, [(2, 1), (757, 1), (1584209657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_757
    · exact prime_1584209657
  · decide +kernel

theorem prime_2398493421767 : Nat.Prime 2398493421767 := by
  apply nodeValid_prime [2, 13, 92249746991] ⟨2398493421767, 5, [(2, 1), (13, 1), (92249746991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_92249746991
  · decide +kernel

theorem prime_2398493463151 : Nat.Prime 2398493463151 := by
  apply nodeValid_prime [2, 3, 5, 15989956421] ⟨2398493463151, 3, [(2, 1), (3, 1), (5, 2), (15989956421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15989956421
  · decide +kernel

theorem prime_2400851664713 : Nat.Prime 2400851664713 := by
  apply nodeValid_prime [2, 67, 3169, 1413443] ⟨2400851664713, 3, [(2, 3), (67, 1), (3169, 1), (1413443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_3169
    · exact prime_1413443
  · decide +kernel

theorem prime_2400851704193 : Nat.Prime 2400851704193 := by
  apply nodeValid_prime [2, 23, 5381, 151553] ⟨2400851704193, 3, [(2, 7), (23, 1), (5381, 1), (151553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_5381
    · exact prime_151553
  · decide +kernel

theorem prime_2400851704631 : Nat.Prime 2400851704631 := by
  apply nodeValid_prime [2, 5, 787, 305063749] ⟨2400851704631, 7, [(2, 1), (5, 1), (787, 1), (305063749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_787
    · exact prime_305063749
  · decide +kernel

theorem prime_2403211424459 : Nat.Prime 2403211424459 := by
  apply nodeValid_prime [2, 13, 92431208633] ⟨2403211424459, 6, [(2, 1), (13, 1), (92431208633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_92431208633
  · decide +kernel

theorem prime_2403211426093 : Nat.Prime 2403211426093 := by
  apply nodeValid_prime [2, 3, 22251957649] ⟨2403211426093, 2, [(2, 2), (3, 3), (22251957649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22251957649
  · decide +kernel

theorem prime_2403211440761 : Nat.Prime 2403211440761 := by
  apply nodeValid_prime [2, 5, 13, 2269, 156679] ⟨2403211440761, 3, [(2, 3), (5, 1), (13, 2), (2269, 1), (156679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2269
    · exact prime_156679
  · decide +kernel

theorem prime_2405572776683 : Nat.Prime 2405572776683 := by
  apply nodeValid_prime [2, 1202786388341] ⟨2405572776683, 2, [(2, 1), (1202786388341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1202786388341
  · decide +kernel

theorem prime_2405572776917 : Nat.Prime 2405572776917 := by
  apply nodeValid_prime [2, 31, 1489, 13028731] ⟨2405572776917, 3, [(2, 2), (31, 1), (1489, 1), (13028731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1489
    · exact prime_13028731
  · decide +kernel

theorem prime_2405572781993 : Nat.Prime 2405572781993 := by
  apply nodeValid_prime [2, 137, 211, 10402207] ⟨2405572781993, 3, [(2, 3), (137, 1), (211, 1), (10402207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_211
    · exact prime_10402207
  · decide +kernel

theorem prime_2407935694427 : Nat.Prime 2407935694427 := by
  apply nodeValid_prime [2, 1229, 979632097] ⟨2407935694427, 2, [(2, 1), (1229, 1), (979632097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1229
    · exact prime_979632097
  · decide +kernel

theorem prime_2407935694961 : Nat.Prime 2407935694961 := by
  apply nodeValid_prime [2, 5, 30099196187] ⟨2407935694961, 3, [(2, 4), (5, 1), (30099196187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30099196187
  · decide +kernel

theorem prime_2407935695393 : Nat.Prime 2407935695393 := by
  apply nodeValid_prime [2, 41, 43, 701, 60887] ⟨2407935695393, 3, [(2, 5), (41, 1), (43, 1), (701, 1), (60887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_43
    · exact prime_701
    · exact prime_60887
  · decide +kernel

theorem prime_2410300176313 : Nat.Prime 2410300176313 := by
  apply nodeValid_prime [2, 3, 7, 14347024859] ⟨2410300176313, 5, [(2, 3), (3, 1), (7, 1), (14347024859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14347024859
  · decide +kernel

theorem prime_2410300187611 : Nat.Prime 2410300187611 := by
  apply nodeValid_prime [2, 3, 5, 7, 191, 60092251] ⟨2410300187611, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (191, 1), (60092251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_191
    · exact prime_60092251
  · decide +kernel

theorem prime_2410300187851 : Nat.Prime 2410300187851 := by
  apply nodeValid_prime [2, 3, 5, 1283, 12524293] ⟨2410300187851, 3, [(2, 1), (3, 1), (5, 2), (1283, 1), (12524293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1283
    · exact prime_12524293
  · decide +kernel

theorem prime_2412666216901 : Nat.Prime 2412666216901 := by
  apply nodeValid_prime [2, 3, 5, 2017, 1329073] ⟨2412666216901, 6, [(2, 2), (3, 2), (5, 2), (2017, 1), (1329073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2017
    · exact prime_1329073
  · decide +kernel

theorem prime_2412666217019 : Nat.Prime 2412666217019 := by
  apply nodeValid_prime [2, 137, 8805351157] ⟨2412666217019, 2, [(2, 1), (137, 1), (8805351157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_8805351157
  · decide +kernel

theorem prime_2412666222587 : Nat.Prime 2412666222587 := by
  apply nodeValid_prime [2, 83, 3559, 4083769] ⟨2412666222587, 2, [(2, 1), (83, 1), (3559, 1), (4083769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_3559
    · exact prime_4083769
  · decide +kernel

theorem prime_2415033843731 : Nat.Prime 2415033843731 := by
  apply nodeValid_prime [2, 5, 3449, 70021277] ⟨2415033843731, 6, [(2, 1), (5, 1), (3449, 1), (70021277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3449
    · exact prime_70021277
  · decide +kernel

theorem prime_2415033865261 : Nat.Prime 2415033865261 := by
  apply nodeValid_prime [2, 3, 5, 19, 15461, 45673] ⟨2415033865261, 7, [(2, 2), (3, 2), (5, 1), (19, 1), (15461, 1), (45673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_15461
    · exact prime_45673
  · decide +kernel

theorem prime_2415033865483 : Nat.Prime 2415033865483 := by
  apply nodeValid_prime [2, 3, 7, 5507, 1491629] ⟨2415033865483, 2, [(2, 1), (3, 1), (7, 2), (5507, 1), (1491629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5507
    · exact prime_1491629
  · decide +kernel

theorem prime_2417403035633 : Nat.Prime 2417403035633 := by
  apply nodeValid_prime [2, 13, 1163, 9993233] ⟨2417403035633, 3, [(2, 4), (13, 1), (1163, 1), (9993233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1163
    · exact prime_9993233
  · decide +kernel

theorem prime_2417403036683 : Nat.Prime 2417403036683 := by
  apply nodeValid_prime [2, 1208701518341] ⟨2417403036683, 2, [(2, 1), (1208701518341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1208701518341
  · decide +kernel

theorem prime_2417403036871 : Nat.Prime 2417403036871 := by
  apply nodeValid_prime [2, 3, 5, 9803, 913327] ⟨2417403036871, 12, [(2, 1), (3, 3), (5, 1), (9803, 1), (913327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9803
    · exact prime_913327
  · decide +kernel

end Sude.Lucas.Generated
