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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0060

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10111 : Nat.Prime 10111 := by
  apply nodeValid_prime [2, 3, 5, 337] ⟨10111, 12, [(2, 1), (3, 1), (5, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_337
  · decide +kernel

theorem prime_14057 : Nat.Prime 14057 := by
  apply nodeValid_prime [2, 7, 251] ⟨14057, 3, [(2, 3), (7, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_251
  · decide +kernel

theorem prime_18899 : Nat.Prime 18899 := by
  apply nodeValid_prime [2, 11, 859] ⟨18899, 2, [(2, 1), (11, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_859
  · decide +kernel

theorem prime_21059 : Nat.Prime 21059 := by
  apply nodeValid_prime [2, 10529] ⟨21059, 2, [(2, 1), (10529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10529
  · decide +kernel

theorem prime_21407 : Nat.Prime 21407 := by
  apply nodeValid_prime [2, 7, 11, 139] ⟨21407, 5, [(2, 1), (7, 1), (11, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_139
  · decide +kernel

theorem prime_22549 : Nat.Prime 22549 := by
  apply nodeValid_prime [2, 3, 1879] ⟨22549, 2, [(2, 2), (3, 1), (1879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1879
  · decide +kernel

theorem prime_24061 : Nat.Prime 24061 := by
  apply nodeValid_prime [2, 3, 5, 401] ⟨24061, 10, [(2, 2), (3, 1), (5, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_401
  · decide +kernel

theorem prime_32411 : Nat.Prime 32411 := by
  apply nodeValid_prime [2, 5, 7, 463] ⟨32411, 2, [(2, 1), (5, 1), (7, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_463
  · decide +kernel

theorem prime_32611 : Nat.Prime 32611 := by
  apply nodeValid_prime [2, 3, 5, 1087] ⟨32611, 3, [(2, 1), (3, 1), (5, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1087
  · decide +kernel

theorem prime_35023 : Nat.Prime 35023 := by
  apply nodeValid_prime [2, 3, 13, 449] ⟨35023, 5, [(2, 1), (3, 1), (13, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_449
  · decide +kernel

theorem prime_39371 : Nat.Prime 39371 := by
  apply nodeValid_prime [2, 5, 31, 127] ⟨39371, 2, [(2, 1), (5, 1), (31, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_127
  · decide +kernel

theorem prime_51283 : Nat.Prime 51283 := by
  apply nodeValid_prime [2, 3, 7, 11, 37] ⟨51283, 2, [(2, 1), (3, 2), (7, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_54617 : Nat.Prime 54617 := by
  apply nodeValid_prime [2, 6827] ⟨54617, 3, [(2, 3), (6827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6827
  · decide +kernel

theorem prime_56519 : Nat.Prime 56519 := by
  apply nodeValid_prime [2, 7, 11, 367] ⟨56519, 13, [(2, 1), (7, 1), (11, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_367
  · decide +kernel

theorem prime_59981 : Nat.Prime 59981 := by
  apply nodeValid_prime [2, 5, 2999] ⟨59981, 2, [(2, 2), (5, 1), (2999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2999
  · decide +kernel

theorem prime_63241 : Nat.Prime 63241 := by
  apply nodeValid_prime [2, 3, 5, 17, 31] ⟨63241, 7, [(2, 3), (3, 1), (5, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_65029 : Nat.Prime 65029 := by
  apply nodeValid_prime [2, 3, 5419] ⟨65029, 2, [(2, 2), (3, 1), (5419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5419
  · decide +kernel

theorem prime_70451 : Nat.Prime 70451 := by
  apply nodeValid_prime [2, 5, 1409] ⟨70451, 6, [(2, 1), (5, 2), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1409
  · decide +kernel

theorem prime_88397 : Nat.Prime 88397 := by
  apply nodeValid_prime [2, 7, 11, 41] ⟨88397, 2, [(2, 2), (7, 2), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_89611 : Nat.Prime 89611 := by
  apply nodeValid_prime [2, 3, 5, 29, 103] ⟨89611, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_103
  · decide +kernel

theorem prime_90197 : Nat.Prime 90197 := by
  apply nodeValid_prime [2, 22549] ⟨90197, 2, [(2, 2), (22549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22549
  · decide +kernel

theorem prime_101603 : Nat.Prime 101603 := by
  apply nodeValid_prime [2, 37, 1373] ⟨101603, 2, [(2, 1), (37, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1373
  · decide +kernel

theorem prime_101693 : Nat.Prime 101693 := by
  apply nodeValid_prime [2, 25423] ⟨101693, 2, [(2, 2), (25423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25423
  · decide +kernel

theorem prime_114661 : Nat.Prime 114661 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨114661, 2, [(2, 2), (3, 2), (5, 1), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_130411 : Nat.Prime 130411 := by
  apply nodeValid_prime [2, 3, 5, 7, 23] ⟨130411, 2, [(2, 1), (3, 4), (5, 1), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_144383 : Nat.Prime 144383 := by
  apply nodeValid_prime [2, 7, 10313] ⟨144383, 5, [(2, 1), (7, 1), (10313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10313
  · decide +kernel

theorem prime_165463 : Nat.Prime 165463 := by
  apply nodeValid_prime [2, 3, 11, 23, 109] ⟨165463, 3, [(2, 1), (3, 1), (11, 1), (23, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_109
  · decide +kernel

theorem prime_216851 : Nat.Prime 216851 := by
  apply nodeValid_prime [2, 5, 4337] ⟨216851, 2, [(2, 1), (5, 2), (4337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4337
  · decide +kernel

theorem prime_252709 : Nat.Prime 252709 := by
  apply nodeValid_prime [2, 3, 21059] ⟨252709, 6, [(2, 2), (3, 1), (21059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21059
  · decide +kernel

theorem prime_282691 : Nat.Prime 282691 := by
  apply nodeValid_prime [2, 3, 5, 349] ⟨282691, 12, [(2, 1), (3, 4), (5, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_320839 : Nat.Prime 320839 := by
  apply nodeValid_prime [2, 3, 7, 7639] ⟨320839, 6, [(2, 1), (3, 1), (7, 1), (7639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7639
  · decide +kernel

theorem prime_326503 : Nat.Prime 326503 := by
  apply nodeValid_prime [2, 3, 11, 17, 97] ⟨326503, 3, [(2, 1), (3, 2), (11, 1), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_330899 : Nat.Prime 330899 := by
  apply nodeValid_prime [2, 165449] ⟨330899, 2, [(2, 1), (165449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_165449
  · decide +kernel

theorem prime_449249 : Nat.Prime 449249 := by
  apply nodeValid_prime [2, 101, 139] ⟨449249, 3, [(2, 5), (101, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_139
  · decide +kernel

theorem prime_455513 : Nat.Prime 455513 := by
  apply nodeValid_prime [2, 97, 587] ⟨455513, 3, [(2, 3), (97, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_587
  · decide +kernel

theorem prime_475649 : Nat.Prime 475649 := by
  apply nodeValid_prime [2, 929] ⟨475649, 3, [(2, 9), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_929
  · decide +kernel

theorem prime_546349 : Nat.Prime 546349 := by
  apply nodeValid_prime [2, 3, 11, 4139] ⟨546349, 2, [(2, 2), (3, 1), (11, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4139
  · decide +kernel

theorem prime_570463 : Nat.Prime 570463 := by
  apply nodeValid_prime [2, 3, 31, 3067] ⟨570463, 3, [(2, 1), (3, 1), (31, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3067
  · decide +kernel

theorem prime_580691 : Nat.Prime 580691 := by
  apply nodeValid_prime [2, 5, 11, 5279] ⟨580691, 2, [(2, 1), (5, 1), (11, 1), (5279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_5279
  · decide +kernel

theorem prime_631613 : Nat.Prime 631613 := by
  apply nodeValid_prime [2, 269, 587] ⟨631613, 2, [(2, 2), (269, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_587
  · decide +kernel

theorem prime_692453 : Nat.Prime 692453 := by
  apply nodeValid_prime [2, 331, 523] ⟨692453, 2, [(2, 2), (331, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_523
  · decide +kernel

theorem prime_702851 : Nat.Prime 702851 := by
  apply nodeValid_prime [2, 5, 14057] ⟨702851, 2, [(2, 1), (5, 2), (14057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14057
  · decide +kernel

theorem prime_1021837 : Nat.Prime 1021837 := by
  apply nodeValid_prime [2, 3, 17, 5009] ⟨1021837, 2, [(2, 2), (3, 1), (17, 1), (5009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_5009
  · decide +kernel

theorem prime_1219237 : Nat.Prime 1219237 := by
  apply nodeValid_prime [2, 3, 101603] ⟨1219237, 2, [(2, 2), (3, 1), (101603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101603
  · decide +kernel

theorem prime_1238621 : Nat.Prime 1238621 := by
  apply nodeValid_prime [2, 5, 17, 3643] ⟨1238621, 2, [(2, 2), (5, 1), (17, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_3643
  · decide +kernel

theorem prime_1537027 : Nat.Prime 1537027 := by
  apply nodeValid_prime [2, 3, 113, 2267] ⟨1537027, 2, [(2, 1), (3, 1), (113, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_2267
  · decide +kernel

theorem prime_1564933 : Nat.Prime 1564933 := by
  apply nodeValid_prime [2, 3, 130411] ⟨1564933, 2, [(2, 2), (3, 1), (130411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130411
  · decide +kernel

theorem prime_1749529 : Nat.Prime 1749529 := by
  apply nodeValid_prime [2, 3, 11, 47] ⟨1749529, 7, [(2, 3), (3, 2), (11, 1), (47, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_1782667 : Nat.Prime 1782667 := by
  apply nodeValid_prime [2, 3, 97, 1021] ⟨1782667, 3, [(2, 1), (3, 2), (97, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1021
  · decide +kernel

theorem prime_2033861 : Nat.Prime 2033861 := by
  apply nodeValid_prime [2, 5, 101693] ⟨2033861, 2, [(2, 2), (5, 1), (101693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101693
  · decide +kernel

theorem prime_2132387 : Nat.Prime 2132387 := by
  apply nodeValid_prime [2, 661, 1613] ⟨2132387, 2, [(2, 1), (661, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_661
    · exact prime_1613
  · decide +kernel

theorem prime_2285399 : Nat.Prime 2285399 := by
  apply nodeValid_prime [2, 811, 1409] ⟨2285399, 7, [(2, 1), (811, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_811
    · exact prime_1409
  · decide +kernel

theorem prime_2330389 : Nat.Prime 2330389 := by
  apply nodeValid_prime [2, 3, 19, 3407] ⟨2330389, 2, [(2, 2), (3, 2), (19, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3407
  · decide +kernel

theorem prime_2656889 : Nat.Prime 2656889 := by
  apply nodeValid_prime [2, 13, 59, 433] ⟨2656889, 3, [(2, 3), (13, 1), (59, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_59
    · exact prime_433
  · decide +kernel

theorem prime_2925893 : Nat.Prime 2925893 := by
  apply nodeValid_prime [2, 43, 17011] ⟨2925893, 2, [(2, 2), (43, 1), (17011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_17011
  · decide +kernel

theorem prime_3077251 : Nat.Prime 3077251 := by
  apply nodeValid_prime [2, 3, 5, 11, 373] ⟨3077251, 2, [(2, 1), (3, 1), (5, 3), (11, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_373
  · decide +kernel

theorem prime_3182293 : Nat.Prime 3182293 := by
  apply nodeValid_prime [2, 3, 88397] ⟨3182293, 2, [(2, 2), (3, 2), (88397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_88397
  · decide +kernel

theorem prime_3263189 : Nat.Prime 3263189 := by
  apply nodeValid_prime [2, 347, 2351] ⟨3263189, 2, [(2, 2), (347, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_2351
  · decide +kernel

theorem prime_3408983 : Nat.Prime 3408983 := by
  apply nodeValid_prime [2, 163, 10457] ⟨3408983, 5, [(2, 1), (163, 1), (10457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_10457
  · decide +kernel

theorem prime_4198349 : Nat.Prime 4198349 := by
  apply nodeValid_prime [2, 7, 11, 43, 317] ⟨4198349, 2, [(2, 2), (7, 1), (11, 1), (43, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_43
    · exact prime_317
  · decide +kernel

theorem prime_7370087 : Nat.Prime 7370087 := by
  apply nodeValid_prime [2, 113, 32611] ⟨7370087, 5, [(2, 1), (113, 1), (32611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_32611
  · decide +kernel

theorem prime_7715999 : Nat.Prime 7715999 := by
  apply nodeValid_prime [2, 1489, 2591] ⟨7715999, 7, [(2, 1), (1489, 1), (2591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1489
    · exact prime_2591
  · decide +kernel

theorem prime_7906277 : Nat.Prime 7906277 := by
  apply nodeValid_prime [2, 7, 41, 71, 97] ⟨7906277, 2, [(2, 2), (7, 1), (41, 1), (71, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_71
    · exact prime_97
  · decide +kernel

theorem prime_8244079 : Nat.Prime 8244079 := by
  apply nodeValid_prime [2, 3, 31, 127, 349] ⟨8244079, 3, [(2, 1), (3, 1), (31, 1), (127, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_127
    · exact prime_349
  · decide +kernel

theorem prime_9265213 : Nat.Prime 9265213 := by
  apply nodeValid_prime [2, 3, 11, 709] ⟨9265213, 2, [(2, 2), (3, 3), (11, 2), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_709
  · decide +kernel

theorem prime_10696003 : Nat.Prime 10696003 := by
  apply nodeValid_prime [2, 3, 1782667] ⟨10696003, 2, [(2, 1), (3, 1), (1782667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1782667
  · decide +kernel

theorem prime_10758677 : Nat.Prime 10758677 := by
  apply nodeValid_prime [2, 47, 89, 643] ⟨10758677, 2, [(2, 2), (47, 1), (89, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_89
    · exact prime_643
  · decide +kernel

theorem prime_12479549 : Nat.Prime 12479549 := by
  apply nodeValid_prime [2, 83, 37589] ⟨12479549, 2, [(2, 2), (83, 1), (37589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_37589
  · decide +kernel

theorem prime_13307057 : Nat.Prime 13307057 := by
  apply nodeValid_prime [2, 7, 17, 29, 241] ⟨13307057, 3, [(2, 4), (7, 1), (17, 1), (29, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_29
    · exact prime_241
  · decide +kernel

theorem prime_14444113 : Nat.Prime 14444113 := by
  apply nodeValid_prime [2, 3, 113, 2663] ⟨14444113, 5, [(2, 4), (3, 1), (113, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_2663
  · decide +kernel

theorem prime_17184511 : Nat.Prime 17184511 := by
  apply nodeValid_prime [2, 3, 5, 7, 27277] ⟨17184511, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (27277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_27277
  · decide +kernel

theorem prime_18099661 : Nat.Prime 18099661 := by
  apply nodeValid_prime [2, 3, 5, 31, 37, 263] ⟨18099661, 2, [(2, 2), (3, 1), (5, 1), (31, 1), (37, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_37
    · exact prime_263
  · decide +kernel

theorem prime_25646947 : Nat.Prime 25646947 := by
  apply nodeValid_prime [2, 3, 13, 59, 5573] ⟨25646947, 3, [(2, 1), (3, 1), (13, 1), (59, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_5573
  · decide +kernel

theorem prime_29502919 : Nat.Prime 29502919 := by
  apply nodeValid_prime [2, 3, 29, 56519] ⟨29502919, 3, [(2, 1), (3, 2), (29, 1), (56519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_56519
  · decide +kernel

theorem prime_31171069 : Nat.Prime 31171069 := by
  apply nodeValid_prime [2, 3, 32069] ⟨31171069, 2, [(2, 2), (3, 5), (32069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32069
  · decide +kernel

theorem prime_38489639 : Nat.Prime 38489639 := by
  apply nodeValid_prime [2, 11, 1749529] ⟨38489639, 11, [(2, 1), (11, 1), (1749529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1749529
  · decide +kernel

theorem prime_38841703 : Nat.Prime 38841703 := by
  apply nodeValid_prime [2, 3, 17, 197, 1933] ⟨38841703, 5, [(2, 1), (3, 1), (17, 1), (197, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_197
    · exact prime_1933
  · decide +kernel

theorem prime_65843053 : Nat.Prime 65843053 := by
  apply nodeValid_prime [2, 3, 11, 47, 10613] ⟨65843053, 2, [(2, 2), (3, 1), (11, 1), (47, 1), (10613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_10613
  · decide +kernel

theorem prime_117717011 : Nat.Prime 117717011 := by
  apply nodeValid_prime [2, 5, 17, 692453] ⟨117717011, 2, [(2, 1), (5, 1), (17, 1), (692453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_692453
  · decide +kernel

theorem prime_124684277 : Nat.Prime 124684277 := by
  apply nodeValid_prime [2, 31171069] ⟨124684277, 2, [(2, 2), (31171069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31171069
  · decide +kernel

theorem prime_153881683 : Nat.Prime 153881683 := by
  apply nodeValid_prime [2, 3, 25646947] ⟨153881683, 2, [(2, 1), (3, 1), (25646947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25646947
  · decide +kernel

theorem prime_180996611 : Nat.Prime 180996611 := by
  apply nodeValid_prime [2, 5, 18099661] ⟨180996611, 2, [(2, 1), (5, 1), (18099661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18099661
  · decide +kernel

theorem prime_231479971 : Nat.Prime 231479971 := by
  apply nodeValid_prime [2, 3, 5, 7715999] ⟨231479971, 3, [(2, 1), (3, 1), (5, 1), (7715999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7715999
  · decide +kernel

theorem prime_673895647 : Nat.Prime 673895647 := by
  apply nodeValid_prime [2, 3, 12479549] ⟨673895647, 3, [(2, 1), (3, 3), (12479549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12479549
  · decide +kernel

theorem prime_1026964087 : Nat.Prime 1026964087 := by
  apply nodeValid_prime [2, 3, 6053, 28277] ⟨1026964087, 3, [(2, 1), (3, 1), (6053, 1), (28277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6053
    · exact prime_28277
  · decide +kernel

theorem prime_2374512667 : Nat.Prime 2374512667 := by
  apply nodeValid_prime [2, 3, 37, 10696003] ⟨2374512667, 2, [(2, 1), (3, 1), (37, 1), (10696003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_10696003
  · decide +kernel

theorem prime_2995581907 : Nat.Prime 2995581907 := by
  apply nodeValid_prime [2, 3, 1409, 39371] ⟨2995581907, 13, [(2, 1), (3, 3), (1409, 1), (39371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1409
    · exact prime_39371
  · decide +kernel

theorem prime_3298825147 : Nat.Prime 3298825147 := by
  apply nodeValid_prime [2, 3, 17, 71, 455513] ⟨3298825147, 2, [(2, 1), (3, 1), (17, 1), (71, 1), (455513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_71
    · exact prime_455513
  · decide +kernel

theorem prime_3834191323 : Nat.Prime 3834191323 := by
  apply nodeValid_prime [2, 3, 13, 17, 18899] ⟨3834191323, 2, [(2, 1), (3, 3), (13, 1), (17, 2), (18899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_18899
  · decide +kernel

theorem prime_4987371079 : Nat.Prime 4987371079 := by
  apply nodeValid_prime [2, 3, 31, 2467, 3623] ⟨4987371079, 6, [(2, 1), (3, 2), (31, 1), (2467, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2467
    · exact prime_3623
  · decide +kernel

theorem prime_6413186621 : Nat.Prime 6413186621 := by
  apply nodeValid_prime [2, 5, 263, 1219237] ⟨6413186621, 2, [(2, 2), (5, 1), (263, 1), (1219237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
    · exact prime_1219237
  · decide +kernel

theorem prime_6494275003 : Nat.Prime 6494275003 := by
  apply nodeValid_prime [2, 3, 31, 37, 71, 13291] ⟨6494275003, 3, [(2, 1), (3, 1), (31, 1), (37, 1), (71, 1), (13291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_37
    · exact prime_71
    · exact prime_13291
  · decide +kernel

theorem prime_7271377903 : Nat.Prime 7271377903 := by
  apply nodeValid_prime [2, 3, 1429, 282691] ⟨7271377903, 5, [(2, 1), (3, 2), (1429, 1), (282691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1429
    · exact prime_282691
  · decide +kernel

theorem prime_10138792033 : Nat.Prime 10138792033 := by
  apply nodeValid_prime [2, 3, 16097] ⟨10138792033, 5, [(2, 5), (3, 9), (16097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16097
  · decide +kernel

theorem prime_10518043919 : Nat.Prime 10518043919 := by
  apply nodeValid_prime [2, 1709, 3077251] ⟨10518043919, 11, [(2, 1), (1709, 1), (3077251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1709
    · exact prime_3077251
  · decide +kernel

theorem prime_10813292129 : Nat.Prime 10813292129 := by
  apply nodeValid_prime [2, 23, 269, 54617] ⟨10813292129, 3, [(2, 5), (23, 1), (269, 1), (54617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_269
    · exact prime_54617
  · decide +kernel

theorem prime_19589938217 : Nat.Prime 19589938217 := by
  apply nodeValid_prime [2, 83, 29502919] ⟨19589938217, 3, [(2, 3), (83, 1), (29502919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_29502919
  · decide +kernel

theorem prime_40501274789 : Nat.Prime 40501274789 := by
  apply nodeValid_prime [2, 13, 53, 3673, 4001] ⟨40501274789, 2, [(2, 2), (13, 1), (53, 1), (3673, 1), (4001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_3673
    · exact prime_4001
  · decide +kernel

theorem prime_54066461753 : Nat.Prime 54066461753 := by
  apply nodeValid_prime [2, 4397, 1537027] ⟨54066461753, 3, [(2, 3), (4397, 1), (1537027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4397
    · exact prime_1537027
  · decide +kernel

theorem prime_57649056769 : Nat.Prime 57649056769 := by
  apply nodeValid_prime [2, 3, 193, 32411] ⟨57649056769, 7, [(2, 10), (3, 2), (193, 1), (32411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_32411
  · decide +kernel

theorem prime_70630206601 : Nat.Prime 70630206601 := by
  apply nodeValid_prime [2, 3, 5, 117717011] ⟨70630206601, 14, [(2, 3), (3, 1), (5, 2), (117717011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_117717011
  · decide +kernel

theorem prime_107873980133 : Nat.Prime 107873980133 := by
  apply nodeValid_prime [2, 21773, 1238621] ⟨107873980133, 2, [(2, 2), (21773, 1), (1238621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21773
    · exact prime_1238621
  · decide +kernel

theorem prime_128056736023 : Nat.Prime 128056736023 := by
  apply nodeValid_prime [2, 3, 29, 277, 2656889] ⟨128056736023, 5, [(2, 1), (3, 1), (29, 1), (277, 1), (2656889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_277
    · exact prime_2656889
  · decide +kernel

theorem prime_128365194259 : Nat.Prime 128365194259 := by
  apply nodeValid_prime [2, 3, 7, 31, 1564933] ⟨128365194259, 2, [(2, 1), (3, 3), (7, 2), (31, 1), (1564933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_1564933
  · decide +kernel

theorem prime_211635143677 : Nat.Prime 211635143677 := by
  apply nodeValid_prime [2, 3, 11, 37, 14444113] ⟨211635143677, 2, [(2, 2), (3, 2), (11, 1), (37, 1), (14444113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_14444113
  · decide +kernel

theorem prime_632609877593 : Nat.Prime 632609877593 := by
  apply nodeValid_prime [2, 7, 11, 1026964087] ⟨632609877593, 3, [(2, 3), (7, 1), (11, 1), (1026964087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1026964087
  · decide +kernel

theorem prime_638743910771 : Nat.Prime 638743910771 := by
  apply nodeValid_prime [2, 5, 7, 14447, 631613] ⟨638743910771, 2, [(2, 1), (5, 1), (7, 1), (14447, 1), (631613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_14447
    · exact prime_631613
  · decide +kernel

theorem prime_640283678213 : Nat.Prime 640283678213 := by
  apply nodeValid_prime [2, 37, 587, 7370087] ⟨640283678213, 2, [(2, 2), (37, 1), (587, 1), (7370087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_587
    · exact prime_7370087
  · decide +kernel

theorem prime_641054528099 : Nat.Prime 641054528099 := by
  apply nodeValid_prime [2, 107, 2995581907] ⟨641054528099, 2, [(2, 1), (107, 1), (2995581907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_2995581907
  · decide +kernel

theorem prime_645692755439 : Nat.Prime 645692755439 := by
  apply nodeValid_prime [2, 39161, 8244079] ⟨645692755439, 7, [(2, 1), (39161, 1), (8244079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_39161
    · exact prime_8244079
  · decide +kernel

theorem prime_646467960863 : Nat.Prime 646467960863 := by
  apply nodeValid_prime [2, 521, 2861, 216851] ⟨646467960863, 5, [(2, 1), (521, 1), (2861, 1), (216851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_521
    · exact prime_2861
    · exact prime_216851
  · decide +kernel

theorem prime_1260639913607 : Nat.Prime 1260639913607 := by
  apply nodeValid_prime [2, 41, 4831, 3182293] ⟨1260639913607, 5, [(2, 1), (41, 1), (4831, 1), (3182293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_4831
    · exact prime_3182293
  · decide +kernel

theorem prime_1260639922067 : Nat.Prime 1260639922067 := by
  apply nodeValid_prime [2, 7, 389, 231479971] ⟨1260639922067, 2, [(2, 1), (7, 1), (389, 1), (231479971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_389
    · exact prime_231479971
  · decide +kernel

theorem prime_1260639922189 : Nat.Prime 1260639922189 := by
  apply nodeValid_prime [2, 3, 47, 101, 367, 1283] ⟨1260639922189, 2, [(2, 2), (3, 1), (47, 2), (101, 1), (367, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_101
    · exact prime_367
    · exact prime_1283
  · decide +kernel

theorem prime_1262165225317 : Nat.Prime 1262165225317 := by
  apply nodeValid_prime [2, 3, 29, 79, 509, 90197] ⟨1262165225317, 6, [(2, 2), (3, 1), (29, 1), (79, 1), (509, 1), (90197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_79
    · exact prime_509
    · exact prime_90197
  · decide +kernel

theorem prime_1262165225729 : Nat.Prime 1262165225729 := by
  apply nodeValid_prime [2, 11, 127, 320839] ⟨1262165225729, 3, [(2, 8), (11, 2), (127, 1), (320839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_320839
  · decide +kernel

theorem prime_1262165270281 : Nat.Prime 1262165270281 := by
  apply nodeValid_prime [2, 3, 5, 10518043919] ⟨1262165270281, 7, [(2, 3), (3, 1), (5, 1), (10518043919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10518043919
  · decide +kernel

theorem prime_1263691826461 : Nat.Prime 1263691826461 := by
  apply nodeValid_prime [2, 3, 5, 7, 823, 135403] ⟨1263691826461, 2, [(2, 2), (3, 4), (5, 1), (7, 1), (823, 1), (135403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_823
    · exact prime_135403
  · decide +kernel

theorem prime_1263691827649 : Nat.Prime 1263691827649 := by
  apply nodeValid_prime [2, 3, 19, 38489639] ⟨1263691827649, 7, [(2, 6), (3, 3), (19, 1), (38489639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_38489639
  · decide +kernel

theorem prime_1263691878019 : Nat.Prime 1263691878019 := by
  apply nodeValid_prime [2, 3, 17, 1567, 7906277] ⟨1263691878019, 2, [(2, 1), (3, 1), (17, 1), (1567, 1), (7906277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1567
    · exact prime_7906277
  · decide +kernel

theorem prime_1265219740391 : Nat.Prime 1265219740391 := by
  apply nodeValid_prime [2, 5, 23, 29, 83, 2285399] ⟨1265219740391, 23, [(2, 1), (5, 1), (23, 1), (29, 1), (83, 1), (2285399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_29
    · exact prime_83
    · exact prime_2285399
  · decide +kernel

theorem prime_1265219755123 : Nat.Prime 1265219755123 := by
  apply nodeValid_prime [2, 3, 29, 7271377903] ⟨1265219755123, 2, [(2, 1), (3, 1), (29, 1), (7271377903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_7271377903
  · decide +kernel

theorem prime_1265219755187 : Nat.Prime 1265219755187 := by
  apply nodeValid_prime [2, 632609877593] ⟨1265219755187, 2, [(2, 1), (632609877593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_632609877593
  · decide +kernel

theorem prime_1266748848289 : Nat.Prime 1266748848289 := by
  apply nodeValid_prime [2, 3, 7, 11, 233, 35023] ⟨1266748848289, 17, [(2, 5), (3, 2), (7, 2), (11, 1), (233, 1), (35023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_233
    · exact prime_35023
  · decide +kernel

theorem prime_1266748848487 : Nat.Prime 1266748848487 := by
  apply nodeValid_prime [2, 3, 11, 2087, 1021837] ⟨1266748848487, 5, [(2, 1), (3, 3), (11, 1), (2087, 1), (1021837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2087
    · exact prime_1021837
  · decide +kernel

theorem prime_1266748856449 : Nat.Prime 1266748856449 := by
  apply nodeValid_prime [2, 3, 3298825147] ⟨1266748856449, 7, [(2, 7), (3, 1), (3298825147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3298825147
  · decide +kernel

theorem prime_1268279231987 : Nat.Prime 1268279231987 := by
  apply nodeValid_prime [2, 13, 271, 317, 349, 1627] ⟨1268279231987, 2, [(2, 1), (13, 1), (271, 1), (317, 1), (349, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_271
    · exact prime_317
    · exact prime_349
    · exact prime_1627
  · decide +kernel

theorem prime_1268279248919 : Nat.Prime 1268279248919 := by
  apply nodeValid_prime [2, 11, 57649056769] ⟨1268279248919, 7, [(2, 1), (11, 1), (57649056769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_57649056769
  · decide +kernel

theorem prime_1268279249411 : Nat.Prime 1268279249411 := by
  apply nodeValid_prime [2, 5, 17, 1777, 4198349] ⟨1268279249411, 2, [(2, 1), (5, 1), (17, 1), (1777, 1), (4198349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1777
    · exact prime_4198349
  · decide +kernel

theorem prime_1269810862063 : Nat.Prime 1269810862063 := by
  apply nodeValid_prime [2, 3, 211635143677] ⟨1269810862063, 7, [(2, 1), (3, 1), (211635143677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211635143677
  · decide +kernel

theorem prime_1269810950959 : Nat.Prime 1269810950959 := by
  apply nodeValid_prime [2, 3, 11, 6413186621] ⟨1269810950959, 3, [(2, 1), (3, 2), (11, 1), (6413186621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6413186621
  · decide +kernel

theorem prime_1269810951281 : Nat.Prime 1269810951281 := by
  apply nodeValid_prime [2, 5, 17, 479, 114661] ⟨1269810951281, 6, [(2, 4), (5, 1), (17, 2), (479, 1), (114661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_479
    · exact prime_114661
  · decide +kernel

theorem prime_1271343718819 : Nat.Prime 1271343718819 := by
  apply nodeValid_prime [2, 3, 70630206601] ⟨1271343718819, 2, [(2, 1), (3, 2), (70630206601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_70630206601
  · decide +kernel

theorem prime_1271343718951 : Nat.Prime 1271343718951 := by
  apply nodeValid_prime [2, 3, 5, 3637, 2330389] ⟨1271343718951, 6, [(2, 1), (3, 1), (5, 2), (3637, 1), (2330389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3637
    · exact prime_2330389
  · decide +kernel

theorem prime_1271343738911 : Nat.Prime 1271343738911 := by
  apply nodeValid_prime [2, 5, 7, 7841, 330899] ⟨1271343738911, 7, [(2, 1), (5, 1), (7, 2), (7841, 1), (330899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7841
    · exact prime_330899
  · decide +kernel

theorem prime_1272877866961 : Nat.Prime 1272877866961 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 1453, 17981] ⟨1272877866961, 11, [(2, 4), (3, 1), (5, 1), (7, 1), (29, 1), (1453, 1), (17981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_1453
    · exact prime_17981
  · decide +kernel

theorem prime_1272877900589 : Nat.Prime 1272877900589 := by
  apply nodeValid_prime [2, 7, 6494275003] ⟨1272877900589, 2, [(2, 2), (7, 2), (6494275003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6494275003
  · decide +kernel

theorem prime_1272877900597 : Nat.Prime 1272877900597 := by
  apply nodeValid_prime [2, 3, 179, 65843053] ⟨1272877900597, 2, [(2, 2), (3, 3), (179, 1), (65843053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_65843053
  · decide +kernel

theorem prime_1274413234153 : Nat.Prime 1274413234153 := by
  apply nodeValid_prime [2, 3, 61, 5261, 165463] ⟨1274413234153, 7, [(2, 3), (3, 1), (61, 1), (5261, 1), (165463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_5261
    · exact prime_165463
  · decide +kernel

theorem prime_1274413234879 : Nat.Prime 1274413234879 := by
  apply nodeValid_prime [2, 3, 7, 4973, 2033861] ⟨1274413234879, 3, [(2, 1), (3, 2), (7, 1), (4973, 1), (2033861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4973
    · exact prime_2033861
  · decide +kernel

theorem prime_1274413250417 : Nat.Prime 1274413250417 := by
  apply nodeValid_prime [2, 1217, 6473, 10111] ⟨1274413250417, 3, [(2, 4), (1217, 1), (6473, 1), (10111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1217
    · exact prime_6473
    · exact prime_10111
  · decide +kernel

theorem prime_1275949896769 : Nat.Prime 1275949896769 := by
  apply nodeValid_prime [2, 3, 47, 223, 70451] ⟨1275949896769, 26, [(2, 6), (3, 3), (47, 1), (223, 1), (70451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_223
    · exact prime_70451
  · decide +kernel

theorem prime_1275949941751 : Nat.Prime 1275949941751 := by
  apply nodeValid_prime [2, 3, 5, 11, 17184511] ⟨1275949941751, 3, [(2, 1), (3, 3), (5, 3), (11, 1), (17184511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17184511
  · decide +kernel

theorem prime_1275949943551 : Nat.Prime 1275949943551 := by
  apply nodeValid_prime [2, 3, 5, 73, 38841703] ⟨1275949943551, 3, [(2, 1), (3, 2), (5, 2), (73, 1), (38841703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_38841703
  · decide +kernel

theorem prime_1277487796159 : Nat.Prime 1277487796159 := by
  apply nodeValid_prime [2, 3, 7, 10138792033] ⟨1277487796159, 3, [(2, 1), (3, 2), (7, 1), (10138792033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10138792033
  · decide +kernel

theorem prime_1277487814847 : Nat.Prime 1277487814847 := by
  apply nodeValid_prime [2, 269, 2374512667] ⟨1277487814847, 5, [(2, 1), (269, 1), (2374512667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_2374512667
  · decide +kernel

theorem prime_1277487821543 : Nat.Prime 1277487821543 := by
  apply nodeValid_prime [2, 638743910771] ⟨1277487821543, 5, [(2, 1), (638743910771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_638743910771
  · decide +kernel

theorem prime_1279026951931 : Nat.Prime 1279026951931 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 4861, 10709] ⟨1279026951931, 7, [(2, 1), (3, 3), (5, 1), (7, 1), (13, 1), (4861, 1), (10709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_4861
    · exact prime_10709
  · decide +kernel

theorem prime_1279027046471 : Nat.Prime 1279027046471 := by
  apply nodeValid_prime [2, 5, 59981, 2132387] ⟨1279027046471, 11, [(2, 1), (5, 1), (59981, 1), (2132387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59981
    · exact prime_2132387
  · decide +kernel

theorem prime_1279027048357 : Nat.Prime 1279027048357 := by
  apply nodeValid_prime [2, 3, 65029, 546349] ⟨1279027048357, 5, [(2, 2), (3, 2), (65029, 1), (546349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_65029
    · exact prime_546349
  · decide +kernel

theorem prime_1280567355919 : Nat.Prime 1280567355919 := by
  apply nodeValid_prime [2, 3, 157, 2383, 570463] ⟨1280567355919, 3, [(2, 1), (3, 1), (157, 1), (2383, 1), (570463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_2383
    · exact prime_570463
  · decide +kernel

theorem prime_1280567356427 : Nat.Prime 1280567356427 := by
  apply nodeValid_prime [2, 640283678213] ⟨1280567356427, 2, [(2, 1), (640283678213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_640283678213
  · decide +kernel

theorem prime_1280567360231 : Nat.Prime 1280567360231 := by
  apply nodeValid_prime [2, 5, 128056736023] ⟨1280567360231, 11, [(2, 1), (5, 1), (128056736023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_128056736023
  · decide +kernel

theorem prime_1282109025607 : Nat.Prime 1282109025607 := by
  apply nodeValid_prime [2, 3, 449249, 475649] ⟨1282109025607, 3, [(2, 1), (3, 1), (449249, 1), (475649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449249
    · exact prime_475649
  · decide +kernel

theorem prime_1282109056199 : Nat.Prime 1282109056199 := by
  apply nodeValid_prime [2, 641054528099] ⟨1282109056199, 11, [(2, 1), (641054528099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_641054528099
  · decide +kernel

theorem prime_1282109056337 : Nat.Prime 1282109056337 := by
  apply nodeValid_prime [2, 31, 53, 2027, 24061] ⟨1282109056337, 3, [(2, 4), (31, 1), (53, 1), (2027, 1), (24061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_53
    · exact prime_2027
    · exact prime_24061
  · decide +kernel

theorem prime_1283651942591 : Nat.Prime 1283651942591 := by
  apply nodeValid_prime [2, 5, 128365194259] ⟨1283651942591, 7, [(2, 1), (5, 1), (128365194259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_128365194259
  · decide +kernel

theorem prime_1283651946449 : Nat.Prime 1283651946449 := by
  apply nodeValid_prime [2, 6029, 13307057] ⟨1283651946449, 3, [(2, 4), (6029, 1), (13307057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6029
    · exact prime_13307057
  · decide +kernel

theorem prime_1283651946637 : Nat.Prime 1283651946637 := by
  apply nodeValid_prime [2, 3, 43, 27527, 90373] ⟨1283651946637, 2, [(2, 2), (3, 1), (43, 1), (27527, 1), (90373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_27527
    · exact prime_90373
  · decide +kernel

theorem prime_1285196127739 : Nat.Prime 1285196127739 := by
  apply nodeValid_prime [2, 3, 41, 16001, 326503] ⟨1285196127739, 2, [(2, 1), (3, 1), (41, 1), (16001, 1), (326503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_16001
    · exact prime_326503
  · decide +kernel

theorem prime_1285196225141 : Nat.Prime 1285196225141 := by
  apply nodeValid_prime [2, 5, 53, 97, 3343, 3739] ⟨1285196225141, 2, [(2, 2), (5, 1), (53, 1), (97, 1), (3343, 1), (3739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_97
    · exact prime_3343
    · exact prime_3739
  · decide +kernel

theorem prime_1285196225657 : Nat.Prime 1285196225657 := by
  apply nodeValid_prime [2, 7, 2477, 9265213] ⟨1285196225657, 5, [(2, 3), (7, 1), (2477, 1), (9265213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2477
    · exact prime_9265213
  · decide +kernel

theorem prime_1286741573081 : Nat.Prime 1286741573081 := by
  apply nodeValid_prime [2, 5, 31, 1787, 580691] ⟨1286741573081, 3, [(2, 3), (5, 1), (31, 1), (1787, 1), (580691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1787
    · exact prime_580691
  · decide +kernel

theorem prime_1286741738383 : Nat.Prime 1286741738383 := by
  apply nodeValid_prime [2, 3, 43, 4987371079] ⟨1286741738383, 3, [(2, 1), (3, 1), (43, 1), (4987371079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_4987371079
  · decide +kernel

theorem prime_1286741738641 : Nat.Prime 1286741738641 := by
  apply nodeValid_prime [2, 3, 5, 43, 124684277] ⟨1286741738641, 19, [(2, 4), (3, 1), (5, 1), (43, 1), (124684277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_124684277
  · decide +kernel

theorem prime_1288288243259 : Nat.Prime 1288288243259 := by
  apply nodeValid_prime [2, 19, 11587, 2925893] ⟨1288288243259, 2, [(2, 1), (19, 1), (11587, 1), (2925893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_11587
    · exact prime_2925893
  · decide +kernel

theorem prime_1288288243609 : Nat.Prime 1288288243609 := by
  apply nodeValid_prime [2, 3, 311, 683, 252709] ⟨1288288243609, 14, [(2, 3), (3, 1), (311, 1), (683, 1), (252709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_683
    · exact prime_252709
  · decide +kernel

theorem prime_1288288284529 : Nat.Prime 1288288284529 := by
  apply nodeValid_prime [2, 3, 7, 3834191323] ⟨1288288284529, 17, [(2, 4), (3, 1), (7, 1), (3834191323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3834191323
  · decide +kernel

theorem prime_1289836266907 : Nat.Prime 1289836266907 := by
  apply nodeValid_prime [2, 3, 11, 127, 153881683] ⟨1289836266907, 3, [(2, 1), (3, 1), (11, 1), (127, 1), (153881683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_127
    · exact prime_153881683
  · decide +kernel

theorem prime_1289836268177 : Nat.Prime 1289836268177 := by
  apply nodeValid_prime [2, 59, 127, 10758677] ⟨1289836268177, 3, [(2, 4), (59, 1), (127, 1), (10758677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_127
    · exact prime_10758677
  · decide +kernel

theorem prime_1289836268359 : Nat.Prime 1289836268359 := by
  apply nodeValid_prime [2, 3, 11, 29, 673895647] ⟨1289836268359, 3, [(2, 1), (3, 1), (11, 1), (29, 1), (673895647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_673895647
  · decide +kernel

theorem prime_1291385510879 : Nat.Prime 1291385510879 := by
  apply nodeValid_prime [2, 645692755439] ⟨1291385510879, 7, [(2, 1), (645692755439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_645692755439
  · decide +kernel

theorem prime_1291385519579 : Nat.Prime 1291385519579 := by
  apply nodeValid_prime [2, 7, 11, 8297, 144383] ⟨1291385519579, 6, [(2, 1), (7, 2), (11, 1), (8297, 1), (144383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_8297
    · exact prime_144383
  · decide +kernel

theorem prime_1291385520389 : Nat.Prime 1291385520389 := by
  apply nodeValid_prime [2, 877, 5821, 63241] ⟨1291385520389, 2, [(2, 2), (877, 1), (5821, 1), (63241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_877
    · exact prime_5821
    · exact prime_63241
  · decide +kernel

theorem prime_1292935921727 : Nat.Prime 1292935921727 := by
  apply nodeValid_prime [2, 646467960863] ⟨1292935921727, 5, [(2, 1), (646467960863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_646467960863
  · decide +kernel

theorem prime_1292935922323 : Nat.Prime 1292935922323 := by
  apply nodeValid_prime [2, 3, 11, 19589938217] ⟨1292935922323, 2, [(2, 1), (3, 1), (11, 1), (19589938217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19589938217
  · decide +kernel

theorem prime_1292936004299 : Nat.Prime 1292936004299 := by
  apply nodeValid_prime [2, 337, 21407, 89611] ⟨1292936004299, 2, [(2, 1), (337, 1), (21407, 1), (89611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_21407
    · exact prime_89611
  · decide +kernel

theorem prime_1294487759029 : Nat.Prime 1294487759029 := by
  apply nodeValid_prime [2, 3, 29, 59, 3011, 20939] ⟨1294487759029, 2, [(2, 2), (3, 1), (29, 1), (59, 1), (3011, 1), (20939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_59
    · exact prime_3011
    · exact prime_20939
  · decide +kernel

theorem prime_1294487761597 : Nat.Prime 1294487761597 := by
  apply nodeValid_prime [2, 3, 107873980133] ⟨1294487761597, 2, [(2, 2), (3, 1), (107873980133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107873980133
  · decide +kernel

theorem prime_1294487761873 : Nat.Prime 1294487761873 := by
  apply nodeValid_prime [2, 3, 149, 180996611] ⟨1294487761873, 5, [(2, 4), (3, 1), (149, 1), (180996611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_180996611
  · decide +kernel

theorem prime_1296040775131 : Nat.Prime 1296040775131 := by
  apply nodeValid_prime [2, 3, 5, 1471, 3263189] ⟨1296040775131, 7, [(2, 1), (3, 3), (5, 1), (1471, 1), (3263189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1471
    · exact prime_3263189
  · decide +kernel

theorem prime_1296040792873 : Nat.Prime 1296040792873 := by
  apply nodeValid_prime [2, 3, 7, 31, 73, 3408983] ⟨1296040792873, 5, [(2, 3), (3, 1), (7, 1), (31, 1), (73, 1), (3408983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_73
    · exact prime_3408983
  · decide +kernel

theorem prime_1296040793249 : Nat.Prime 1296040793249 := by
  apply nodeValid_prime [2, 40501274789] ⟨1296040793249, 3, [(2, 5), (40501274789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40501274789
  · decide +kernel

theorem prime_1297595055481 : Nat.Prime 1297595055481 := by
  apply nodeValid_prime [2, 3, 5, 10813292129] ⟨1297595055481, 11, [(2, 3), (3, 1), (5, 1), (10813292129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10813292129
  · decide +kernel

theorem prime_1297595081989 : Nat.Prime 1297595081989 := by
  apply nodeValid_prime [2, 3, 51283, 702851] ⟨1297595081989, 2, [(2, 2), (3, 2), (51283, 1), (702851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51283
    · exact prime_702851
  · decide +kernel

theorem prime_1297595082073 : Nat.Prime 1297595082073 := by
  apply nodeValid_prime [2, 3, 54066461753] ⟨1297595082073, 5, [(2, 3), (3, 1), (54066461753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54066461753
  · decide +kernel

end Sude.Lucas.Generated
