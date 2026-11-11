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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0103

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10037 : Nat.Prime 10037 := by
  apply nodeValid_prime [2, 13, 193] ⟨10037, 2, [(2, 2), (13, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_193
  · decide +kernel

theorem prime_10867 : Nat.Prime 10867 := by
  apply nodeValid_prime [2, 3, 1811] ⟨10867, 2, [(2, 1), (3, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1811
  · decide +kernel

theorem prime_13499 : Nat.Prime 13499 := by
  apply nodeValid_prime [2, 17, 397] ⟨13499, 6, [(2, 1), (17, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_397
  · decide +kernel

theorem prime_14543 : Nat.Prime 14543 := by
  apply nodeValid_prime [2, 11, 661] ⟨14543, 5, [(2, 1), (11, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_661
  · decide +kernel

theorem prime_17713 : Nat.Prime 17713 := by
  apply nodeValid_prime [2, 3, 41] ⟨17713, 7, [(2, 4), (3, 3), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_22639 : Nat.Prime 22639 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨22639, 6, [(2, 1), (3, 1), (7, 3), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_25447 : Nat.Prime 25447 := by
  apply nodeValid_prime [2, 3, 4241] ⟨25447, 3, [(2, 1), (3, 1), (4241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4241
  · decide +kernel

theorem prime_33581 : Nat.Prime 33581 := by
  apply nodeValid_prime [2, 5, 23, 73] ⟨33581, 2, [(2, 2), (5, 1), (23, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_73
  · decide +kernel

theorem prime_42743 : Nat.Prime 42743 := by
  apply nodeValid_prime [2, 7, 43, 71] ⟨42743, 7, [(2, 1), (7, 1), (43, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_71
  · decide +kernel

theorem prime_45943 : Nat.Prime 45943 := by
  apply nodeValid_prime [2, 3, 13, 19, 31] ⟨45943, 6, [(2, 1), (3, 1), (13, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_50707 : Nat.Prime 50707 := by
  apply nodeValid_prime [2, 3, 313] ⟨50707, 3, [(2, 1), (3, 4), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
  · decide +kernel

theorem prime_52363 : Nat.Prime 52363 := by
  apply nodeValid_prime [2, 3, 2909] ⟨52363, 5, [(2, 1), (3, 2), (2909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2909
  · decide +kernel

theorem prime_53951 : Nat.Prime 53951 := by
  apply nodeValid_prime [2, 5, 13, 83] ⟨53951, 7, [(2, 1), (5, 2), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_61031 : Nat.Prime 61031 := by
  apply nodeValid_prime [2, 5, 17, 359] ⟨61031, 22, [(2, 1), (5, 1), (17, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_359
  · decide +kernel

theorem prime_61673 : Nat.Prime 61673 := by
  apply nodeValid_prime [2, 13, 593] ⟨61673, 5, [(2, 3), (13, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_593
  · decide +kernel

theorem prime_66797 : Nat.Prime 66797 := by
  apply nodeValid_prime [2, 16699] ⟨66797, 2, [(2, 2), (16699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16699
  · decide +kernel

theorem prime_74761 : Nat.Prime 74761 := by
  apply nodeValid_prime [2, 3, 5, 7, 89] ⟨74761, 19, [(2, 3), (3, 1), (5, 1), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_76091 : Nat.Prime 76091 := by
  apply nodeValid_prime [2, 5, 7, 1087] ⟨76091, 2, [(2, 1), (5, 1), (7, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1087
  · decide +kernel

theorem prime_78341 : Nat.Prime 78341 := by
  apply nodeValid_prime [2, 5, 3917] ⟨78341, 2, [(2, 2), (5, 1), (3917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3917
  · decide +kernel

theorem prime_82781 : Nat.Prime 82781 := by
  apply nodeValid_prime [2, 5, 4139] ⟨82781, 2, [(2, 2), (5, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4139
  · decide +kernel

theorem prime_85487 : Nat.Prime 85487 := by
  apply nodeValid_prime [2, 42743] ⟨85487, 5, [(2, 1), (42743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42743
  · decide +kernel

theorem prime_87877 : Nat.Prime 87877 := by
  apply nodeValid_prime [2, 3, 2441] ⟨87877, 2, [(2, 2), (3, 2), (2441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2441
  · decide +kernel

theorem prime_95869 : Nat.Prime 95869 := by
  apply nodeValid_prime [2, 3, 2663] ⟨95869, 6, [(2, 2), (3, 2), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2663
  · decide +kernel

theorem prime_102611 : Nat.Prime 102611 := by
  apply nodeValid_prime [2, 5, 31, 331] ⟨102611, 2, [(2, 1), (5, 1), (31, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_331
  · decide +kernel

theorem prime_118409 : Nat.Prime 118409 := by
  apply nodeValid_prime [2, 19, 41] ⟨118409, 3, [(2, 3), (19, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_131591 : Nat.Prime 131591 := by
  apply nodeValid_prime [2, 5, 13159] ⟨131591, 11, [(2, 1), (5, 1), (13159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13159
  · decide +kernel

theorem prime_132329 : Nat.Prime 132329 := by
  apply nodeValid_prime [2, 7, 17, 139] ⟨132329, 3, [(2, 3), (7, 1), (17, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_139
  · decide +kernel

theorem prime_141461 : Nat.Prime 141461 := by
  apply nodeValid_prime [2, 5, 11, 643] ⟨141461, 7, [(2, 2), (5, 1), (11, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_643
  · decide +kernel

theorem prime_152183 : Nat.Prime 152183 := by
  apply nodeValid_prime [2, 76091] ⟨152183, 5, [(2, 1), (76091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76091
  · decide +kernel

theorem prime_156683 : Nat.Prime 156683 := by
  apply nodeValid_prime [2, 78341] ⟨156683, 2, [(2, 1), (78341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_78341
  · decide +kernel

theorem prime_168449 : Nat.Prime 168449 := by
  apply nodeValid_prime [2, 7, 47] ⟨168449, 3, [(2, 9), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_169093 : Nat.Prime 169093 := by
  apply nodeValid_prime [2, 3, 7, 11, 61] ⟨169093, 6, [(2, 2), (3, 2), (7, 1), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_169657 : Nat.Prime 169657 := by
  apply nodeValid_prime [2, 3, 7069] ⟨169657, 5, [(2, 3), (3, 1), (7069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7069
  · decide +kernel

theorem prime_176503 : Nat.Prime 176503 := by
  apply nodeValid_prime [2, 3, 23, 1279] ⟨176503, 5, [(2, 1), (3, 1), (23, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1279
  · decide +kernel

theorem prime_180181 : Nat.Prime 180181 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 13] ⟨180181, 6, [(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_212557 : Nat.Prime 212557 := by
  apply nodeValid_prime [2, 3, 17713] ⟨212557, 2, [(2, 2), (3, 1), (17713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17713
  · decide +kernel

theorem prime_225871 : Nat.Prime 225871 := by
  apply nodeValid_prime [2, 3, 5, 7529] ⟨225871, 6, [(2, 1), (3, 1), (5, 1), (7529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7529
  · decide +kernel

theorem prime_260231 : Nat.Prime 260231 := by
  apply nodeValid_prime [2, 5, 53, 491] ⟨260231, 11, [(2, 1), (5, 1), (53, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_491
  · decide +kernel

theorem prime_260417 : Nat.Prime 260417 := by
  apply nodeValid_prime [2, 13, 313] ⟨260417, 3, [(2, 6), (13, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_313
  · decide +kernel

theorem prime_261673 : Nat.Prime 261673 := by
  apply nodeValid_prime [2, 3, 10903] ⟨261673, 7, [(2, 3), (3, 1), (10903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10903
  · decide +kernel

theorem prime_289361 : Nat.Prime 289361 := by
  apply nodeValid_prime [2, 5, 3617] ⟨289361, 3, [(2, 4), (5, 1), (3617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3617
  · decide +kernel

theorem prime_290861 : Nat.Prime 290861 := by
  apply nodeValid_prime [2, 5, 14543] ⟨290861, 2, [(2, 2), (5, 1), (14543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14543
  · decide +kernel

theorem prime_293473 : Nat.Prime 293473 := by
  apply nodeValid_prime [2, 3, 1019] ⟨293473, 5, [(2, 5), (3, 2), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1019
  · decide +kernel

theorem prime_295237 : Nat.Prime 295237 := by
  apply nodeValid_prime [2, 3, 59, 139] ⟨295237, 2, [(2, 2), (3, 2), (59, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_139
  · decide +kernel

theorem prime_592219 : Nat.Prime 592219 := by
  apply nodeValid_prime [2, 3, 11, 997] ⟨592219, 2, [(2, 1), (3, 3), (11, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_997
  · decide +kernel

theorem prime_799807 : Nat.Prime 799807 := by
  apply nodeValid_prime [2, 3, 7, 137, 139] ⟨799807, 3, [(2, 1), (3, 1), (7, 1), (137, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_139
  · decide +kernel

theorem prime_820921 : Nat.Prime 820921 := by
  apply nodeValid_prime [2, 3, 5, 6841] ⟨820921, 21, [(2, 3), (3, 1), (5, 1), (6841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6841
  · decide +kernel

theorem prime_951193 : Nat.Prime 951193 := by
  apply nodeValid_prime [2, 3, 11, 1201] ⟨951193, 5, [(2, 3), (3, 2), (11, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1201
  · decide +kernel

theorem prime_1043849 : Nat.Prime 1043849 := by
  apply nodeValid_prime [2, 13, 10037] ⟨1043849, 3, [(2, 3), (13, 1), (10037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10037
  · decide +kernel

theorem prime_1180121 : Nat.Prime 1180121 := by
  apply nodeValid_prime [2, 5, 163, 181] ⟨1180121, 3, [(2, 3), (5, 1), (163, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_181
  · decide +kernel

theorem prime_1415059 : Nat.Prime 1415059 := by
  apply nodeValid_prime [2, 3, 181, 1303] ⟨1415059, 7, [(2, 1), (3, 1), (181, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_1303
  · decide +kernel

theorem prime_1553509 : Nat.Prime 1553509 := by
  apply nodeValid_prime [2, 3, 11, 3923] ⟨1553509, 2, [(2, 2), (3, 2), (11, 1), (3923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3923
  · decide +kernel

theorem prime_1826197 : Nat.Prime 1826197 := by
  apply nodeValid_prime [2, 3, 152183] ⟨1826197, 2, [(2, 2), (3, 1), (152183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152183
  · decide +kernel

theorem prime_2098927 : Nat.Prime 2098927 := by
  apply nodeValid_prime [2, 3, 47, 827] ⟨2098927, 3, [(2, 1), (3, 3), (47, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_827
  · decide +kernel

theorem prime_2296621 : Nat.Prime 2296621 := by
  apply nodeValid_prime [2, 3, 5, 4253] ⟨2296621, 6, [(2, 2), (3, 3), (5, 1), (4253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4253
  · decide +kernel

theorem prime_2950271 : Nat.Prime 2950271 := by
  apply nodeValid_prime [2, 5, 31, 307] ⟨2950271, 7, [(2, 1), (5, 1), (31, 2), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_307
  · decide +kernel

theorem prime_3038779 : Nat.Prime 3038779 := by
  apply nodeValid_prime [2, 3, 401, 421] ⟨3038779, 2, [(2, 1), (3, 2), (401, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_421
  · decide +kernel

theorem prime_3389333 : Nat.Prime 3389333 := by
  apply nodeValid_prime [2, 107, 7919] ⟨3389333, 2, [(2, 2), (107, 1), (7919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_7919
  · decide +kernel

theorem prime_3521677 : Nat.Prime 3521677 := by
  apply nodeValid_prime [2, 3, 293473] ⟨3521677, 5, [(2, 2), (3, 1), (293473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293473
  · decide +kernel

theorem prime_4840933 : Nat.Prime 4840933 := by
  apply nodeValid_prime [2, 3, 37, 10903] ⟨4840933, 2, [(2, 2), (3, 1), (37, 1), (10903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_10903
  · decide +kernel

theorem prime_4969163 : Nat.Prime 4969163 := by
  apply nodeValid_prime [2, 11, 225871] ⟨4969163, 2, [(2, 1), (11, 1), (225871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_225871
  · decide +kernel

theorem prime_5158211 : Nat.Prime 5158211 := by
  apply nodeValid_prime [2, 5, 23, 41, 547] ⟨5158211, 2, [(2, 1), (5, 1), (23, 1), (41, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_41
    · exact prime_547
  · decide +kernel

theorem prime_5939449 : Nat.Prime 5939449 := by
  apply nodeValid_prime [2, 3, 61, 4057] ⟨5939449, 7, [(2, 3), (3, 1), (61, 1), (4057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_4057
  · decide +kernel

theorem prime_13708679 : Nat.Prime 13708679 := by
  apply nodeValid_prime [2, 41, 47, 3557] ⟨13708679, 23, [(2, 1), (41, 1), (47, 1), (3557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_47
    · exact prime_3557
  · decide +kernel

theorem prime_14101471 : Nat.Prime 14101471 := by
  apply nodeValid_prime [2, 3, 5, 156683] ⟨14101471, 6, [(2, 1), (3, 2), (5, 1), (156683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_156683
  · decide +kernel

theorem prime_14625047 : Nat.Prime 14625047 := by
  apply nodeValid_prime [2, 277, 26399] ⟨14625047, 5, [(2, 1), (277, 1), (26399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_26399
  · decide +kernel

theorem prime_17025223 : Nat.Prime 17025223 := by
  apply nodeValid_prime [2, 3, 61, 181, 257] ⟨17025223, 5, [(2, 1), (3, 1), (61, 1), (181, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_181
    · exact prime_257
  · decide +kernel

theorem prime_19891769 : Nat.Prime 19891769 := by
  apply nodeValid_prime [2, 13, 17, 11251] ⟨19891769, 3, [(2, 3), (13, 1), (17, 1), (11251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_11251
  · decide +kernel

theorem prime_20335999 : Nat.Prime 20335999 := by
  apply nodeValid_prime [2, 3, 3389333] ⟨20335999, 6, [(2, 1), (3, 1), (3389333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3389333
  · decide +kernel

theorem prime_22283771 : Nat.Prime 22283771 := by
  apply nodeValid_prime [2, 5, 17, 19, 6899] ⟨22283771, 2, [(2, 1), (5, 1), (17, 1), (19, 1), (6899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_6899
  · decide +kernel

theorem prime_24562693 : Nat.Prime 24562693 := by
  apply nodeValid_prime [2, 3, 7, 11, 8861] ⟨24562693, 5, [(2, 2), (3, 2), (7, 1), (11, 1), (8861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_8861
  · decide +kernel

theorem prime_30994891 : Nat.Prime 30994891 := by
  apply nodeValid_prime [2, 3, 5, 19, 54377] ⟨30994891, 19, [(2, 1), (3, 1), (5, 1), (19, 1), (54377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_54377
  · decide +kernel

theorem prime_31992281 : Nat.Prime 31992281 := by
  apply nodeValid_prime [2, 5, 799807] ⟨31992281, 3, [(2, 3), (5, 1), (799807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_799807
  · decide +kernel

theorem prime_33403169 : Nat.Prime 33403169 := by
  apply nodeValid_prime [2, 1043849] ⟨33403169, 3, [(2, 5), (1043849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1043849
  · decide +kernel

theorem prime_41092169 : Nat.Prime 41092169 := by
  apply nodeValid_prime [2, 13, 23, 41, 419] ⟨41092169, 3, [(2, 3), (13, 1), (23, 1), (41, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_41
    · exact prime_419
  · decide +kernel

theorem prime_44871457 : Nat.Prime 44871457 := by
  apply nodeValid_prime [2, 3, 7, 9539] ⟨44871457, 10, [(2, 5), (3, 1), (7, 2), (9539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9539
  · decide +kernel

theorem prime_84437783 : Nat.Prime 84437783 := by
  apply nodeValid_prime [2, 11, 13, 295237] ⟨84437783, 5, [(2, 1), (11, 1), (13, 1), (295237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_295237
  · decide +kernel

theorem prime_111852649 : Nat.Prime 111852649 := by
  apply nodeValid_prime [2, 3, 1553509] ⟨111852649, 7, [(2, 3), (3, 2), (1553509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1553509
  · decide +kernel

theorem prime_116182393 : Nat.Prime 116182393 := by
  apply nodeValid_prime [2, 3, 4840933] ⟨116182393, 5, [(2, 3), (3, 1), (4840933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4840933
  · decide +kernel

theorem prime_117627247 : Nat.Prime 117627247 := by
  apply nodeValid_prime [2, 3, 11, 53, 1019] ⟨117627247, 3, [(2, 1), (3, 2), (11, 2), (53, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_1019
  · decide +kernel

theorem prime_140820209 : Nat.Prime 140820209 := by
  apply nodeValid_prime [2, 61, 157, 919] ⟨140820209, 3, [(2, 4), (61, 1), (157, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_157
    · exact prime_919
  · decide +kernel

theorem prime_141944111 : Nat.Prime 141944111 := by
  apply nodeValid_prime [2, 5, 7, 11, 83, 2221] ⟨141944111, 14, [(2, 1), (5, 1), (7, 1), (11, 1), (83, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_83
    · exact prime_2221
  · decide +kernel

theorem prime_209896103 : Nat.Prime 209896103 := by
  apply nodeValid_prime [2, 13, 31, 260417] ⟨209896103, 7, [(2, 1), (13, 1), (31, 1), (260417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_260417
  · decide +kernel

theorem prime_219597883 : Nat.Prime 219597883 := by
  apply nodeValid_prime [2, 3, 7, 23, 59, 3853] ⟨219597883, 2, [(2, 1), (3, 1), (7, 1), (23, 1), (59, 1), (3853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_59
    · exact prime_3853
  · decide +kernel

theorem prime_226732771 : Nat.Prime 226732771 := by
  apply nodeValid_prime [2, 3, 5, 11, 25447] ⟨226732771, 11, [(2, 1), (3, 4), (5, 1), (11, 1), (25447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_25447
  · decide +kernel

theorem prime_279894473 : Nat.Prime 279894473 := by
  apply nodeValid_prime [2, 11, 13, 19, 79, 163] ⟨279894473, 3, [(2, 3), (11, 1), (13, 1), (19, 1), (79, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_79
    · exact prime_163
  · decide +kernel

theorem prime_289983191 : Nat.Prime 289983191 := by
  apply nodeValid_prime [2, 5, 7, 139, 29803] ⟨289983191, 7, [(2, 1), (5, 1), (7, 1), (139, 1), (29803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_139
    · exact prime_29803
  · decide +kernel

theorem prime_448714571 : Nat.Prime 448714571 := by
  apply nodeValid_prime [2, 5, 44871457] ⟨448714571, 2, [(2, 1), (5, 1), (44871457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_44871457
  · decide +kernel

theorem prime_518367607 : Nat.Prime 518367607 := by
  apply nodeValid_prime [2, 3, 23, 47, 229, 349] ⟨518367607, 3, [(2, 1), (3, 1), (23, 1), (47, 1), (229, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47
    · exact prime_229
    · exact prime_349
  · decide +kernel

theorem prime_648667667 : Nat.Prime 648667667 := by
  apply nodeValid_prime [2, 23, 14101471] ⟨648667667, 2, [(2, 1), (23, 1), (14101471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_14101471
  · decide +kernel

theorem prime_949670681 : Nat.Prime 949670681 := by
  apply nodeValid_prime [2, 5, 7, 101, 33581] ⟨949670681, 3, [(2, 3), (5, 1), (7, 1), (101, 1), (33581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_101
    · exact prime_33581
  · decide +kernel

theorem prime_1461532591 : Nat.Prime 1461532591 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 53951] ⟨1461532591, 7, [(2, 1), (3, 2), (5, 1), (7, 1), (43, 1), (53951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_53951
  · decide +kernel

theorem prime_1488604807 : Nat.Prime 1488604807 := by
  apply nodeValid_prime [2, 3, 13, 281, 22639] ⟨1488604807, 3, [(2, 1), (3, 2), (13, 1), (281, 1), (22639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_281
    · exact prime_22639
  · decide +kernel

theorem prime_1632163619 : Nat.Prime 1632163619 := by
  apply nodeValid_prime [2, 457, 1229, 1453] ⟨1632163619, 2, [(2, 1), (457, 1), (1229, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_1229
    · exact prime_1453
  · decide +kernel

theorem prime_2029143091 : Nat.Prime 2029143091 := by
  apply nodeValid_prime [2, 3, 5, 13, 149, 34919] ⟨2029143091, 15, [(2, 1), (3, 1), (5, 1), (13, 1), (149, 1), (34919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_149
    · exact prime_34919
  · decide +kernel

theorem prime_2138279107 : Nat.Prime 2138279107 := by
  apply nodeValid_prime [2, 3, 7757, 45943] ⟨2138279107, 2, [(2, 1), (3, 1), (7757, 1), (45943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7757
    · exact prime_45943
  · decide +kernel

theorem prime_2275273289 : Nat.Prime 2275273289 := by
  apply nodeValid_prime [2, 241, 1180121] ⟨2275273289, 3, [(2, 3), (241, 1), (1180121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_1180121
  · decide +kernel

theorem prime_2355133483 : Nat.Prime 2355133483 := by
  apply nodeValid_prime [2, 3, 13, 67, 16691] ⟨2355133483, 3, [(2, 1), (3, 4), (13, 1), (67, 1), (16691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
    · exact prime_16691
  · decide +kernel

theorem prime_2544211457 : Nat.Prime 2544211457 := by
  apply nodeValid_prime [2, 4969163] ⟨2544211457, 3, [(2, 9), (4969163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4969163
  · decide +kernel

theorem prime_3485471791 : Nat.Prime 3485471791 := by
  apply nodeValid_prime [2, 3, 5, 116182393] ⟨3485471791, 3, [(2, 1), (3, 1), (5, 1), (116182393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_116182393
  · decide +kernel

theorem prime_3513603799 : Nat.Prime 3513603799 := by
  apply nodeValid_prime [2, 3, 31, 2098927] ⟨3513603799, 6, [(2, 1), (3, 3), (31, 1), (2098927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2098927
  · decide +kernel

theorem prime_3919643423 : Nat.Prime 3919643423 := by
  apply nodeValid_prime [2, 29, 593, 113963] ⟨3919643423, 5, [(2, 1), (29, 1), (593, 1), (113963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_593
    · exact prime_113963
  · decide +kernel

theorem prime_4673349319 : Nat.Prime 4673349319 := by
  apply nodeValid_prime [2, 3, 11, 887, 79829] ⟨4673349319, 3, [(2, 1), (3, 1), (11, 1), (887, 1), (79829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_887
    · exact prime_79829
  · decide +kernel

theorem prime_5380197721 : Nat.Prime 5380197721 := by
  apply nodeValid_prime [2, 3, 5, 23, 1019, 1913] ⟨5380197721, 7, [(2, 3), (3, 1), (5, 1), (23, 1), (1019, 1), (1913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1019
    · exact prime_1913
  · decide +kernel

theorem prime_8076862279 : Nat.Prime 8076862279 := by
  apply nodeValid_prime [2, 3, 448714571] ⟨8076862279, 3, [(2, 1), (3, 2), (448714571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_448714571
  · decide +kernel

theorem prime_8160818053 : Nat.Prime 8160818053 := by
  apply nodeValid_prime [2, 3, 11027, 61673] ⟨8160818053, 2, [(2, 2), (3, 1), (11027, 1), (61673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11027
    · exact prime_61673
  · decide +kernel

theorem prime_14403338659 : Nat.Prime 14403338659 := by
  apply nodeValid_prime [2, 3, 47, 17025223] ⟨14403338659, 10, [(2, 1), (3, 2), (47, 1), (17025223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_17025223
  · decide +kernel

theorem prime_17018111827 : Nat.Prime 17018111827 := by
  apply nodeValid_prime [2, 3, 2713, 12907] ⟨17018111827, 5, [(2, 1), (3, 5), (2713, 1), (12907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2713
    · exact prime_12907
  · decide +kernel

theorem prime_23817676913 : Nat.Prime 23817676913 := by
  apply nodeValid_prime [2, 1488604807] ⟨23817676913, 3, [(2, 4), (1488604807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1488604807
  · decide +kernel

theorem prime_25314363857 : Nat.Prime 25314363857 := by
  apply nodeValid_prime [2, 71, 22283771] ⟨25314363857, 3, [(2, 4), (71, 1), (22283771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_22283771
  · decide +kernel

theorem prime_37711322351 : Nat.Prime 37711322351 := by
  apply nodeValid_prime [2, 5, 13, 41, 1415059] ⟨37711322351, 37, [(2, 1), (5, 2), (13, 1), (41, 1), (1415059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_1415059
  · decide +kernel

theorem prime_74582075507 : Nat.Prime 74582075507 := by
  apply nodeValid_prime [2, 10589, 3521677] ⟨74582075507, 2, [(2, 1), (10589, 1), (3521677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10589
    · exact prime_3521677
  · decide +kernel

theorem prime_120261325211 : Nat.Prime 120261325211 := by
  apply nodeValid_prime [2, 5, 13, 23, 139, 289361] ⟨120261325211, 2, [(2, 1), (5, 1), (13, 1), (23, 1), (139, 1), (289361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_139
    · exact prime_289361
  · decide +kernel

theorem prime_225101689027 : Nat.Prime 225101689027 := by
  apply nodeValid_prime [2, 3, 176503, 212557] ⟨225101689027, 3, [(2, 1), (3, 1), (176503, 1), (212557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_176503
    · exact prime_212557
  · decide +kernel

theorem prime_260152801199 : Nat.Prime 260152801199 := by
  apply nodeValid_prime [2, 89, 1461532591] ⟨260152801199, 7, [(2, 1), (89, 1), (1461532591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1461532591
  · decide +kernel

theorem prime_602862064303 : Nat.Prime 602862064303 := by
  apply nodeValid_prime [2, 3, 151, 2557, 260231] ⟨602862064303, 3, [(2, 1), (3, 1), (151, 1), (2557, 1), (260231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_2557
    · exact prime_260231
  · decide +kernel

theorem prime_894212167843 : Nat.Prime 894212167843 := by
  apply nodeValid_prime [2, 3, 7, 59, 709, 169657] ⟨894212167843, 3, [(2, 1), (3, 2), (7, 1), (59, 1), (709, 1), (169657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_709
    · exact prime_169657
  · decide +kernel

theorem prime_1803919853663 : Nat.Prime 1803919853663 := by
  apply nodeValid_prime [2, 53, 17018111827] ⟨1803919853663, 5, [(2, 1), (53, 1), (17018111827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_17018111827
  · decide +kernel

theorem prime_3576848667383 : Nat.Prime 3576848667383 := by
  apply nodeValid_prime [2, 509, 3513603799] ⟨3576848667383, 5, [(2, 1), (509, 1), (3513603799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_3513603799
  · decide +kernel

theorem prime_3576848670809 : Nat.Prime 3576848670809 := by
  apply nodeValid_prime [2, 7, 311, 6277, 32719] ⟨3576848670809, 3, [(2, 3), (7, 1), (311, 1), (6277, 1), (32719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_311
    · exact prime_6277
    · exact prime_32719
  · decide +kernel

theorem prime_3576848671373 : Nat.Prime 3576848671373 := by
  apply nodeValid_prime [2, 894212167843] ⟨3576848671373, 2, [(2, 2), (894212167843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_894212167843
  · decide +kernel

theorem prime_3579939611923 : Nat.Prime 3579939611923 := by
  apply nodeValid_prime [2, 3, 1069, 6529, 85487] ⟨3579939611923, 2, [(2, 1), (3, 1), (1069, 1), (6529, 1), (85487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
    · exact prime_6529
    · exact prime_85487
  · decide +kernel

theorem prime_3579939612323 : Nat.Prime 3579939612323 := by
  apply nodeValid_prime [2, 613, 3557, 820921] ⟨3579939612323, 2, [(2, 1), (613, 1), (3557, 1), (820921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_3557
    · exact prime_820921
  · decide +kernel

theorem prime_3579939624337 : Nat.Prime 3579939624337 := by
  apply nodeValid_prime [2, 3, 74582075507] ⟨3579939624337, 5, [(2, 4), (3, 1), (74582075507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74582075507
  · decide +kernel

theorem prime_3583032307997 : Nat.Prime 3583032307997 := by
  apply nodeValid_prime [2, 3089, 289983191] ⟨3583032307997, 2, [(2, 2), (3089, 1), (289983191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3089
    · exact prime_289983191
  · decide +kernel

theorem prime_3583032309403 : Nat.Prime 3583032309403 := by
  apply nodeValid_prime [2, 3, 7, 13, 197, 169093] ⟨3583032309403, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (197, 2), (169093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_197
    · exact prime_169093
  · decide +kernel

theorem prime_3583032390979 : Nat.Prime 3583032390979 := by
  apply nodeValid_prime [2, 3, 17, 134243, 261673] ⟨3583032390979, 3, [(2, 1), (3, 1), (17, 1), (134243, 1), (261673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_134243
    · exact prime_261673
  · decide +kernel

theorem prime_3586126850989 : Nat.Prime 3586126850989 := by
  apply nodeValid_prime [2, 3, 11, 37, 73, 79, 127321] ⟨3586126850989, 2, [(2, 2), (3, 1), (11, 1), (37, 1), (73, 1), (79, 1), (127321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_73
    · exact prime_79
    · exact prime_127321
  · decide +kernel

theorem prime_3586126851877 : Nat.Prime 3586126851877 := by
  apply nodeValid_prime [2, 3, 37, 8076862279] ⟨3586126851877, 2, [(2, 2), (3, 1), (37, 1), (8076862279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_8076862279
  · decide +kernel

theorem prime_3586126972249 : Nat.Prime 3586126972249 := by
  apply nodeValid_prime [2, 3, 52363, 951193] ⟨3586126972249, 7, [(2, 3), (3, 2), (52363, 1), (951193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52363
    · exact prime_951193
  · decide +kernel

theorem prime_3589223361301 : Nat.Prime 3589223361301 := by
  apply nodeValid_prime [2, 3, 5, 19, 209896103] ⟨3589223361301, 2, [(2, 2), (3, 2), (5, 2), (19, 1), (209896103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_209896103
  · decide +kernel

theorem prime_3589223428061 : Nat.Prime 3589223428061 := by
  apply nodeValid_prime [2, 5, 73, 809, 3038779] ⟨3589223428061, 2, [(2, 2), (5, 1), (73, 1), (809, 1), (3038779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_809
    · exact prime_3038779
  · decide +kernel

theorem prime_3589223428093 : Nat.Prime 3589223428093 := by
  apply nodeValid_prime [2, 3, 127, 2355133483] ⟨3589223428093, 5, [(2, 2), (3, 1), (127, 1), (2355133483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_2355133483
  · decide +kernel

theorem prime_3592321537531 : Nat.Prime 3592321537531 := by
  apply nodeValid_prime [2, 3, 5, 11, 587, 1289, 14387] ⟨3592321537531, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (587, 1), (1289, 1), (14387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_587
    · exact prime_1289
    · exact prime_14387
  · decide +kernel

theorem prime_3592321539847 : Nat.Prime 3592321539847 := by
  apply nodeValid_prime [2, 3, 13, 71, 648667667] ⟨3592321539847, 5, [(2, 1), (3, 1), (13, 1), (71, 1), (648667667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_648667667
  · decide +kernel

theorem prime_3592321561189 : Nat.Prime 3592321561189 := by
  apply nodeValid_prime [2, 3, 19, 37, 141944111] ⟨3592321561189, 2, [(2, 2), (3, 2), (19, 1), (37, 1), (141944111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_141944111
  · decide +kernel

theorem prime_3595421554481 : Nat.Prime 3595421554481 := by
  apply nodeValid_prime [2, 5, 7, 439, 14625047] ⟨3595421554481, 3, [(2, 4), (5, 1), (7, 1), (439, 1), (14625047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_439
    · exact prime_14625047
  · decide +kernel

theorem prime_3595421555053 : Nat.Prime 3595421555053 := by
  apply nodeValid_prime [2, 3, 71, 157, 227, 118409] ⟨3595421555053, 2, [(2, 2), (3, 1), (71, 1), (157, 1), (227, 1), (118409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_157
    · exact prime_227
    · exact prime_118409
  · decide +kernel

theorem prime_3595421576189 : Nat.Prime 3595421576189 := by
  apply nodeValid_prime [2, 13, 491, 140820209] ⟨3595421576189, 2, [(2, 2), (13, 1), (491, 1), (140820209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_491
    · exact prime_140820209
  · decide +kernel

theorem prime_3598523396371 : Nat.Prime 3598523396371 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 33403169] ⟨3598523396371, 7, [(2, 1), (3, 4), (5, 1), (7, 1), (19, 1), (33403169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_33403169
  · decide +kernel

theorem prime_3598523423629 : Nat.Prime 3598523423629 := by
  apply nodeValid_prime [2, 3, 7, 383, 111852649] ⟨3598523423629, 6, [(2, 2), (3, 1), (7, 1), (383, 1), (111852649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
    · exact prime_111852649
  · decide +kernel

theorem prime_3598523423669 : Nat.Prime 3598523423669 := by
  apply nodeValid_prime [2, 21893, 41092169] ⟨3598523423669, 2, [(2, 2), (21893, 1), (41092169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21893
    · exact prime_41092169
  · decide +kernel

theorem prime_3601627010419 : Nat.Prime 3601627010419 := by
  apply nodeValid_prime [2, 3, 29, 647, 31992281] ⟨3601627010419, 3, [(2, 1), (3, 1), (29, 1), (647, 1), (31992281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_647
    · exact prime_31992281
  · decide +kernel

theorem prime_3601627010507 : Nat.Prime 3601627010507 := by
  apply nodeValid_prime [2, 7, 61, 311, 1741, 7789] ⟨3601627010507, 2, [(2, 1), (7, 1), (61, 1), (311, 1), (1741, 1), (7789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_311
    · exact prime_1741
    · exact prime_7789
  · decide +kernel

theorem prime_3601627024433 : Nat.Prime 3601627024433 := by
  apply nodeValid_prime [2, 225101689027] ⟨3601627024433, 3, [(2, 4), (225101689027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_225101689027
  · decide +kernel

theorem prime_3604732461053 : Nat.Prime 3604732461053 := by
  apply nodeValid_prime [2, 19, 31, 293, 168449] ⟨3604732461053, 2, [(2, 2), (19, 1), (31, 2), (293, 1), (168449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_293
    · exact prime_168449
  · decide +kernel

theorem prime_3604732473037 : Nat.Prime 3604732473037 := by
  apply nodeValid_prime [2, 3, 113, 20089, 132329] ⟨3604732473037, 5, [(2, 2), (3, 1), (113, 1), (20089, 1), (132329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_20089
    · exact prime_132329
  · decide +kernel

theorem prime_3604732473071 : Nat.Prime 3604732473071 := by
  apply nodeValid_prime [2, 5, 67, 5380197721] ⟨3604732473071, 7, [(2, 1), (5, 1), (67, 1), (5380197721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_5380197721
  · decide +kernel

theorem prime_3607839707327 : Nat.Prime 3607839707327 := by
  apply nodeValid_prime [2, 1803919853663] ⟨3607839707327, 5, [(2, 1), (1803919853663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1803919853663
  · decide +kernel

theorem prime_3607839756331 : Nat.Prime 3607839756331 := by
  apply nodeValid_prime [2, 3, 5, 120261325211] ⟨3607839756331, 2, [(2, 1), (3, 1), (5, 1), (120261325211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_120261325211
  · decide +kernel

theorem prime_3607839756971 : Nat.Prime 3607839756971 := by
  apply nodeValid_prime [2, 5, 1289, 279894473] ⟨3607839756971, 2, [(2, 1), (5, 1), (1289, 1), (279894473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1289
    · exact prime_279894473
  · decide +kernel

theorem prime_3610948750363 : Nat.Prime 3610948750363 := by
  apply nodeValid_prime [2, 3, 43, 518367607] ⟨3610948750363, 2, [(2, 1), (3, 4), (43, 1), (518367607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_518367607
  · decide +kernel

theorem prime_3610948753081 : Nat.Prime 3610948753081 := by
  apply nodeValid_prime [2, 3, 5, 16937, 592219] ⟨3610948753081, 7, [(2, 3), (3, 2), (5, 1), (16937, 1), (592219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16937
    · exact prime_592219
  · decide +kernel

theorem prime_3610948775477 : Nat.Prime 3610948775477 := by
  apply nodeValid_prime [2, 7, 37, 3485471791] ⟨3610948775477, 2, [(2, 2), (7, 1), (37, 1), (3485471791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_3485471791
  · decide +kernel

theorem prime_3614059666367 : Nat.Prime 3614059666367 := by
  apply nodeValid_prime [2, 1217, 24329, 61031] ⟨3614059666367, 5, [(2, 1), (1217, 1), (24329, 1), (61031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1217
    · exact prime_24329
    · exact prime_61031
  · decide +kernel

theorem prime_3614059685317 : Nat.Prime 3614059685317 := by
  apply nodeValid_prime [2, 3, 50707, 5939449] ⟨3614059685317, 2, [(2, 2), (3, 1), (50707, 1), (5939449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50707
    · exact prime_5939449
  · decide +kernel

theorem prime_3614059686043 : Nat.Prime 3614059686043 := by
  apply nodeValid_prime [2, 3, 13, 62191, 82781] ⟨3614059686043, 2, [(2, 1), (3, 3), (13, 1), (62191, 1), (82781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_62191
    · exact prime_82781
  · decide +kernel

theorem prime_3617172372907 : Nat.Prime 3617172372907 := by
  apply nodeValid_prime [2, 3, 43, 4673349319] ⟨3617172372907, 2, [(2, 1), (3, 2), (43, 1), (4673349319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_4673349319
  · decide +kernel

theorem prime_3617172385457 : Nat.Prime 3617172385457 := by
  apply nodeValid_prime [2, 7, 31, 71, 1087, 13499] ⟨3617172385457, 3, [(2, 4), (7, 1), (31, 1), (71, 1), (1087, 1), (13499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_71
    · exact prime_1087
    · exact prime_13499
  · decide +kernel

theorem prime_3617172385819 : Nat.Prime 3617172385819 := by
  apply nodeValid_prime [2, 3, 602862064303] ⟨3617172385819, 3, [(2, 1), (3, 1), (602862064303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_602862064303
  · decide +kernel

theorem prime_3620286890777 : Nat.Prime 3620286890777 := by
  apply nodeValid_prime [2, 19, 23817676913] ⟨3620286890777, 3, [(2, 3), (19, 1), (23817676913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23817676913
  · decide +kernel

theorem prime_3620286945281 : Nat.Prime 3620286945281 := by
  apply nodeValid_prime [2, 5, 227, 1039, 1499] ⟨3620286945281, 3, [(2, 11), (5, 1), (227, 1), (1039, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
    · exact prime_1039
    · exact prime_1499
  · decide +kernel

theorem prime_3620286945697 : Nat.Prime 3620286945697 := by
  apply nodeValid_prime [2, 3, 37711322351] ⟨3620286945697, 5, [(2, 5), (3, 1), (37711322351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37711322351
  · decide +kernel

theorem prime_3623403215533 : Nat.Prime 3623403215533 := by
  apply nodeValid_prime [2, 3, 37, 8160818053] ⟨3623403215533, 11, [(2, 2), (3, 1), (37, 1), (8160818053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_8160818053
  · decide +kernel

theorem prime_3623403234181 : Nat.Prime 3623403234181 := by
  apply nodeValid_prime [2, 3, 5, 37, 1632163619] ⟨3623403234181, 7, [(2, 2), (3, 1), (5, 1), (37, 1), (1632163619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_1632163619
  · decide +kernel

theorem prime_3623403234389 : Nat.Prime 3623403234389 := by
  apply nodeValid_prime [2, 7, 89, 4999, 290861] ⟨3623403234389, 2, [(2, 2), (7, 1), (89, 1), (4999, 1), (290861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_4999
    · exact prime_290861
  · decide +kernel

theorem prime_3626521360019 : Nat.Prime 3626521360019 := by
  apply nodeValid_prime [2, 349, 379, 13708679] ⟨3626521360019, 2, [(2, 1), (349, 1), (379, 1), (13708679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_349
    · exact prime_379
    · exact prime_13708679
  · decide +kernel

theorem prime_3626521365463 : Nat.Prime 3626521365463 := by
  apply nodeValid_prime [2, 3, 29, 131, 883, 180181] ⟨3626521365463, 5, [(2, 1), (3, 1), (29, 1), (131, 1), (883, 1), (180181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_131
    · exact prime_883
    · exact prime_180181
  · decide +kernel

theorem prime_3626521365473 : Nat.Prime 3626521365473 := by
  apply nodeValid_prime [2, 53, 2138279107] ⟨3626521365473, 3, [(2, 5), (53, 1), (2138279107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_2138279107
  · decide +kernel

theorem prime_3629641316731 : Nat.Prime 3629641316731 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 11317, 74761] ⟨3629641316731, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (11317, 1), (74761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_11317
    · exact prime_74761
  · decide +kernel

theorem prime_3629641342069 : Nat.Prime 3629641342069 := by
  apply nodeValid_prime [2, 3, 7, 14403338659] ⟨3629641342069, 2, [(2, 2), (3, 2), (7, 1), (14403338659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14403338659
  · decide +kernel

theorem prime_3629641342783 : Nat.Prime 3629641342783 := by
  apply nodeValid_prime [2, 3, 7, 13, 949670681] ⟨3629641342783, 3, [(2, 1), (3, 1), (7, 2), (13, 1), (949670681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_949670681
  · decide +kernel

theorem prime_3632762944549 : Nat.Prime 3632762944549 := by
  apply nodeValid_prime [2, 3, 6521, 5158211] ⟨3632762944549, 2, [(2, 2), (3, 3), (6521, 1), (5158211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6521
    · exact prime_5158211
  · decide +kernel

theorem prime_3632762945107 : Nat.Prime 3632762945107 := by
  apply nodeValid_prime [2, 3, 87877, 2296621] ⟨3632762945107, 2, [(2, 1), (3, 2), (87877, 1), (2296621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_87877
    · exact prime_2296621
  · decide +kernel

theorem prime_3632763090973 : Nat.Prime 3632763090973 := by
  apply nodeValid_prime [2, 3, 102611, 2950271] ⟨3632763090973, 2, [(2, 2), (3, 1), (102611, 1), (2950271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102611
    · exact prime_2950271
  · decide +kernel

theorem prime_3635886683647 : Nat.Prime 3635886683647 := by
  apply nodeValid_prime [2, 3, 7, 19, 30994891] ⟨3635886683647, 6, [(2, 1), (3, 2), (7, 3), (19, 1), (30994891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_30994891
  · decide +kernel

theorem prime_3635886715757 : Nat.Prime 3635886715757 := by
  apply nodeValid_prime [2, 19, 211, 226732771] ⟨3635886715757, 2, [(2, 2), (19, 1), (211, 1), (226732771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_211
    · exact prime_226732771
  · decide +kernel

theorem prime_3635886715823 : Nat.Prime 3635886715823 := by
  apply nodeValid_prime [2, 17, 47, 2275273289] ⟨3635886715823, 5, [(2, 1), (17, 1), (47, 1), (2275273289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_2275273289
  · decide +kernel

theorem prime_3639011987179 : Nat.Prime 3639011987179 := by
  apply nodeValid_prime [2, 3, 23, 66797, 131591] ⟨3639011987179, 2, [(2, 1), (3, 2), (23, 1), (66797, 1), (131591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_66797
    · exact prime_131591
  · decide +kernel

theorem prime_3639011991469 : Nat.Prime 3639011991469 := by
  apply nodeValid_prime [2, 3, 7, 311, 1453, 95869] ⟨3639011991469, 6, [(2, 2), (3, 1), (7, 1), (311, 1), (1453, 1), (95869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_311
    · exact prime_1453
    · exact prime_95869
  · decide +kernel

theorem prime_3639012093337 : Nat.Prime 3639012093337 := by
  apply nodeValid_prime [2, 3, 6173, 24562693] ⟨3639012093337, 5, [(2, 3), (3, 1), (6173, 1), (24562693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6173
    · exact prime_24562693
  · decide +kernel

theorem prime_3642139216757 : Nat.Prime 3642139216757 := by
  apply nodeValid_prime [2, 19, 277, 1223, 141461] ⟨3642139216757, 2, [(2, 2), (19, 1), (277, 1), (1223, 1), (141461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_277
    · exact prime_1223
    · exact prime_141461
  · decide +kernel

theorem prime_3642139216787 : Nat.Prime 3642139216787 := by
  apply nodeValid_prime [2, 7, 260152801199] ⟨3642139216787, 2, [(2, 1), (7, 1), (260152801199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_260152801199
  · decide +kernel

theorem prime_3642139331923 : Nat.Prime 3642139331923 := by
  apply nodeValid_prime [2, 3, 7, 13, 79, 84437783] ⟨3642139331923, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (79, 1), (84437783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_79
    · exact prime_84437783
  · decide +kernel

theorem prime_3645268383391 : Nat.Prime 3645268383391 := by
  apply nodeValid_prime [2, 3, 5, 31, 3919643423] ⟨3645268383391, 6, [(2, 1), (3, 1), (5, 1), (31, 1), (3919643423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_3919643423
  · decide +kernel

theorem prime_3645268384531 : Nat.Prime 3645268384531 := by
  apply nodeValid_prime [2, 3, 5, 1033, 117627247] ⟨3645268384531, 3, [(2, 1), (3, 1), (5, 1), (1033, 1), (117627247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1033
    · exact prime_117627247
  · decide +kernel

theorem prime_3645268395409 : Nat.Prime 3645268395409 := by
  apply nodeValid_prime [2, 3, 25314363857] ⟨3645268395409, 29, [(2, 4), (3, 2), (25314363857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25314363857
  · decide +kernel

theorem prime_3648399228163 : Nat.Prime 3648399228163 := by
  apply nodeValid_prime [2, 3, 13, 71, 219597883] ⟨3648399228163, 2, [(2, 1), (3, 2), (13, 1), (71, 1), (219597883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_219597883
  · decide +kernel

theorem prime_3648399229339 : Nat.Prime 3648399229339 := by
  apply nodeValid_prime [2, 3, 239, 2544211457] ⟨3648399229339, 2, [(2, 1), (3, 1), (239, 1), (2544211457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_2544211457
  · decide +kernel

theorem prime_3648399277619 : Nat.Prime 3648399277619 := by
  apply nodeValid_prime [2, 29, 31, 2029143091] ⟨3648399277619, 2, [(2, 1), (29, 1), (31, 1), (2029143091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_31
    · exact prime_2029143091
  · decide +kernel

theorem prime_3651531980441 : Nat.Prime 3651531980441 := by
  apply nodeValid_prime [2, 5, 67, 20335999] ⟨3651531980441, 3, [(2, 3), (5, 1), (67, 2), (20335999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_20335999
  · decide +kernel

theorem prime_3651532035017 : Nat.Prime 3651532035017 := by
  apply nodeValid_prime [2, 23, 10867, 1826197] ⟨3651532035017, 3, [(2, 3), (23, 1), (10867, 1), (1826197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_10867
    · exact prime_1826197
  · decide +kernel

theorem prime_3651532035331 : Nat.Prime 3651532035331 := by
  apply nodeValid_prime [2, 3, 5, 29, 211, 19891769] ⟨3651532035331, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (211, 1), (19891769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_211
    · exact prime_19891769
  · decide +kernel

end Sude.Lucas.Generated
