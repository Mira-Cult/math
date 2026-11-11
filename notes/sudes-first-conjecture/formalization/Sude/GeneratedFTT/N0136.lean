import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0124
import Sude.GeneratedFTT.N0129

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10859 : Nat.Prime 10859 := by
  apply nodeValid_prime [2, 61, 89] ⟨10859, 2, [(2, 1), (61, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_89
  · decide +kernel

theorem prime_14071 : Nat.Prime 14071 := by
  apply nodeValid_prime [2, 3, 5, 7, 67] ⟨14071, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_14699 : Nat.Prime 14699 := by
  apply nodeValid_prime [2, 7349] ⟨14699, 2, [(2, 1), (7349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7349
  · decide +kernel

theorem prime_21269 : Nat.Prime 21269 := by
  apply nodeValid_prime [2, 13, 409] ⟨21269, 2, [(2, 2), (13, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_409
  · decide +kernel

theorem prime_25301 : Nat.Prime 25301 := by
  apply nodeValid_prime [2, 5, 11, 23] ⟨25301, 3, [(2, 2), (5, 2), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_41897 : Nat.Prime 41897 := by
  apply nodeValid_prime [2, 5237] ⟨41897, 3, [(2, 3), (5237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5237
  · decide +kernel

theorem prime_42863 : Nat.Prime 42863 := by
  apply nodeValid_prime [2, 29, 739] ⟨42863, 5, [(2, 1), (29, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_739
  · decide +kernel

theorem prime_45139 : Nat.Prime 45139 := by
  apply nodeValid_prime [2, 3, 7523] ⟨45139, 2, [(2, 1), (3, 1), (7523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7523
  · decide +kernel

theorem prime_46133 : Nat.Prime 46133 := by
  apply nodeValid_prime [2, 19, 607] ⟨46133, 2, [(2, 2), (19, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_607
  · decide +kernel

theorem prime_46751 : Nat.Prime 46751 := by
  apply nodeValid_prime [2, 5, 11, 17] ⟨46751, 11, [(2, 1), (5, 3), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_49801 : Nat.Prime 49801 := by
  apply nodeValid_prime [2, 3, 5, 83] ⟨49801, 13, [(2, 3), (3, 1), (5, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
  · decide +kernel

theorem prime_65899 : Nat.Prime 65899 := by
  apply nodeValid_prime [2, 3, 7, 523] ⟨65899, 3, [(2, 1), (3, 2), (7, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_523
  · decide +kernel

theorem prime_74047 : Nat.Prime 74047 := by
  apply nodeValid_prime [2, 3, 7, 41, 43] ⟨74047, 3, [(2, 1), (3, 1), (7, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_81013 : Nat.Prime 81013 := by
  apply nodeValid_prime [2, 3, 43, 157] ⟨81013, 6, [(2, 2), (3, 1), (43, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_157
  · decide +kernel

theorem prime_82139 : Nat.Prime 82139 := by
  apply nodeValid_prime [2, 7, 5867] ⟨82139, 6, [(2, 1), (7, 1), (5867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5867
  · decide +kernel

theorem prime_88589 : Nat.Prime 88589 := by
  apply nodeValid_prime [2, 22147] ⟨88589, 2, [(2, 2), (22147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22147
  · decide +kernel

theorem prime_105319 : Nat.Prime 105319 := by
  apply nodeValid_prime [2, 3, 5851] ⟨105319, 3, [(2, 1), (3, 2), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5851
  · decide +kernel

theorem prime_108377 : Nat.Prime 108377 := by
  apply nodeValid_prime [2, 19, 23, 31] ⟨108377, 3, [(2, 3), (19, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_109169 : Nat.Prime 109169 := by
  apply nodeValid_prime [2, 6823] ⟨109169, 3, [(2, 4), (6823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6823
  · decide +kernel

theorem prime_150571 : Nat.Prime 150571 := by
  apply nodeValid_prime [2, 3, 5, 7, 239] ⟨150571, 7, [(2, 1), (3, 2), (5, 1), (7, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_239
  · decide +kernel

theorem prime_174763 : Nat.Prime 174763 := by
  apply nodeValid_prime [2, 3, 7, 19, 73] ⟨174763, 17, [(2, 1), (3, 2), (7, 1), (19, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_73
  · decide +kernel

theorem prime_178441 : Nat.Prime 178441 := by
  apply nodeValid_prime [2, 3, 5, 1487] ⟨178441, 11, [(2, 3), (3, 1), (5, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1487
  · decide +kernel

theorem prime_179287 : Nat.Prime 179287 := by
  apply nodeValid_prime [2, 3, 29881] ⟨179287, 3, [(2, 1), (3, 1), (29881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29881
  · decide +kernel

theorem prime_201011 : Nat.Prime 201011 := by
  apply nodeValid_prime [2, 5, 20101] ⟨201011, 2, [(2, 1), (5, 1), (20101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20101
  · decide +kernel

theorem prime_202409 : Nat.Prime 202409 := by
  apply nodeValid_prime [2, 25301] ⟨202409, 3, [(2, 3), (25301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25301
  · decide +kernel

theorem prime_213737 : Nat.Prime 213737 := by
  apply nodeValid_prime [2, 26717] ⟨213737, 3, [(2, 3), (26717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26717
  · decide +kernel

theorem prime_295153 : Nat.Prime 295153 := by
  apply nodeValid_prime [2, 3, 11, 13, 43] ⟨295153, 10, [(2, 4), (3, 1), (11, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_391073 : Nat.Prime 391073 := by
  apply nodeValid_prime [2, 11, 101] ⟨391073, 3, [(2, 5), (11, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_101
  · decide +kernel

theorem prime_419191 : Nat.Prime 419191 := by
  apply nodeValid_prime [2, 3, 5, 89, 157] ⟨419191, 6, [(2, 1), (3, 1), (5, 1), (89, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_157
  · decide +kernel

theorem prime_509573 : Nat.Prime 509573 := by
  apply nodeValid_prime [2, 7, 18199] ⟨509573, 2, [(2, 2), (7, 1), (18199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_18199
  · decide +kernel

theorem prime_532009 : Nat.Prime 532009 := by
  apply nodeValid_prime [2, 3, 821] ⟨532009, 37, [(2, 3), (3, 4), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_821
  · decide +kernel

theorem prime_595801 : Nat.Prime 595801 := by
  apply nodeValid_prime [2, 3, 5, 331] ⟨595801, 11, [(2, 3), (3, 2), (5, 2), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_331
  · decide +kernel

theorem prime_597613 : Nat.Prime 597613 := by
  apply nodeValid_prime [2, 3, 49801] ⟨597613, 2, [(2, 2), (3, 1), (49801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49801
  · decide +kernel

theorem prime_734663 : Nat.Prime 734663 := by
  apply nodeValid_prime [2, 107, 3433] ⟨734663, 5, [(2, 1), (107, 1), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_3433
  · decide +kernel

theorem prime_901861 : Nat.Prime 901861 := by
  apply nodeValid_prime [2, 3, 5, 15031] ⟨901861, 14, [(2, 2), (3, 1), (5, 1), (15031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15031
  · decide +kernel

theorem prime_983791 : Nat.Prime 983791 := by
  apply nodeValid_prime [2, 3, 5, 17, 643] ⟨983791, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_643
  · decide +kernel

theorem prime_1258711 : Nat.Prime 1258711 := by
  apply nodeValid_prime [2, 3, 5, 41957] ⟨1258711, 3, [(2, 1), (3, 1), (5, 1), (41957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41957
  · decide +kernel

theorem prime_1282423 : Nat.Prime 1282423 := by
  apply nodeValid_prime [2, 3, 213737] ⟨1282423, 3, [(2, 1), (3, 1), (213737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_213737
  · decide +kernel

theorem prime_1299019 : Nat.Prime 1299019 := by
  apply nodeValid_prime [2, 3, 7, 157, 197] ⟨1299019, 2, [(2, 1), (3, 1), (7, 1), (157, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
    · exact prime_197
  · decide +kernel

theorem prime_1410911 : Nat.Prime 1410911 := by
  apply nodeValid_prime [2, 5, 199, 709] ⟨1410911, 13, [(2, 1), (5, 1), (199, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_709
  · decide +kernel

theorem prime_1681991 : Nat.Prime 1681991 := by
  apply nodeValid_prime [2, 5, 23, 71, 103] ⟨1681991, 11, [(2, 1), (5, 1), (23, 1), (71, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_71
    · exact prime_103
  · decide +kernel

theorem prime_1986581 : Nat.Prime 1986581 := by
  apply nodeValid_prime [2, 5, 71, 1399] ⟨1986581, 2, [(2, 2), (5, 1), (71, 1), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_1399
  · decide +kernel

theorem prime_2395541 : Nat.Prime 2395541 := by
  apply nodeValid_prime [2, 5, 7, 71, 241] ⟨2395541, 2, [(2, 2), (5, 1), (7, 1), (71, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_241
  · decide +kernel

theorem prime_2437507 : Nat.Prime 2437507 := by
  apply nodeValid_prime [2, 3, 45139] ⟨2437507, 2, [(2, 1), (3, 3), (45139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45139
  · decide +kernel

theorem prime_2542187 : Nat.Prime 2542187 := by
  apply nodeValid_prime [2, 31, 131, 313] ⟨2542187, 2, [(2, 1), (31, 1), (131, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_131
    · exact prime_313
  · decide +kernel

theorem prime_3585679 : Nat.Prime 3585679 := by
  apply nodeValid_prime [2, 3, 597613] ⟨3585679, 6, [(2, 1), (3, 1), (597613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_597613
  · decide +kernel

theorem prime_4116449 : Nat.Prime 4116449 := by
  apply nodeValid_prime [2, 7, 17, 23, 47] ⟨4116449, 3, [(2, 5), (7, 1), (17, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_4284349 : Nat.Prime 4284349 := by
  apply nodeValid_prime [2, 3, 19, 23, 43] ⟨4284349, 2, [(2, 2), (3, 1), (19, 2), (23, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_43
  · decide +kernel

theorem prime_4704241 : Nat.Prime 4704241 := by
  apply nodeValid_prime [2, 3, 5, 17, 1153] ⟨4704241, 21, [(2, 4), (3, 1), (5, 1), (17, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1153
  · decide +kernel

theorem prime_5460067 : Nat.Prime 5460067 := by
  apply nodeValid_prime [2, 3, 303337] ⟨5460067, 2, [(2, 1), (3, 2), (303337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_303337
  · decide +kernel

theorem prime_5588243 : Nat.Prime 5588243 := by
  apply nodeValid_prime [2, 11, 19, 29, 461] ⟨5588243, 5, [(2, 1), (11, 1), (19, 1), (29, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_29
    · exact prime_461
  · decide +kernel

theorem prime_5894209 : Nat.Prime 5894209 := by
  apply nodeValid_prime [2, 3, 379] ⟨5894209, 11, [(2, 6), (3, 5), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
  · decide +kernel

theorem prime_6493367 : Nat.Prime 6493367 := by
  apply nodeValid_prime [2, 11, 295153] ⟨6493367, 10, [(2, 1), (11, 1), (295153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_295153
  · decide +kernel

theorem prime_6960419 : Nat.Prime 6960419 := by
  apply nodeValid_prime [2, 47, 74047] ⟨6960419, 2, [(2, 1), (47, 1), (74047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_74047
  · decide +kernel

theorem prime_7673819 : Nat.Prime 7673819 := by
  apply nodeValid_prime [2, 109, 35201] ⟨7673819, 2, [(2, 1), (109, 1), (35201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_35201
  · decide +kernel

theorem prime_9750029 : Nat.Prime 9750029 := by
  apply nodeValid_prime [2, 2437507] ⟨9750029, 2, [(2, 2), (2437507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2437507
  · decide +kernel

theorem prime_10821001 : Nat.Prime 10821001 := by
  apply nodeValid_prime [2, 3, 5, 3607] ⟨10821001, 31, [(2, 3), (3, 1), (5, 3), (3607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3607
  · decide +kernel

theorem prime_12944951 : Nat.Prime 12944951 := by
  apply nodeValid_prime [2, 5, 199, 1301] ⟨12944951, 13, [(2, 1), (5, 2), (199, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_1301
  · decide +kernel

theorem prime_14734297 : Nat.Prime 14734297 := by
  apply nodeValid_prime [2, 3, 113, 1811] ⟨14734297, 13, [(2, 3), (3, 2), (113, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_1811
  · decide +kernel

theorem prime_16923601 : Nat.Prime 16923601 := by
  apply nodeValid_prime [2, 3, 5, 1567] ⟨16923601, 26, [(2, 4), (3, 3), (5, 2), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1567
  · decide +kernel

theorem prime_18072157 : Nat.Prime 18072157 := by
  apply nodeValid_prime [2, 3, 17, 88589] ⟨18072157, 2, [(2, 2), (3, 1), (17, 1), (88589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_88589
  · decide +kernel

theorem prime_19500059 : Nat.Prime 19500059 := by
  apply nodeValid_prime [2, 9750029] ⟨19500059, 2, [(2, 1), (9750029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9750029
  · decide +kernel

theorem prime_25755533 : Nat.Prime 25755533 := by
  apply nodeValid_prime [2, 11, 89, 6577] ⟨25755533, 2, [(2, 2), (11, 1), (89, 1), (6577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
    · exact prime_6577
  · decide +kernel

theorem prime_26087059 : Nat.Prime 26087059 := by
  apply nodeValid_prime [2, 3, 31, 46751] ⟨26087059, 2, [(2, 1), (3, 2), (31, 1), (46751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_46751
  · decide +kernel

theorem prime_28966309 : Nat.Prime 28966309 := by
  apply nodeValid_prime [2, 3, 7, 419, 823] ⟨28966309, 2, [(2, 2), (3, 1), (7, 1), (419, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_419
    · exact prime_823
  · decide +kernel

theorem prime_37141339 : Nat.Prime 37141339 := by
  apply nodeValid_prime [2, 3, 13, 83, 5737] ⟨37141339, 2, [(2, 1), (3, 1), (13, 1), (83, 1), (5737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
    · exact prime_5737
  · decide +kernel

theorem prime_42917851 : Nat.Prime 42917851 := by
  apply nodeValid_prime [2, 3, 5, 10597] ⟨42917851, 2, [(2, 1), (3, 4), (5, 2), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10597
  · decide +kernel

theorem prime_56313769 : Nat.Prime 56313769 := by
  apply nodeValid_prime [2, 3, 7, 67, 5003] ⟨56313769, 11, [(2, 3), (3, 1), (7, 1), (67, 1), (5003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
    · exact prime_5003
  · decide +kernel

theorem prime_57232519 : Nat.Prime 57232519 := by
  apply nodeValid_prime [2, 3, 7, 61, 89, 251] ⟨57232519, 3, [(2, 1), (3, 1), (7, 1), (61, 1), (89, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_89
    · exact prime_251
  · decide +kernel

theorem prime_58073789 : Nat.Prime 58073789 := by
  apply nodeValid_prime [2, 31, 101, 4637] ⟨58073789, 2, [(2, 2), (31, 1), (101, 1), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_101
    · exact prime_4637
  · decide +kernel

theorem prime_70543273 : Nat.Prime 70543273 := by
  apply nodeValid_prime [2, 3, 367, 8009] ⟨70543273, 5, [(2, 3), (3, 1), (367, 1), (8009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_8009
  · decide +kernel

theorem prime_77243993 : Nat.Prime 77243993 := by
  apply nodeValid_prime [2, 7, 101, 1951] ⟨77243993, 3, [(2, 3), (7, 2), (101, 1), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_1951
  · decide +kernel

theorem prime_84099551 : Nat.Prime 84099551 := by
  apply nodeValid_prime [2, 5, 1681991] ⟨84099551, 7, [(2, 1), (5, 2), (1681991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1681991
  · decide +kernel

theorem prime_92677339 : Nat.Prime 92677339 := by
  apply nodeValid_prime [2, 3, 13, 132019] ⟨92677339, 2, [(2, 1), (3, 3), (13, 1), (132019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_132019
  · decide +kernel

theorem prime_102462121 : Nat.Prime 102462121 := by
  apply nodeValid_prime [2, 3, 5, 43, 6619] ⟨102462121, 7, [(2, 3), (3, 2), (5, 1), (43, 1), (6619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_6619
  · decide +kernel

theorem prime_132940417 : Nat.Prime 132940417 := by
  apply nodeValid_prime [2, 3, 7, 19, 137] ⟨132940417, 15, [(2, 7), (3, 1), (7, 1), (19, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_250296931 : Nat.Prime 250296931 := by
  apply nodeValid_prime [2, 3, 5, 13, 213929] ⟨250296931, 2, [(2, 1), (3, 2), (5, 1), (13, 1), (213929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_213929
  · decide +kernel

theorem prime_257241461 : Nat.Prime 257241461 := by
  apply nodeValid_prime [2, 5, 7, 743, 2473] ⟨257241461, 2, [(2, 2), (5, 1), (7, 1), (743, 1), (2473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_743
    · exact prime_2473
  · decide +kernel

theorem prime_277733399 : Nat.Prime 277733399 := by
  apply nodeValid_prime [2, 71, 139, 14071] ⟨277733399, 11, [(2, 1), (71, 1), (139, 1), (14071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_139
    · exact prime_14071
  · decide +kernel

theorem prime_279637469 : Nat.Prime 279637469 := by
  apply nodeValid_prime [2, 11, 1051, 6047] ⟨279637469, 2, [(2, 2), (11, 1), (1051, 1), (6047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1051
    · exact prime_6047
  · decide +kernel

theorem prime_461784943 : Nat.Prime 461784943 := by
  apply nodeValid_prime [2, 3, 83, 197, 523] ⟨461784943, 3, [(2, 1), (3, 3), (83, 1), (197, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_197
    · exact prime_523
  · decide +kernel

theorem prime_475035203 : Nat.Prime 475035203 := by
  apply nodeValid_prime [2, 257, 467, 1979] ⟨475035203, 2, [(2, 1), (257, 1), (467, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_467
    · exact prime_1979
  · decide +kernel

theorem prime_808676203 : Nat.Prime 808676203 := by
  apply nodeValid_prime [2, 3, 137, 983791] ⟨808676203, 2, [(2, 1), (3, 1), (137, 1), (983791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_983791
  · decide +kernel

theorem prime_1090181299 : Nat.Prime 1090181299 := by
  apply nodeValid_prime [2, 3, 173, 863, 1217] ⟨1090181299, 2, [(2, 1), (3, 1), (173, 1), (863, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_863
    · exact prime_1217
  · decide +kernel

theorem prime_1523620409 : Nat.Prime 1523620409 := by
  apply nodeValid_prime [2, 487, 391073] ⟨1523620409, 3, [(2, 3), (487, 1), (391073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_391073
  · decide +kernel

theorem prime_1596843047 : Nat.Prime 1596843047 := by
  apply nodeValid_prime [2, 31, 25755533] ⟨1596843047, 5, [(2, 1), (31, 1), (25755533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_25755533
  · decide +kernel

theorem prime_2146797481 : Nat.Prime 2146797481 := by
  apply nodeValid_prime [2, 3, 5, 89, 201011] ⟨2146797481, 7, [(2, 3), (3, 1), (5, 1), (89, 1), (201011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_201011
  · decide +kernel

theorem prime_4411418629 : Nat.Prime 4411418629 := by
  apply nodeValid_prime [2, 3, 691, 532009] ⟨4411418629, 2, [(2, 2), (3, 1), (691, 1), (532009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_532009
  · decide +kernel

theorem prime_5449399523 : Nat.Prime 5449399523 := by
  apply nodeValid_prime [2, 7, 23, 16923601] ⟨5449399523, 2, [(2, 1), (7, 1), (23, 1), (16923601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_16923601
  · decide +kernel

theorem prime_7853155201 : Nat.Prime 7853155201 := by
  apply nodeValid_prime [2, 3, 5, 11, 8263] ⟨7853155201, 14, [(2, 7), (3, 3), (5, 2), (11, 1), (8263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_8263
  · decide +kernel

theorem prime_10077629123 : Nat.Prime 10077629123 := by
  apply nodeValid_prime [2, 11, 73, 1867, 3361] ⟨10077629123, 2, [(2, 1), (11, 1), (73, 1), (1867, 1), (3361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_1867
    · exact prime_3361
  · decide +kernel

theorem prime_10420988647 : Nat.Prime 10420988647 := by
  apply nodeValid_prime [2, 3, 1231, 1410911] ⟨10420988647, 5, [(2, 1), (3, 1), (1231, 1), (1410911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1231
    · exact prime_1410911
  · decide +kernel

theorem prime_10895956417 : Nat.Prime 10895956417 := by
  apply nodeValid_prime [2, 3, 167, 227, 499] ⟨10895956417, 7, [(2, 6), (3, 2), (167, 1), (227, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_227
    · exact prime_499
  · decide +kernel

theorem prime_15732717397 : Nat.Prime 15732717397 := by
  apply nodeValid_prime [2, 3, 11, 47, 83, 30553] ⟨15732717397, 2, [(2, 2), (3, 1), (11, 1), (47, 1), (83, 1), (30553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_83
    · exact prime_30553
  · decide +kernel

theorem prime_20155258247 : Nat.Prime 20155258247 := by
  apply nodeValid_prime [2, 10077629123] ⟨20155258247, 5, [(2, 1), (10077629123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10077629123
  · decide +kernel

theorem prime_370559164837 : Nat.Prime 370559164837 := by
  apply nodeValid_prime [2, 3, 7, 4411418629] ⟨370559164837, 5, [(2, 2), (3, 1), (7, 1), (4411418629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4411418629
  · decide +kernel

theorem prime_551530822723 : Nat.Prime 551530822723 := by
  apply nodeValid_prime [2, 3, 11, 19, 31, 331, 42863] ⟨551530822723, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (31, 1), (331, 1), (42863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_31
    · exact prime_331
    · exact prime_42863
  · decide +kernel

theorem prime_555053789671 : Nat.Prime 555053789671 := by
  apply nodeValid_prime [2, 3, 5, 14699, 1258711] ⟨555053789671, 3, [(2, 1), (3, 1), (5, 1), (14699, 1), (1258711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14699
    · exact prime_1258711
  · decide +kernel

theorem prime_833169277601 : Nat.Prime 833169277601 := by
  apply nodeValid_prime [2, 5, 11, 23, 4116449] ⟨833169277601, 3, [(2, 5), (5, 2), (11, 1), (23, 1), (4116449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_4116449
  · decide +kernel

theorem prime_833758127051 : Nat.Prime 833758127051 := by
  apply nodeValid_prime [2, 5, 23, 67, 10821001] ⟨833758127051, 6, [(2, 1), (5, 2), (23, 1), (67, 1), (10821001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_67
    · exact prime_10821001
  · decide +kernel

theorem prime_1099939828241 : Nat.Prime 1099939828241 := by
  apply nodeValid_prime [2, 5, 11, 73, 1447, 11833] ⟨1099939828241, 6, [(2, 4), (5, 1), (11, 1), (73, 1), (1447, 1), (11833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_73
    · exact prime_1447
    · exact prime_11833
  · decide +kernel

theorem prime_1667516254039 : Nat.Prime 1667516254039 := by
  apply nodeValid_prime [2, 3, 17, 5449399523] ⟨1667516254039, 3, [(2, 1), (3, 2), (17, 1), (5449399523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_5449399523
  · decide +kernel

theorem prime_6557625772513 : Nat.Prime 6557625772513 := by
  apply nodeValid_prime [2, 3, 1213, 56313769] ⟨6557625772513, 5, [(2, 5), (3, 1), (1213, 1), (56313769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1213
    · exact prime_56313769
  · decide +kernel

theorem prime_6557625799631 : Nat.Prime 6557625799631 := by
  apply nodeValid_prime [2, 5, 457, 599, 2395541] ⟨6557625799631, 7, [(2, 1), (5, 1), (457, 1), (599, 1), (2395541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_457
    · exact prime_599
    · exact prime_2395541
  · decide +kernel

theorem prime_6557625799787 : Nat.Prime 6557625799787 := by
  apply nodeValid_prime [2, 167, 3331, 5894209] ⟨6557625799787, 2, [(2, 1), (167, 1), (3331, 1), (5894209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_3331
    · exact prime_5894209
  · decide +kernel

theorem prime_6562284931387 : Nat.Prime 6562284931387 := by
  apply nodeValid_prime [2, 3, 65239, 5588243] ⟨6562284931387, 2, [(2, 1), (3, 2), (65239, 1), (5588243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_65239
    · exact prime_5588243
  · decide +kernel

theorem prime_6562284936787 : Nat.Prime 6562284936787 := by
  apply nodeValid_prime [2, 3, 23, 79, 101, 1986581] ⟨6562284936787, 3, [(2, 1), (3, 2), (23, 1), (79, 1), (101, 1), (1986581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_79
    · exact prime_101
    · exact prime_1986581
  · decide +kernel

theorem prime_6562284936959 : Nat.Prime 6562284936959 := by
  apply nodeValid_prime [2, 13109, 250296931] ⟨6562284936959, 11, [(2, 1), (13109, 1), (250296931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13109
    · exact prime_250296931
  · decide +kernel

theorem prime_6566946217213 : Nat.Prime 6566946217213 := by
  apply nodeValid_prime [2, 3, 41, 311, 42917851] ⟨6566946217213, 2, [(2, 2), (3, 1), (41, 1), (311, 1), (42917851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_311
    · exact prime_42917851
  · decide +kernel

theorem prime_6566946217849 : Nat.Prime 6566946217849 := by
  apply nodeValid_prime [2, 3, 23, 22691, 174763] ⟨6566946217849, 7, [(2, 3), (3, 2), (23, 1), (22691, 1), (174763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_22691
    · exact prime_174763
  · decide +kernel

theorem prime_6566946338929 : Nat.Prime 6566946338929 := by
  apply nodeValid_prime [2, 3, 105319, 1299019] ⟨6566946338929, 13, [(2, 4), (3, 1), (105319, 1), (1299019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105319
    · exact prime_1299019
  · decide +kernel

theorem prime_6571609948469 : Nat.Prime 6571609948469 := by
  apply nodeValid_prime [2, 21269, 77243993] ⟨6571609948469, 2, [(2, 2), (21269, 1), (77243993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21269
    · exact prime_77243993
  · decide +kernel

theorem prime_6571609948511 : Nat.Prime 6571609948511 := by
  apply nodeValid_prime [2, 5, 419, 1223, 1282423] ⟨6571609948511, 11, [(2, 1), (5, 1), (419, 1), (1223, 1), (1282423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_419
    · exact prime_1223
    · exact prime_1282423
  · decide +kernel

theorem prime_6571609985081 : Nat.Prime 6571609985081 := by
  apply nodeValid_prime [2, 5, 7, 17, 79, 157, 1409] ⟨6571609985081, 3, [(2, 3), (5, 1), (7, 1), (17, 1), (79, 2), (157, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_79
    · exact prime_157
    · exact prime_1409
  · decide +kernel

theorem prime_6576275865031 : Nat.Prime 6576275865031 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 31, 197, 82139] ⟨6576275865031, 13, [(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (31, 1), (197, 1), (82139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_31
    · exact prime_197
    · exact prime_82139
  · decide +kernel

theorem prime_6576275866361 : Nat.Prime 6576275866361 := by
  apply nodeValid_prime [2, 5, 19, 149, 58073789] ⟨6576275866361, 3, [(2, 3), (5, 1), (19, 1), (149, 1), (58073789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_149
    · exact prime_58073789
  · decide +kernel

theorem prime_6576275871947 : Nat.Prime 6576275871947 := by
  apply nodeValid_prime [2, 11, 19, 15732717397] ⟨6576275871947, 2, [(2, 1), (11, 1), (19, 1), (15732717397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_15732717397
  · decide +kernel

theorem prime_6580943998393 : Nat.Prime 6580943998393 := by
  apply nodeValid_prime [2, 3, 251, 10007, 109169] ⟨6580943998393, 10, [(2, 3), (3, 1), (251, 1), (10007, 1), (109169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_10007
    · exact prime_109169
  · decide +kernel

theorem prime_6580944057901 : Nat.Prime 6580944057901 := by
  apply nodeValid_prime [2, 3, 5, 108377, 202409] ⟨6580944057901, 6, [(2, 2), (3, 1), (5, 2), (108377, 1), (202409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_108377
    · exact prime_202409
  · decide +kernel

theorem prime_6580944058439 : Nat.Prime 6580944058439 := by
  apply nodeValid_prime [2, 419, 7853155201] ⟨6580944058439, 7, [(2, 1), (419, 1), (7853155201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_7853155201
  · decide +kernel

theorem prime_6585614357089 : Nat.Prime 6585614357089 := by
  apply nodeValid_prime [2, 3, 13, 19, 277733399] ⟨6585614357089, 7, [(2, 5), (3, 1), (13, 1), (19, 1), (277733399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_277733399
  · decide +kernel

theorem prime_6585614357689 : Nat.Prime 6585614357689 := by
  apply nodeValid_prime [2, 3, 17, 773, 6960419] ⟨6585614357689, 19, [(2, 3), (3, 2), (17, 1), (773, 1), (6960419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_773
    · exact prime_6960419
  · decide +kernel

theorem prime_6585614371741 : Nat.Prime 6585614371741 := by
  apply nodeValid_prime [2, 3, 5, 61, 139, 12944951] ⟨6585614371741, 2, [(2, 2), (3, 1), (5, 1), (61, 1), (139, 1), (12944951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_139
    · exact prime_12944951
  · decide +kernel

theorem prime_6590286965137 : Nat.Prime 6590286965137 := by
  apply nodeValid_prime [2, 3, 7, 73, 109, 227, 10859] ⟨6590286965137, 11, [(2, 4), (3, 1), (7, 1), (73, 1), (109, 1), (227, 1), (10859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_109
    · exact prime_227
    · exact prime_10859
  · decide +kernel

theorem prime_6590286965959 : Nat.Prime 6590286965959 := by
  apply nodeValid_prime [2, 3, 17, 127, 349, 859, 1697] ⟨6590286965959, 3, [(2, 1), (3, 1), (17, 1), (127, 1), (349, 1), (859, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_127
    · exact prime_349
    · exact prime_859
    · exact prime_1697
  · decide +kernel

theorem prime_6590286995843 : Nat.Prime 6590286995843 := by
  apply nodeValid_prime [2, 11, 46133, 6493367] ⟨6590286995843, 2, [(2, 1), (11, 1), (46133, 1), (6493367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_46133
    · exact prime_6493367
  · decide +kernel

theorem prime_6594961783469 : Nat.Prime 6594961783469 := by
  apply nodeValid_prime [2, 29, 37, 2579, 595801] ⟨6594961783469, 2, [(2, 2), (29, 1), (37, 1), (2579, 1), (595801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_2579
    · exact prime_595801
  · decide +kernel

theorem prime_6594961784111 : Nat.Prime 6594961784111 := by
  apply nodeValid_prime [2, 5, 7, 59, 1596843047] ⟨6594961784111, 7, [(2, 1), (5, 1), (7, 1), (59, 1), (1596843047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_1596843047
  · decide +kernel

theorem prime_6594961861633 : Nat.Prime 6594961861633 := by
  apply nodeValid_prime [2, 3, 2146797481] ⟨6594961861633, 10, [(2, 10), (3, 1), (2146797481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2146797481
  · decide +kernel

theorem prime_6599638968079 : Nat.Prime 6599638968079 := by
  apply nodeValid_prime [2, 3, 13, 4339, 19500059] ⟨6599638968079, 6, [(2, 1), (3, 1), (13, 1), (4339, 1), (19500059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4339
    · exact prime_19500059
  · decide +kernel

theorem prime_6599638969271 : Nat.Prime 6599638969271 := by
  apply nodeValid_prime [2, 5, 47, 953, 14734297] ⟨6599638969271, 19, [(2, 1), (5, 1), (47, 1), (953, 1), (14734297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_953
    · exact prime_14734297
  · decide +kernel

theorem prime_6599638969447 : Nat.Prime 6599638969447 := by
  apply nodeValid_prime [2, 3, 1099939828241] ⟨6599638969447, 3, [(2, 1), (3, 1), (1099939828241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1099939828241
  · decide +kernel

theorem prime_6604318309343 : Nat.Prime 6604318309343 := by
  apply nodeValid_prime [2, 13, 233, 1090181299] ⟨6604318309343, 5, [(2, 1), (13, 1), (233, 1), (1090181299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_233
    · exact prime_1090181299
  · decide +kernel

theorem prime_6604318452001 : Nat.Prime 6604318452001 := by
  apply nodeValid_prime [2, 3, 5, 19, 28966309] ⟨6604318452001, 11, [(2, 5), (3, 1), (5, 3), (19, 1), (28966309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_28966309
  · decide +kernel

theorem prime_6604318454257 : Nat.Prime 6604318454257 := by
  apply nodeValid_prime [2, 3, 491, 1153, 81013] ⟨6604318454257, 5, [(2, 4), (3, 2), (491, 1), (1153, 1), (81013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_491
    · exact prime_1153
    · exact prime_81013
  · decide +kernel

theorem prime_6608999875297 : Nat.Prime 6608999875297 := by
  apply nodeValid_prime [2, 3, 7, 13, 29, 26087059] ⟨6608999875297, 5, [(2, 5), (3, 1), (7, 1), (13, 1), (29, 1), (26087059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_26087059
  · decide +kernel

theorem prime_6608999875561 : Nat.Prime 6608999875561 := by
  apply nodeValid_prime [2, 3, 5, 7177, 7673819] ⟨6608999875561, 13, [(2, 3), (3, 1), (5, 1), (7177, 1), (7673819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7177
    · exact prime_7673819
  · decide +kernel

theorem prime_6608999890739 : Nat.Prime 6608999890739 := by
  apply nodeValid_prime [2, 7, 53, 67, 132940417] ⟨6608999890739, 2, [(2, 1), (7, 1), (53, 1), (67, 1), (132940417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_67
    · exact prime_132940417
  · decide +kernel

theorem prime_6613683719897 : Nat.Prime 6613683719897 := by
  apply nodeValid_prime [2, 11, 179287, 419191] ⟨6613683719897, 3, [(2, 3), (11, 1), (179287, 1), (419191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_179287
    · exact prime_419191
  · decide +kernel

theorem prime_6613683953053 : Nat.Prime 6613683953053 := by
  apply nodeValid_prime [2, 3, 11, 19, 71, 37141339] ⟨6613683953053, 5, [(2, 2), (3, 1), (11, 1), (19, 1), (71, 1), (37141339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_71
    · exact prime_37141339
  · decide +kernel

theorem prime_6613683953647 : Nat.Prime 6613683953647 := by
  apply nodeValid_prime [2, 3, 7, 11, 31, 461784943] ⟨6613683953647, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (31, 1), (461784943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_461784943
  · decide +kernel

theorem prime_6618369794111 : Nat.Prime 6618369794111 := by
  apply nodeValid_prime [2, 5, 31, 41897, 509573] ⟨6618369794111, 11, [(2, 1), (5, 1), (31, 1), (41897, 1), (509573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_41897
    · exact prime_509573
  · decide +kernel

theorem prime_6618369872677 : Nat.Prime 6618369872677 := by
  apply nodeValid_prime [2, 3, 551530822723] ⟨6618369872677, 2, [(2, 2), (3, 1), (551530822723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_551530822723
  · decide +kernel

theorem prime_6618369872861 : Nat.Prime 6618369872861 := by
  apply nodeValid_prime [2, 5, 4691, 70543273] ⟨6618369872861, 2, [(2, 2), (5, 1), (4691, 1), (70543273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4691
    · exact prime_70543273
  · decide +kernel

theorem prime_6623058102571 : Nat.Prime 6623058102571 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 808676203] ⟨6623058102571, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (808676203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_808676203
  · decide +kernel

theorem prime_6623058103621 : Nat.Prime 6623058103621 := by
  apply nodeValid_prime [2, 3, 5, 7, 6203, 2542187] ⟨6623058103621, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (6203, 1), (2542187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_6203
    · exact prime_2542187
  · decide +kernel

theorem prime_6623058121639 : Nat.Prime 6623058121639 := by
  apply nodeValid_prime [2, 3, 7, 17, 19, 2791, 24989] ⟨6623058121639, 6, [(2, 1), (3, 1), (7, 2), (17, 1), (19, 1), (2791, 1), (24989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
    · exact prime_2791
    · exact prime_24989
  · decide +kernel

theorem prime_6627748694009 : Nat.Prime 6627748694009 := by
  apply nodeValid_prime [2, 13, 19, 23, 31, 4704241] ⟨6627748694009, 3, [(2, 3), (13, 1), (19, 1), (23, 1), (31, 1), (4704241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_23
    · exact prime_31
    · exact prime_4704241
  · decide +kernel

theorem prime_6627748779151 : Nat.Prime 6627748779151 := by
  apply nodeValid_prime [2, 3, 5, 29, 1523620409] ⟨6627748779151, 13, [(2, 1), (3, 1), (5, 2), (29, 1), (1523620409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1523620409
  · decide +kernel

theorem prime_6627748779493 : Nat.Prime 6627748779493 := by
  apply nodeValid_prime [2, 3, 53, 10420988647] ⟨6627748779493, 5, [(2, 2), (3, 1), (53, 1), (10420988647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_10420988647
  · decide +kernel

theorem prime_6632441489743 : Nat.Prime 6632441489743 := by
  apply nodeValid_prime [2, 3, 59, 67, 279637469] ⟨6632441489743, 5, [(2, 1), (3, 1), (59, 1), (67, 1), (279637469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_67
    · exact prime_279637469
  · decide +kernel

theorem prime_6632441489873 : Nat.Prime 6632441489873 := by
  apply nodeValid_prime [2, 11, 19, 79, 103, 22159] ⟨6632441489873, 3, [(2, 4), (11, 2), (19, 1), (79, 1), (103, 1), (22159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_79
    · exact prime_103
    · exact prime_22159
  · decide +kernel

theorem prime_6632441504287 : Nat.Prime 6632441504287 := by
  apply nodeValid_prime [2, 3, 13, 179, 475035203] ⟨6632441504287, 6, [(2, 1), (3, 1), (13, 1), (179, 1), (475035203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_179
    · exact prime_475035203
  · decide +kernel

theorem prime_6637136554381 : Nat.Prime 6637136554381 := by
  apply nodeValid_prime [2, 3, 5, 150571, 734663] ⟨6637136554381, 10, [(2, 2), (3, 1), (5, 1), (150571, 1), (734663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_150571
    · exact prime_734663
  · decide +kernel

theorem prime_6637136564921 : Nat.Prime 6637136564921 := by
  apply nodeValid_prime [2, 5, 1973, 84099551] ⟨6637136564921, 3, [(2, 3), (5, 1), (1973, 1), (84099551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1973
    · exact prime_84099551
  · decide +kernel

theorem prime_6637136566157 : Nat.Prime 6637136566157 := by
  apply nodeValid_prime [2, 1543, 18803, 57191] ⟨6637136566157, 2, [(2, 2), (1543, 1), (18803, 1), (57191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1543
    · exact prime_18803
    · exact prime_57191
  · decide +kernel

theorem prime_6641833829951 : Nat.Prime 6641833829951 := by
  apply nodeValid_prime [2, 5, 11, 211, 57232519] ⟨6641833829951, 11, [(2, 1), (5, 2), (11, 1), (211, 1), (57232519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_211
    · exact prime_57232519
  · decide +kernel

theorem prime_6641833830097 : Nat.Prime 6641833830097 := by
  apply nodeValid_prime [2, 3, 19, 40813, 178441] ⟨6641833830097, 5, [(2, 4), (3, 1), (19, 1), (40813, 1), (178441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_40813
    · exact prime_178441
  · decide +kernel

theorem prime_6641833858109 : Nat.Prime 6641833858109 := by
  apply nodeValid_prime [2, 71, 83, 16421, 17159] ⟨6641833858109, 2, [(2, 2), (71, 1), (83, 1), (16421, 1), (17159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_83
    · exact prime_16421
    · exact prime_17159
  · decide +kernel

theorem prime_6646533389849 : Nat.Prime 6646533389849 := by
  apply nodeValid_prime [2, 11, 17, 61, 4284349] ⟨6646533389849, 3, [(2, 3), (11, 1), (17, 2), (61, 1), (4284349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_61
    · exact prime_4284349
  · decide +kernel

theorem prime_6646533394079 : Nat.Prime 6646533394079 := by
  apply nodeValid_prime [2, 23, 131, 1223, 901861] ⟨6646533394079, 13, [(2, 1), (23, 1), (131, 1), (1223, 1), (901861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_131
    · exact prime_1223
    · exact prime_901861
  · decide +kernel

theorem prime_6646533414371 : Nat.Prime 6646533414371 := by
  apply nodeValid_prime [2, 5, 61, 10895956417] ⟨6646533414371, 2, [(2, 1), (5, 1), (61, 1), (10895956417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_10895956417
  · decide +kernel

theorem prime_6651235215617 : Nat.Prime 6651235215617 := by
  apply nodeValid_prime [2, 101, 257241461] ⟨6651235215617, 3, [(2, 8), (101, 1), (257241461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_257241461
  · decide +kernel

theorem prime_6651235216721 : Nat.Prime 6651235216721 := by
  apply nodeValid_prime [2, 5, 15227, 5460067] ⟨6651235216721, 3, [(2, 4), (5, 1), (15227, 1), (5460067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15227
    · exact prime_5460067
  · decide +kernel

theorem prime_6651235221511 : Nat.Prime 6651235221511 := by
  apply nodeValid_prime [2, 3, 5, 11, 20155258247] ⟨6651235221511, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (20155258247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_20155258247
  · decide +kernel

theorem prime_6655939278787 : Nat.Prime 6655939278787 := by
  apply nodeValid_prime [2, 3, 7, 37, 79, 18072157] ⟨6655939278787, 7, [(2, 1), (3, 2), (7, 1), (37, 1), (79, 1), (18072157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_79
    · exact prime_18072157
  · decide +kernel

theorem prime_6655939379927 : Nat.Prime 6655939379927 := by
  apply nodeValid_prime [2, 17, 83, 359, 1049, 6263] ⟨6655939379927, 5, [(2, 1), (17, 1), (83, 1), (359, 1), (1049, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_83
    · exact prime_359
    · exact prime_1049
    · exact prime_6263
  · decide +kernel

theorem prime_6655939380161 : Nat.Prime 6655939380161 := by
  apply nodeValid_prime [2, 5, 7, 29, 102462121] ⟨6655939380161, 3, [(2, 6), (5, 1), (7, 1), (29, 1), (102462121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_102462121
  · decide +kernel

theorem prime_6660645476053 : Nat.Prime 6660645476053 := by
  apply nodeValid_prime [2, 3, 555053789671] ⟨6660645476053, 2, [(2, 2), (3, 1), (555053789671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_555053789671
  · decide +kernel

theorem prime_6660645476057 : Nat.Prime 6660645476057 := by
  apply nodeValid_prime [2, 11, 13, 53, 1667, 65899] ⟨6660645476057, 3, [(2, 3), (11, 1), (13, 1), (53, 1), (1667, 1), (65899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_53
    · exact prime_1667
    · exact prime_65899
  · decide +kernel

theorem prime_6660645588161 : Nat.Prime 6660645588161 := by
  apply nodeValid_prime [2, 5, 1021, 4357, 4679] ⟨6660645588161, 3, [(2, 6), (5, 1), (1021, 1), (4357, 1), (4679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1021
    · exact prime_4357
    · exact prime_4679
  · decide +kernel

theorem prime_6665354150879 : Nat.Prime 6665354150879 := by
  apply nodeValid_prime [2, 17, 54673, 3585679] ⟨6665354150879, 7, [(2, 1), (17, 1), (54673, 1), (3585679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_54673
    · exact prime_3585679
  · decide +kernel

theorem prime_6665354220809 : Nat.Prime 6665354220809 := by
  apply nodeValid_prime [2, 833169277601] ⟨6665354220809, 3, [(2, 3), (833169277601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_833169277601
  · decide +kernel

theorem prime_6665354220881 : Nat.Prime 6665354220881 := by
  apply nodeValid_prime [2, 5, 29, 31, 92677339] ⟨6665354220881, 3, [(2, 4), (5, 1), (29, 1), (31, 1), (92677339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_31
    · exact prime_92677339
  · decide +kernel

theorem prime_6670064967067 : Nat.Prime 6670064967067 := by
  apply nodeValid_prime [2, 3, 370559164837] ⟨6670064967067, 3, [(2, 1), (3, 2), (370559164837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_370559164837
  · decide +kernel

theorem prime_6670065016157 : Nat.Prime 6670065016157 := by
  apply nodeValid_prime [2, 1667516254039] ⟨6670065016157, 2, [(2, 2), (1667516254039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1667516254039
  · decide +kernel

theorem prime_6670065016409 : Nat.Prime 6670065016409 := by
  apply nodeValid_prime [2, 833758127051] ⟨6670065016409, 3, [(2, 3), (833758127051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_833758127051
  · decide +kernel

end Sude.Lucas.Generated
