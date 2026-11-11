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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0080

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6829 : Nat.Prime 6829 := by
  apply nodeValid_prime [2, 3, 569] ⟨6829, 2, [(2, 2), (3, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
  · decide +kernel

theorem prime_10487 : Nat.Prime 10487 := by
  apply nodeValid_prime [2, 7, 107] ⟨10487, 5, [(2, 1), (7, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
  · decide +kernel

theorem prime_12791 : Nat.Prime 12791 := by
  apply nodeValid_prime [2, 5, 1279] ⟨12791, 7, [(2, 1), (5, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1279
  · decide +kernel

theorem prime_13781 : Nat.Prime 13781 := by
  apply nodeValid_prime [2, 5, 13, 53] ⟨13781, 7, [(2, 2), (5, 1), (13, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_16417 : Nat.Prime 16417 := by
  apply nodeValid_prime [2, 3, 19] ⟨16417, 10, [(2, 5), (3, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_16619 : Nat.Prime 16619 := by
  apply nodeValid_prime [2, 7, 1187] ⟨16619, 2, [(2, 1), (7, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1187
  · decide +kernel

theorem prime_17903 : Nat.Prime 17903 := by
  apply nodeValid_prime [2, 8951] ⟨17903, 5, [(2, 1), (8951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8951
  · decide +kernel

theorem prime_19183 : Nat.Prime 19183 := by
  apply nodeValid_prime [2, 3, 23, 139] ⟨19183, 3, [(2, 1), (3, 1), (23, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_139
  · decide +kernel

theorem prime_21503 : Nat.Prime 21503 := by
  apply nodeValid_prime [2, 13, 827] ⟨21503, 5, [(2, 1), (13, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_827
  · decide +kernel

theorem prime_25583 : Nat.Prime 25583 := by
  apply nodeValid_prime [2, 12791] ⟨25583, 5, [(2, 1), (12791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12791
  · decide +kernel

theorem prime_31193 : Nat.Prime 31193 := by
  apply nodeValid_prime [2, 7, 557] ⟨31193, 5, [(2, 3), (7, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_557
  · decide +kernel

theorem prime_36761 : Nat.Prime 36761 := by
  apply nodeValid_prime [2, 5, 919] ⟨36761, 6, [(2, 3), (5, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_919
  · decide +kernel

theorem prime_36929 : Nat.Prime 36929 := by
  apply nodeValid_prime [2, 577] ⟨36929, 3, [(2, 6), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_577
  · decide +kernel

theorem prime_37571 : Nat.Prime 37571 := by
  apply nodeValid_prime [2, 5, 13, 17] ⟨37571, 2, [(2, 1), (5, 1), (13, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_42821 : Nat.Prime 42821 := by
  apply nodeValid_prime [2, 5, 2141] ⟨42821, 2, [(2, 2), (5, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2141
  · decide +kernel

theorem prime_42953 : Nat.Prime 42953 := by
  apply nodeValid_prime [2, 7, 13, 59] ⟨42953, 3, [(2, 3), (7, 1), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_47599 : Nat.Prime 47599 := by
  apply nodeValid_prime [2, 3, 7933] ⟨47599, 3, [(2, 1), (3, 1), (7933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7933
  · decide +kernel

theorem prime_55843 : Nat.Prime 55843 := by
  apply nodeValid_prime [2, 3, 41, 227] ⟨55843, 2, [(2, 1), (3, 1), (41, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_227
  · decide +kernel

theorem prime_64301 : Nat.Prime 64301 := by
  apply nodeValid_prime [2, 5, 643] ⟨64301, 2, [(2, 2), (5, 2), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_643
  · decide +kernel

theorem prime_64303 : Nat.Prime 64303 := by
  apply nodeValid_prime [2, 3, 7, 1531] ⟨64303, 6, [(2, 1), (3, 1), (7, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1531
  · decide +kernel

theorem prime_69011 : Nat.Prime 69011 := by
  apply nodeValid_prime [2, 5, 67, 103] ⟨69011, 6, [(2, 1), (5, 1), (67, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_103
  · decide +kernel

theorem prime_69929 : Nat.Prime 69929 := by
  apply nodeValid_prime [2, 8741] ⟨69929, 3, [(2, 3), (8741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8741
  · decide +kernel

theorem prime_70627 : Nat.Prime 70627 := by
  apply nodeValid_prime [2, 3, 79, 149] ⟨70627, 7, [(2, 1), (3, 1), (79, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_149
  · decide +kernel

theorem prime_73523 : Nat.Prime 73523 := by
  apply nodeValid_prime [2, 36761] ⟨73523, 2, [(2, 1), (36761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36761
  · decide +kernel

theorem prime_73859 : Nat.Prime 73859 := by
  apply nodeValid_prime [2, 36929] ⟨73859, 2, [(2, 1), (36929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36929
  · decide +kernel

theorem prime_76261 : Nat.Prime 76261 := by
  apply nodeValid_prime [2, 3, 5, 31, 41] ⟨76261, 2, [(2, 2), (3, 1), (5, 1), (31, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_41
  · decide +kernel

theorem prime_77621 : Nat.Prime 77621 := by
  apply nodeValid_prime [2, 5, 3881] ⟨77621, 2, [(2, 2), (5, 1), (3881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3881
  · decide +kernel

theorem prime_81527 : Nat.Prime 81527 := by
  apply nodeValid_prime [2, 40763] ⟨81527, 5, [(2, 1), (40763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40763
  · decide +kernel

theorem prime_84631 : Nat.Prime 84631 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 31] ⟨84631, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_85643 : Nat.Prime 85643 := by
  apply nodeValid_prime [2, 42821] ⟨85643, 2, [(2, 1), (42821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42821
  · decide +kernel

theorem prime_85703 : Nat.Prime 85703 := by
  apply nodeValid_prime [2, 73, 587] ⟨85703, 5, [(2, 1), (73, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_587
  · decide +kernel

theorem prime_87427 : Nat.Prime 87427 := by
  apply nodeValid_prime [2, 3, 1619] ⟨87427, 2, [(2, 1), (3, 3), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1619
  · decide +kernel

theorem prime_95219 : Nat.Prime 95219 := by
  apply nodeValid_prime [2, 47609] ⟨95219, 2, [(2, 1), (47609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_47609
  · decide +kernel

theorem prime_96457 : Nat.Prime 96457 := by
  apply nodeValid_prime [2, 3, 4019] ⟨96457, 5, [(2, 3), (3, 1), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4019
  · decide +kernel

theorem prime_102001 : Nat.Prime 102001 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨102001, 31, [(2, 4), (3, 1), (5, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_115099 : Nat.Prime 115099 := by
  apply nodeValid_prime [2, 3, 19183] ⟨115099, 3, [(2, 1), (3, 1), (19183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19183
  · decide +kernel

theorem prime_116483 : Nat.Prime 116483 := by
  apply nodeValid_prime [2, 139, 419] ⟨116483, 2, [(2, 1), (139, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_419
  · decide +kernel

theorem prime_118891 : Nat.Prime 118891 := by
  apply nodeValid_prime [2, 3, 5, 1321] ⟨118891, 10, [(2, 1), (3, 2), (5, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1321
  · decide +kernel

theorem prime_119671 : Nat.Prime 119671 := by
  apply nodeValid_prime [2, 3, 5, 3989] ⟨119671, 3, [(2, 1), (3, 1), (5, 1), (3989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3989
  · decide +kernel

theorem prime_136607 : Nat.Prime 136607 := by
  apply nodeValid_prime [2, 167, 409] ⟨136607, 5, [(2, 1), (167, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_409
  · decide +kernel

theorem prime_143813 : Nat.Prime 143813 := by
  apply nodeValid_prime [2, 157, 229] ⟨143813, 2, [(2, 2), (157, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_229
  · decide +kernel

theorem prime_145487 : Nat.Prime 145487 := by
  apply nodeValid_prime [2, 11, 17, 389] ⟨145487, 5, [(2, 1), (11, 1), (17, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_389
  · decide +kernel

theorem prime_151703 : Nat.Prime 151703 := by
  apply nodeValid_prime [2, 101, 751] ⟨151703, 5, [(2, 1), (101, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_751
  · decide +kernel

theorem prime_153499 : Nat.Prime 153499 := by
  apply nodeValid_prime [2, 3, 25583] ⟨153499, 3, [(2, 1), (3, 1), (25583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25583
  · decide +kernel

theorem prime_170899 : Nat.Prime 170899 := by
  apply nodeValid_prime [2, 3, 7, 13, 313] ⟨170899, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_313
  · decide +kernel

theorem prime_174659 : Nat.Prime 174659 := by
  apply nodeValid_prime [2, 11, 17, 467] ⟨174659, 2, [(2, 1), (11, 1), (17, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_467
  · decide +kernel

theorem prime_209669 : Nat.Prime 209669 := by
  apply nodeValid_prime [2, 23, 43, 53] ⟨209669, 2, [(2, 2), (23, 1), (43, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
    · exact prime_53
  · decide +kernel

theorem prime_231169 : Nat.Prime 231169 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨231169, 17, [(2, 8), (3, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_245501 : Nat.Prime 245501 := by
  apply nodeValid_prime [2, 5, 491] ⟨245501, 2, [(2, 2), (5, 3), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_491
  · decide +kernel

theorem prime_258127 : Nat.Prime 258127 := by
  apply nodeValid_prime [2, 3, 11, 3911] ⟨258127, 5, [(2, 1), (3, 1), (11, 1), (3911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3911
  · decide +kernel

theorem prime_276763 : Nat.Prime 276763 := by
  apply nodeValid_prime [2, 3, 193, 239] ⟨276763, 5, [(2, 1), (3, 1), (193, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_239
  · decide +kernel

theorem prime_302833 : Nat.Prime 302833 := by
  apply nodeValid_prime [2, 3, 701] ⟨302833, 5, [(2, 4), (3, 3), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_701
  · decide +kernel

theorem prime_380327 : Nat.Prime 380327 := by
  apply nodeValid_prime [2, 397, 479] ⟨380327, 5, [(2, 1), (397, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_479
  · decide +kernel

theorem prime_388657 : Nat.Prime 388657 := by
  apply nodeValid_prime [2, 3, 2699] ⟨388657, 7, [(2, 4), (3, 2), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2699
  · decide +kernel

theorem prime_447353 : Nat.Prime 447353 := by
  apply nodeValid_prime [2, 199, 281] ⟨447353, 3, [(2, 3), (199, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_281
  · decide +kernel

theorem prime_487471 : Nat.Prime 487471 := by
  apply nodeValid_prime [2, 3, 5, 16249] ⟨487471, 3, [(2, 1), (3, 1), (5, 1), (16249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16249
  · decide +kernel

theorem prime_519031 : Nat.Prime 519031 := by
  apply nodeValid_prime [2, 3, 5, 73, 79] ⟨519031, 6, [(2, 1), (3, 2), (5, 1), (73, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_79
  · decide +kernel

theorem prime_573277 : Nat.Prime 573277 := by
  apply nodeValid_prime [2, 3, 11, 43, 101] ⟨573277, 7, [(2, 2), (3, 1), (11, 1), (43, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_101
  · decide +kernel

theorem prime_578183 : Nat.Prime 578183 := by
  apply nodeValid_prime [2, 11, 41, 641] ⟨578183, 5, [(2, 1), (11, 1), (41, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_641
  · decide +kernel

theorem prime_737533 : Nat.Prime 737533 := by
  apply nodeValid_prime [2, 3, 6829] ⟨737533, 2, [(2, 2), (3, 3), (6829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6829
  · decide +kernel

theorem prime_790693 : Nat.Prime 790693 := by
  apply nodeValid_prime [2, 3, 7, 9413] ⟨790693, 2, [(2, 2), (3, 1), (7, 1), (9413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9413
  · decide +kernel

theorem prime_910219 : Nat.Prime 910219 := by
  apply nodeValid_prime [2, 3, 151703] ⟨910219, 2, [(2, 1), (3, 1), (151703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151703
  · decide +kernel

theorem prime_1156367 : Nat.Prime 1156367 := by
  apply nodeValid_prime [2, 578183] ⟨1156367, 5, [(2, 1), (578183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_578183
  · decide +kernel

theorem prime_1204169 : Nat.Prime 1204169 := by
  apply nodeValid_prime [2, 7, 21503] ⟨1204169, 3, [(2, 3), (7, 1), (21503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_21503
  · decide +kernel

theorem prime_1548763 : Nat.Prime 1548763 := by
  apply nodeValid_prime [2, 3, 258127] ⟨1548763, 2, [(2, 1), (3, 1), (258127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_258127
  · decide +kernel

theorem prime_1708991 : Nat.Prime 1708991 := by
  apply nodeValid_prime [2, 5, 170899] ⟨1708991, 7, [(2, 1), (5, 1), (170899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_170899
  · decide +kernel

theorem prime_2930539 : Nat.Prime 2930539 := by
  apply nodeValid_prime [2, 3, 13, 37571] ⟨2930539, 3, [(2, 1), (3, 1), (13, 1), (37571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37571
  · decide +kernel

theorem prime_3439663 : Nat.Prime 3439663 := by
  apply nodeValid_prime [2, 3, 573277] ⟨3439663, 3, [(2, 1), (3, 1), (573277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_573277
  · decide +kernel

theorem prime_3618323 : Nat.Prime 3618323 := by
  apply nodeValid_prime [2, 19, 95219] ⟨3618323, 2, [(2, 1), (19, 1), (95219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_95219
  · decide +kernel

theorem prime_3964087 : Nat.Prime 3964087 := by
  apply nodeValid_prime [2, 3, 7, 10487] ⟨3964087, 5, [(2, 1), (3, 3), (7, 1), (10487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10487
  · decide +kernel

theorem prime_6215347 : Nat.Prime 6215347 := by
  apply nodeValid_prime [2, 3, 115099] ⟨6215347, 2, [(2, 1), (3, 3), (115099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115099
  · decide +kernel

theorem prime_6228373 : Nat.Prime 6228373 := by
  apply nodeValid_prime [2, 3, 519031] ⟨6228373, 5, [(2, 2), (3, 1), (519031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_519031
  · decide +kernel

theorem prime_6977329 : Nat.Prime 6977329 := by
  apply nodeValid_prime [2, 3, 145361] ⟨6977329, 11, [(2, 4), (3, 1), (145361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_145361
  · decide +kernel

theorem prime_6999533 : Nat.Prime 6999533 := by
  apply nodeValid_prime [2, 73, 23971] ⟨6999533, 2, [(2, 2), (73, 1), (23971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_23971
  · decide +kernel

theorem prime_7505129 : Nat.Prime 7505129 := by
  apply nodeValid_prime [2, 419, 2239] ⟨7505129, 3, [(2, 3), (419, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_2239
  · decide +kernel

theorem prime_8218139 : Nat.Prime 8218139 := by
  apply nodeValid_prime [2, 47, 87427] ⟨8218139, 2, [(2, 1), (47, 1), (87427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_87427
  · decide +kernel

theorem prime_9469763 : Nat.Prime 9469763 := by
  apply nodeValid_prime [2, 61, 77621] ⟨9469763, 2, [(2, 1), (61, 1), (77621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_77621
  · decide +kernel

theorem prime_10051003 : Nat.Prime 10051003 := by
  apply nodeValid_prime [2, 3, 13, 42953] ⟨10051003, 2, [(2, 1), (3, 2), (13, 1), (42953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_42953
  · decide +kernel

theorem prime_11719651 : Nat.Prime 11719651 := by
  apply nodeValid_prime [2, 3, 5, 23, 43, 79] ⟨11719651, 2, [(2, 1), (3, 1), (5, 2), (23, 1), (43, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_43
    · exact prime_79
  · decide +kernel

theorem prime_13512029 : Nat.Prime 13512029 := by
  apply nodeValid_prime [2, 29, 116483] ⟨13512029, 2, [(2, 2), (29, 1), (116483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_116483
  · decide +kernel

theorem prime_16587677 : Nat.Prime 16587677 := by
  apply nodeValid_prime [2, 7, 84631] ⟨16587677, 2, [(2, 2), (7, 2), (84631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_84631
  · decide +kernel

theorem prime_23563157 : Nat.Prime 23563157 := by
  apply nodeValid_prime [2, 17, 373, 929] ⟨23563157, 3, [(2, 2), (17, 1), (373, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_373
    · exact prime_929
  · decide +kernel

theorem prime_23902889 : Nat.Prime 23902889 := by
  apply nodeValid_prime [2, 23, 37, 3511] ⟨23902889, 3, [(2, 3), (23, 1), (37, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_3511
  · decide +kernel

theorem prime_29354713 : Nat.Prime 29354713 := by
  apply nodeValid_prime [2, 3, 359, 3407] ⟨29354713, 7, [(2, 3), (3, 1), (359, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_3407
  · decide +kernel

theorem prime_30831481 : Nat.Prime 30831481 := by
  apply nodeValid_prime [2, 3, 5, 85643] ⟨30831481, 22, [(2, 3), (3, 2), (5, 1), (85643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_85643
  · decide +kernel

theorem prime_31096517 : Nat.Prime 31096517 := by
  apply nodeValid_prime [2, 11, 47, 1367] ⟨31096517, 3, [(2, 2), (11, 2), (47, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_1367
  · decide +kernel

theorem prime_36545653 : Nat.Prime 36545653 := by
  apply nodeValid_prime [2, 3, 11, 13, 31, 229] ⟨36545653, 5, [(2, 2), (3, 2), (11, 1), (13, 1), (31, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_229
  · decide +kernel

theorem prime_41997199 : Nat.Prime 41997199 := by
  apply nodeValid_prime [2, 3, 6999533] ⟨41997199, 23, [(2, 1), (3, 1), (6999533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6999533
  · decide +kernel

theorem prime_45347441 : Nat.Prime 45347441 := by
  apply nodeValid_prime [2, 5, 313, 1811] ⟨45347441, 3, [(2, 4), (5, 1), (313, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_313
    · exact prime_1811
  · decide +kernel

theorem prime_61950521 : Nat.Prime 61950521 := by
  apply nodeValid_prime [2, 5, 1548763] ⟨61950521, 3, [(2, 3), (5, 1), (1548763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1548763
  · decide +kernel

theorem prime_150486841 : Nat.Prime 150486841 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 449] ⟨150486841, 13, [(2, 3), (3, 2), (5, 1), (7, 2), (19, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_449
  · decide +kernel

theorem prime_160187117 : Nat.Prime 160187117 := by
  apply nodeValid_prime [2, 191, 209669] ⟨160187117, 2, [(2, 2), (191, 1), (209669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_209669
  · decide +kernel

theorem prime_239815061 : Nat.Prime 239815061 := by
  apply nodeValid_prime [2, 5, 2711, 4423] ⟨239815061, 2, [(2, 2), (5, 1), (2711, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2711
    · exact prime_4423
  · decide +kernel

theorem prime_320401111 : Nat.Prime 320401111 := by
  apply nodeValid_prime [2, 3, 5, 131, 81527] ⟨320401111, 6, [(2, 1), (3, 1), (5, 1), (131, 1), (81527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_81527
  · decide +kernel

theorem prime_385329179 : Nat.Prime 385329179 := by
  apply nodeValid_prime [2, 13, 3449, 4297] ⟨385329179, 2, [(2, 1), (13, 1), (3449, 1), (4297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3449
    · exact prime_4297
  · decide +kernel

theorem prime_405448343 : Nat.Prime 405448343 := by
  apply nodeValid_prime [2, 13, 223, 69929] ⟨405448343, 5, [(2, 1), (13, 1), (223, 1), (69929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_223
    · exact prime_69929
  · decide +kernel

theorem prime_440053171 : Nat.Prime 440053171 := by
  apply nodeValid_prime [2, 3, 5, 53, 276763] ⟨440053171, 2, [(2, 1), (3, 1), (5, 1), (53, 1), (276763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_276763
  · decide +kernel

theorem prime_484797067 : Nat.Prime 484797067 := by
  apply nodeValid_prime [2, 3, 13, 6215347] ⟨484797067, 2, [(2, 1), (3, 1), (13, 1), (6215347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6215347
  · decide +kernel

theorem prime_495604169 : Nat.Prime 495604169 := by
  apply nodeValid_prime [2, 61950521] ⟨495604169, 3, [(2, 3), (61950521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61950521
  · decide +kernel

theorem prime_561706289 : Nat.Prime 561706289 := by
  apply nodeValid_prime [2, 11, 13, 245501] ⟨561706289, 3, [(2, 4), (11, 1), (13, 1), (245501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_245501
  · decide +kernel

theorem prime_770658359 : Nat.Prime 770658359 := by
  apply nodeValid_prime [2, 385329179] ⟨770658359, 7, [(2, 1), (385329179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_385329179
  · decide +kernel

theorem prime_849884479 : Nat.Prime 849884479 := by
  apply nodeValid_prime [2, 3, 19, 239, 31193] ⟨849884479, 3, [(2, 1), (3, 1), (19, 1), (239, 1), (31193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_239
    · exact prime_31193
  · decide +kernel

theorem prime_956329249 : Nat.Prime 956329249 := by
  apply nodeValid_prime [2, 3, 7, 479, 2971] ⟨956329249, 13, [(2, 5), (3, 1), (7, 1), (479, 1), (2971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_479
    · exact prime_2971
  · decide +kernel

theorem prime_961011383 : Nat.Prime 961011383 := by
  apply nodeValid_prime [2, 41, 11719651] ⟨961011383, 5, [(2, 1), (41, 1), (11719651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_11719651
  · decide +kernel

theorem prime_1033253743 : Nat.Prime 1033253743 := by
  apply nodeValid_prime [2, 3, 9619, 17903] ⟨1033253743, 3, [(2, 1), (3, 1), (9619, 1), (17903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9619
    · exact prime_17903
  · decide +kernel

theorem prime_1383712751 : Nat.Prime 1383712751 := by
  apply nodeValid_prime [2, 5, 7, 790693] ⟨1383712751, 17, [(2, 1), (5, 3), (7, 1), (790693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_790693
  · decide +kernel

theorem prime_3238658947 : Nat.Prime 3238658947 := by
  apply nodeValid_prime [2, 3, 19, 9469763] ⟨3238658947, 5, [(2, 1), (3, 2), (19, 1), (9469763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_9469763
  · decide +kernel

theorem prime_3251909659 : Nat.Prime 3251909659 := by
  apply nodeValid_prime [2, 3, 43, 53, 163, 1459] ⟨3251909659, 10, [(2, 1), (3, 1), (43, 1), (53, 1), (163, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_53
    · exact prime_163
    · exact prime_1459
  · decide +kernel

theorem prime_4872882359 : Nat.Prime 4872882359 := by
  apply nodeValid_prime [2, 83, 29354713] ⟨4872882359, 7, [(2, 1), (83, 1), (29354713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_29354713
  · decide +kernel

theorem prime_5676276803 : Nat.Prime 5676276803 := by
  apply nodeValid_prime [2, 7, 405448343] ⟨5676276803, 2, [(2, 1), (7, 1), (405448343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_405448343
  · decide +kernel

theorem prime_7100345221 : Nat.Prime 7100345221 := by
  apply nodeValid_prime [2, 3, 5, 19, 6228373] ⟨7100345221, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (6228373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_6228373
  · decide +kernel

theorem prime_7709064971 : Nat.Prime 7709064971 := by
  apply nodeValid_prime [2, 5, 17, 45347441] ⟨7709064971, 2, [(2, 1), (5, 1), (17, 1), (45347441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_45347441
  · decide +kernel

theorem prime_9745764719 : Nat.Prime 9745764719 := by
  apply nodeValid_prime [2, 4872882359] ⟨9745764719, 11, [(2, 1), (4872882359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4872882359
  · decide +kernel

theorem prime_13101271793 : Nat.Prime 13101271793 := by
  apply nodeValid_prime [2, 7, 10289, 11369] ⟨13101271793, 3, [(2, 4), (7, 1), (10289, 1), (11369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10289
    · exact prime_11369
  · decide +kernel

theorem prime_18110185361 : Nat.Prime 18110185361 := by
  apply nodeValid_prime [2, 5, 3079, 73523] ⟨18110185361, 3, [(2, 4), (5, 1), (3079, 1), (73523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3079
    · exact prime_73523
  · decide +kernel

theorem prime_23654695837 : Nat.Prime 23654695837 := by
  apply nodeValid_prime [2, 3, 1637, 1204169] ⟨23654695837, 5, [(2, 2), (3, 1), (1637, 1), (1204169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1637
    · exact prime_1204169
  · decide +kernel

theorem prime_24780208451 : Nat.Prime 24780208451 := by
  apply nodeValid_prime [2, 5, 495604169] ⟨24780208451, 2, [(2, 1), (5, 2), (495604169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_495604169
  · decide +kernel

theorem prime_25435774489 : Nat.Prime 25435774489 := by
  apply nodeValid_prime [2, 3, 29, 36545653] ⟨25435774489, 13, [(2, 3), (3, 1), (29, 1), (36545653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_36545653
  · decide +kernel

theorem prime_26611532807 : Nat.Prime 26611532807 := by
  apply nodeValid_prime [2, 1907, 6977329] ⟨26611532807, 5, [(2, 1), (1907, 1), (6977329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1907
    · exact prime_6977329
  · decide +kernel

theorem prime_58115935543 : Nat.Prime 58115935543 := by
  apply nodeValid_prime [2, 3, 7, 1383712751] ⟨58115935543, 5, [(2, 1), (3, 1), (7, 1), (1383712751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1383712751
  · decide +kernel

theorem prime_69810777649 : Nat.Prime 69810777649 := by
  apply nodeValid_prime [2, 3, 484797067] ⟨69810777649, 11, [(2, 4), (3, 2), (484797067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_484797067
  · decide +kernel

theorem prime_70602302807 : Nat.Prime 70602302807 := by
  apply nodeValid_prime [2, 7, 19, 163, 85703] ⟨70602302807, 5, [(2, 1), (7, 1), (19, 2), (163, 1), (85703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_163
    · exact prime_85703
  · decide +kernel

theorem prime_522506367403 : Nat.Prime 522506367403 := by
  apply nodeValid_prime [2, 3, 113, 770658359] ⟨522506367403, 2, [(2, 1), (3, 1), (113, 1), (770658359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_770658359
  · decide +kernel

theorem prime_1043939366273 : Nat.Prime 1043939366273 := by
  apply nodeValid_prime [2, 11, 17, 73, 269, 2221] ⟨1043939366273, 3, [(2, 7), (11, 1), (17, 1), (73, 1), (269, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_73
    · exact prime_269
    · exact prime_2221
  · decide +kernel

theorem prime_2081447528551 : Nat.Prime 2081447528551 := by
  apply nodeValid_prime [2, 3, 5, 13, 2957, 360977] ⟨2081447528551, 3, [(2, 1), (3, 1), (5, 2), (13, 1), (2957, 1), (360977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_2957
    · exact prime_360977
  · decide +kernel

theorem prime_2081447542171 : Nat.Prime 2081447542171 := by
  apply nodeValid_prime [2, 3, 5, 7709064971] ⟨2081447542171, 2, [(2, 1), (3, 3), (5, 1), (7709064971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7709064971
  · decide +kernel

theorem prime_2081447542397 : Nat.Prime 2081447542397 := by
  apply nodeValid_prime [2, 143813, 3618323] ⟨2081447542397, 2, [(2, 2), (143813, 1), (3618323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_143813
    · exact prime_3618323
  · decide +kernel

theorem prime_2083589725991 : Nat.Prime 2083589725991 := by
  apply nodeValid_prime [2, 5, 1231, 7499, 22571] ⟨2083589725991, 13, [(2, 1), (5, 1), (1231, 1), (7499, 1), (22571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1231
    · exact prime_7499
    · exact prime_22571
  · decide +kernel

theorem prime_2083589727641 : Nat.Prime 2083589727641 := by
  apply nodeValid_prime [2, 5, 70627, 737533] ⟨2083589727641, 3, [(2, 3), (5, 1), (70627, 1), (737533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_70627
    · exact prime_737533
  · decide +kernel

theorem prime_2083589772587 : Nat.Prime 2083589772587 := by
  apply nodeValid_prime [2, 7, 41, 47599, 76261] ⟨2083589772587, 2, [(2, 1), (7, 1), (41, 1), (47599, 1), (76261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_47599
    · exact prime_76261
  · decide +kernel

theorem prime_2085733393099 : Nat.Prime 2085733393099 := by
  apply nodeValid_prime [2, 3, 17, 19, 31, 2089, 16619] ⟨2085733393099, 2, [(2, 1), (3, 1), (17, 1), (19, 1), (31, 1), (2089, 1), (16619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_31
    · exact prime_2089
    · exact prime_16619
  · decide +kernel

theorem prime_2085733393223 : Nat.Prime 2085733393223 := by
  apply nodeValid_prime [2, 31, 69011, 487471] ⟨2085733393223, 5, [(2, 1), (31, 1), (69011, 1), (487471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_69011
    · exact prime_487471
  · decide +kernel

theorem prime_2085733508099 : Nat.Prime 2085733508099 := by
  apply nodeValid_prime [2, 41, 25435774489] ⟨2085733508099, 2, [(2, 1), (41, 1), (25435774489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_25435774489
  · decide +kernel

theorem prime_2087878721081 : Nat.Prime 2087878721081 := by
  apply nodeValid_prime [2, 5, 3863, 13512029] ⟨2087878721081, 3, [(2, 3), (5, 1), (3863, 1), (13512029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3863
    · exact prime_13512029
  · decide +kernel

theorem prime_2087878732547 : Nat.Prime 2087878732547 := by
  apply nodeValid_prime [2, 1043939366273] ⟨2087878732547, 2, [(2, 1), (1043939366273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1043939366273
  · decide +kernel

theorem prime_2090025453151 : Nat.Prime 2090025453151 := by
  apply nodeValid_prime [2, 3, 5, 179, 269, 96457] ⟨2090025453151, 29, [(2, 1), (3, 2), (5, 2), (179, 1), (269, 1), (96457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_269
    · exact prime_96457
  · decide +kernel

theorem prime_2090025468551 : Nat.Prime 2090025468551 := by
  apply nodeValid_prime [2, 5, 19, 139, 1193, 13267] ⟨2090025468551, 11, [(2, 1), (5, 2), (19, 1), (139, 1), (1193, 1), (13267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_139
    · exact prime_1193
    · exact prime_13267
  · decide +kernel

theorem prime_2090025469613 : Nat.Prime 2090025469613 := by
  apply nodeValid_prime [2, 522506367403] ⟨2090025469613, 2, [(2, 2), (522506367403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_522506367403
  · decide +kernel

theorem prime_2092173663761 : Nat.Prime 2092173663761 := by
  apply nodeValid_prime [2, 5, 29, 31096517] ⟨2092173663761, 6, [(2, 4), (5, 1), (29, 2), (31096517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_31096517
  · decide +kernel

theorem prime_2092173679549 : Nat.Prime 2092173679549 := by
  apply nodeValid_prime [2, 3, 58115935543] ⟨2092173679549, 2, [(2, 2), (3, 2), (58115935543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58115935543
  · decide +kernel

theorem prime_2092173679763 : Nat.Prime 2092173679763 := by
  apply nodeValid_prime [2, 17, 19, 3238658947] ⟨2092173679763, 2, [(2, 1), (17, 1), (19, 1), (3238658947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_3238658947
  · decide +kernel

theorem prime_2094323329471 : Nat.Prime 2094323329471 := by
  apply nodeValid_prime [2, 3, 5, 69810777649] ⟨2094323329471, 3, [(2, 1), (3, 1), (5, 1), (69810777649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_69810777649
  · decide +kernel

theorem prime_2094323331271 : Nat.Prime 2094323331271 := by
  apply nodeValid_prime [2, 3, 5, 113, 1381, 447353] ⟨2094323331271, 3, [(2, 1), (3, 1), (5, 1), (113, 1), (1381, 1), (447353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_1381
    · exact prime_447353
  · decide +kernel

theorem prime_2094323375801 : Nat.Prime 2094323375801 := by
  apply nodeValid_prime [2, 5, 773, 983, 13781] ⟨2094323375801, 3, [(2, 3), (5, 2), (773, 1), (983, 1), (13781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_773
    · exact prime_983
    · exact prime_13781
  · decide +kernel

theorem prime_2096474569081 : Nat.Prime 2096474569081 := by
  apply nodeValid_prime [2, 3, 5, 29, 37, 691, 23563] ⟨2096474569081, 17, [(2, 3), (3, 1), (5, 1), (29, 1), (37, 1), (691, 1), (23563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_37
    · exact prime_691
    · exact prime_23563
  · decide +kernel

theorem prime_2096474570107 : Nat.Prime 2096474570107 := by
  apply nodeValid_prime [2, 3, 7, 97, 3767, 136607] ⟨2096474570107, 5, [(2, 1), (3, 1), (7, 1), (97, 1), (3767, 1), (136607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_3767
    · exact prime_136607
  · decide +kernel

theorem prime_2096474588413 : Nat.Prime 2096474588413 := by
  apply nodeValid_prime [2, 3, 7309, 23902889] ⟨2096474588413, 6, [(2, 2), (3, 1), (7309, 1), (23902889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7309
    · exact prime_23902889
  · decide +kernel

theorem prime_2098627276073 : Nat.Prime 2098627276073 := by
  apply nodeValid_prime [2, 153499, 1708991] ⟨2098627276073, 3, [(2, 3), (153499, 1), (1708991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_153499
    · exact prime_1708991
  · decide +kernel

theorem prime_2098627277051 : Nat.Prime 2098627277051 := by
  apply nodeValid_prime [2, 5, 131, 320401111] ⟨2098627277051, 2, [(2, 1), (5, 2), (131, 1), (320401111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_320401111
  · decide +kernel

theorem prime_2098627298671 : Nat.Prime 2098627298671 := by
  apply nodeValid_prime [2, 3, 5, 7, 2521, 3964087] ⟨2098627298671, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (2521, 1), (3964087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2521
    · exact prime_3964087
  · decide +kernel

theorem prime_2100781501877 : Nat.Prime 2100781501877 := by
  apply nodeValid_prime [2, 29, 18110185361] ⟨2100781501877, 2, [(2, 2), (29, 1), (18110185361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_18110185361
  · decide +kernel

theorem prime_2100781520861 : Nat.Prime 2100781520861 := by
  apply nodeValid_prime [2, 5, 11, 17, 561706289] ⟨2100781520861, 2, [(2, 2), (5, 1), (11, 1), (17, 1), (561706289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_561706289
  · decide +kernel

theorem prime_2100781521143 : Nat.Prime 2100781521143 := by
  apply nodeValid_prime [2, 227, 1277, 1831, 1979] ⟨2100781521143, 5, [(2, 1), (227, 1), (1277, 1), (1831, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_1277
    · exact prime_1831
    · exact prime_1979
  · decide +kernel

theorem prime_2102937145801 : Nat.Prime 2102937145801 := by
  apply nodeValid_prime [2, 3, 5, 467, 7505129] ⟨2102937145801, 11, [(2, 3), (3, 1), (5, 2), (467, 1), (7505129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
    · exact prime_7505129
  · decide +kernel

theorem prime_2102937145919 : Nat.Prime 2102937145919 := by
  apply nodeValid_prime [2, 7, 17, 55843, 158227] ⟨2102937145919, 7, [(2, 1), (7, 1), (17, 1), (55843, 1), (158227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_55843
    · exact prime_158227
  · decide +kernel

theorem prime_2102937203167 : Nat.Prime 2102937203167 := by
  apply nodeValid_prime [2, 3, 199, 601, 2930539] ⟨2102937203167, 3, [(2, 1), (3, 1), (199, 1), (601, 1), (2930539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_601
    · exact prime_2930539
  · decide +kernel

theorem prime_2105094393979 : Nat.Prime 2105094393979 := by
  apply nodeValid_prime [2, 3, 102001, 3439663] ⟨2105094393979, 3, [(2, 1), (3, 1), (102001, 1), (3439663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102001
    · exact prime_3439663
  · decide +kernel

theorem prime_2105094428747 : Nat.Prime 2105094428747 := by
  apply nodeValid_prime [2, 910219, 1156367] ⟨2105094428747, 2, [(2, 1), (910219, 1), (1156367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_910219
    · exact prime_1156367
  · decide +kernel

theorem prime_2105094429509 : Nat.Prime 2105094429509 := by
  apply nodeValid_prime [2, 7, 367, 2243, 91331] ⟨2105094429509, 2, [(2, 2), (7, 1), (367, 1), (2243, 1), (91331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_367
    · exact prime_2243
    · exact prime_91331
  · decide +kernel

theorem prime_2107253084969 : Nat.Prime 2107253084969 := by
  apply nodeValid_prime [2, 73, 359, 10051003] ⟨2107253084969, 3, [(2, 3), (73, 1), (359, 1), (10051003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_359
    · exact prime_10051003
  · decide +kernel

theorem prime_2107253130511 : Nat.Prime 2107253130511 := by
  apply nodeValid_prime [2, 3, 5, 11, 271, 23563157] ⟨2107253130511, 14, [(2, 1), (3, 1), (5, 1), (11, 1), (271, 1), (23563157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_271
    · exact prime_23563157
  · decide +kernel

theorem prime_2107253131121 : Nat.Prime 2107253131121 := by
  apply nodeValid_prime [2, 5, 53, 4153, 119671] ⟨2107253131121, 3, [(2, 4), (5, 1), (53, 1), (4153, 1), (119671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_4153
    · exact prime_119671
  · decide +kernel

theorem prime_2109413276557 : Nat.Prime 2109413276557 := by
  apply nodeValid_prime [2, 3, 733, 239815061] ⟨2109413276557, 2, [(2, 2), (3, 1), (733, 1), (239815061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_733
    · exact prime_239815061
  · decide +kernel

theorem prime_2109413276879 : Nat.Prime 2109413276879 := by
  apply nodeValid_prime [2, 17, 73, 849884479] ⟨2109413276879, 37, [(2, 1), (17, 1), (73, 1), (849884479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_73
    · exact prime_849884479
  · decide +kernel

theorem prime_2109413276983 : Nat.Prime 2109413276983 := by
  apply nodeValid_prime [2, 3, 11, 19583, 20149] ⟨2109413276983, 6, [(2, 1), (3, 5), (11, 1), (19583, 1), (20149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19583
    · exact prime_20149
  · decide +kernel

theorem prime_2111574970717 : Nat.Prime 2111574970717 := by
  apply nodeValid_prime [2, 3, 31, 5676276803] ⟨2111574970717, 2, [(2, 2), (3, 1), (31, 1), (5676276803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_5676276803
  · decide +kernel

theorem prime_2111574981793 : Nat.Prime 2111574981793 := by
  apply nodeValid_prime [2, 3, 23, 956329249] ⟨2111574981793, 15, [(2, 5), (3, 1), (23, 1), (956329249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_956329249
  · decide +kernel

theorem prime_2111574982609 : Nat.Prime 2111574982609 := by
  apply nodeValid_prime [2, 3, 7, 13, 3203, 7187] ⟨2111574982609, 17, [(2, 4), (3, 2), (7, 2), (13, 1), (3203, 1), (7187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_3203
    · exact prime_7187
  · decide +kernel

theorem prime_2113738168687 : Nat.Prime 2113738168687 := by
  apply nodeValid_prime [2, 3, 2341, 150486841] ⟨2113738168687, 3, [(2, 1), (3, 1), (2341, 1), (150486841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2341
    · exact prime_150486841
  · decide +kernel

theorem prime_2113738223041 : Nat.Prime 2113738223041 := by
  apply nodeValid_prime [2, 3, 5, 19, 523, 73859] ⟨2113738223041, 34, [(2, 6), (3, 2), (5, 1), (19, 1), (523, 1), (73859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_523
    · exact prime_73859
  · decide +kernel

theorem prime_2113738223357 : Nat.Prime 2113738223357 := by
  apply nodeValid_prime [2, 64301, 8218139] ⟨2113738223357, 2, [(2, 2), (64301, 1), (8218139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_64301
    · exact prime_8218139
  · decide +kernel

theorem prime_2115902875859 : Nat.Prime 2115902875859 := by
  apply nodeValid_prime [2, 149, 7100345221] ⟨2115902875859, 2, [(2, 1), (149, 1), (7100345221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_7100345221
  · decide +kernel

theorem prime_2115902878069 : Nat.Prime 2115902878069 := by
  apply nodeValid_prime [2, 3, 7, 19, 43, 30831481] ⟨2115902878069, 10, [(2, 2), (3, 1), (7, 1), (19, 1), (43, 1), (30831481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_43
    · exact prime_30831481
  · decide +kernel

theorem prime_2115902880019 : Nat.Prime 2115902880019 := by
  apply nodeValid_prime [2, 3, 311, 41997199] ⟨2115902880019, 2, [(2, 1), (3, 4), (311, 1), (41997199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_41997199
  · decide +kernel

theorem prime_2118069083239 : Nat.Prime 2118069083239 := by
  apply nodeValid_prime [2, 3, 17, 118891, 174659] ⟨2118069083239, 3, [(2, 1), (3, 1), (17, 1), (118891, 1), (174659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_118891
    · exact prime_174659
  · decide +kernel

theorem prime_2118069084211 : Nat.Prime 2118069084211 := by
  apply nodeValid_prime [2, 3, 5, 70602302807] ⟨2118069084211, 12, [(2, 1), (3, 1), (5, 1), (70602302807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_70602302807
  · decide +kernel

theorem prime_2118069088133 : Nat.Prime 2118069088133 := by
  apply nodeValid_prime [2, 19, 29, 961011383] ⟨2118069088133, 2, [(2, 2), (19, 1), (29, 1), (961011383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_961011383
  · decide +kernel

theorem prime_2120236680613 : Nat.Prime 2120236680613 := by
  apply nodeValid_prime [2, 3, 1103, 160187117] ⟨2120236680613, 5, [(2, 2), (3, 1), (1103, 1), (160187117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1103
    · exact prime_160187117
  · decide +kernel

theorem prime_2120236680637 : Nat.Prime 2120236680637 := by
  apply nodeValid_prime [2, 3, 19, 1033253743] ⟨2120236680637, 2, [(2, 2), (3, 3), (19, 1), (1033253743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1033253743
  · decide +kernel

theorem prime_2120236806913 : Nat.Prime 2120236806913 := by
  apply nodeValid_prime [2, 3, 7, 139, 1171, 2423] ⟨2120236806913, 5, [(2, 8), (3, 1), (7, 1), (139, 1), (1171, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
    · exact prime_1171
    · exact prime_2423
  · decide +kernel

theorem prime_2122406030467 : Nat.Prime 2122406030467 := by
  apply nodeValid_prime [2, 3, 13101271793] ⟨2122406030467, 2, [(2, 1), (3, 4), (13101271793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13101271793
  · decide +kernel

theorem prime_2122406048209 : Nat.Prime 2122406048209 := by
  apply nodeValid_prime [2, 3, 53, 107, 577, 13513] ⟨2122406048209, 7, [(2, 4), (3, 1), (53, 1), (107, 1), (577, 1), (13513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_107
    · exact prime_577
    · exact prime_13513
  · decide +kernel

theorem prime_2122406048773 : Nat.Prime 2122406048773 := by
  apply nodeValid_prime [2, 3, 43, 659, 231169] ⟨2122406048773, 2, [(2, 2), (3, 4), (43, 1), (659, 1), (231169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_659
    · exact prime_231169
  · decide +kernel

theorem prime_2124576708743 : Nat.Prime 2124576708743 := by
  apply nodeValid_prime [2, 109, 9745764719] ⟨2124576708743, 5, [(2, 1), (109, 1), (9745764719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_9745764719
  · decide +kernel

theorem prime_2124576709589 : Nat.Prime 2124576709589 := by
  apply nodeValid_prime [2, 17, 71, 440053171] ⟨2124576709589, 2, [(2, 2), (17, 1), (71, 1), (440053171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_440053171
  · decide +kernel

theorem prime_2124576754771 : Nat.Prime 2124576754771 := by
  apply nodeValid_prime [2, 3, 5, 89, 173, 883, 5209] ⟨2124576754771, 3, [(2, 1), (3, 1), (5, 1), (89, 1), (173, 1), (883, 1), (5209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_173
    · exact prime_883
    · exact prime_5209
  · decide +kernel

theorem prime_2126748916987 : Nat.Prime 2126748916987 := by
  apply nodeValid_prime [2, 3, 109, 3251909659] ⟨2126748916987, 3, [(2, 1), (3, 1), (109, 1), (3251909659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_3251909659
  · decide +kernel

theorem prime_2126748917053 : Nat.Prime 2126748917053 := by
  apply nodeValid_prime [2, 3, 373, 523, 302833] ⟨2126748917053, 5, [(2, 2), (3, 2), (373, 1), (523, 1), (302833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_523
    · exact prime_302833
  · decide +kernel

theorem prime_2126748982223 : Nat.Prime 2126748982223 := by
  apply nodeValid_prime [2, 401, 6823, 388657] ⟨2126748982223, 5, [(2, 1), (401, 1), (6823, 1), (388657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_401
    · exact prime_6823
    · exact prime_388657
  · decide +kernel

theorem prime_2128922624561 : Nat.Prime 2128922624561 := by
  apply nodeValid_prime [2, 5, 26611532807] ⟨2128922624561, 3, [(2, 4), (5, 1), (26611532807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_26611532807
  · decide +kernel

theorem prime_2128922625331 : Nat.Prime 2128922625331 := by
  apply nodeValid_prime [2, 3, 5, 23654695837] ⟨2128922625331, 2, [(2, 1), (3, 2), (5, 1), (23654695837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23654695837
  · decide +kernel

theorem prime_2128922708147 : Nat.Prime 2128922708147 := by
  apply nodeValid_prime [2, 13, 17, 43, 6823, 16417] ⟨2128922708147, 2, [(2, 1), (13, 1), (17, 1), (43, 1), (6823, 1), (16417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_43
    · exact prime_6823
    · exact prime_16417
  · decide +kernel

theorem prime_2131097926787 : Nat.Prime 2131097926787 := by
  apply nodeValid_prime [2, 43, 24780208451] ⟨2131097926787, 2, [(2, 1), (43, 1), (24780208451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_24780208451
  · decide +kernel

theorem prime_2131097927201 : Nat.Prime 2131097927201 := by
  apply nodeValid_prime [2, 5, 11, 17, 19, 823, 911] ⟨2131097927201, 3, [(2, 5), (5, 2), (11, 1), (17, 1), (19, 1), (823, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_823
    · exact prime_911
  · decide +kernel

theorem prime_2131097940611 : Nat.Prime 2131097940611 := by
  apply nodeValid_prime [2, 5, 101, 14503, 145487] ⟨2131097940611, 2, [(2, 1), (5, 1), (101, 1), (14503, 1), (145487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_14503
    · exact prime_145487
  · decide +kernel

theorem prime_2133274680659 : Nat.Prime 2133274680659 := by
  apply nodeValid_prime [2, 11, 137, 1861, 380327] ⟨2133274680659, 2, [(2, 1), (11, 1), (137, 1), (1861, 1), (380327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_137
    · exact prime_1861
    · exact prime_380327
  · decide +kernel

theorem prime_2133274788263 : Nat.Prime 2133274788263 := by
  apply nodeValid_prime [2, 64303, 16587677] ⟨2133274788263, 5, [(2, 1), (64303, 1), (16587677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_64303
    · exact prime_16587677
  · decide +kernel

theorem prime_2133274791517 : Nat.Prime 2133274791517 := by
  apply nodeValid_prime [2, 3, 11, 23, 41, 167, 2503] ⟨2133274791517, 5, [(2, 2), (3, 1), (11, 1), (23, 1), (41, 2), (167, 1), (2503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_41
    · exact prime_167
    · exact prime_2503
  · decide +kernel

end Sude.Lucas.Generated
