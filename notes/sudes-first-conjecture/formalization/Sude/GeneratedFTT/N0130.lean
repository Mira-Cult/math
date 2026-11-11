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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0122

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_20483 : Nat.Prime 20483 := by
  apply nodeValid_prime [2, 7, 11, 19] ⟨20483, 5, [(2, 1), (7, 2), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_23873 : Nat.Prime 23873 := by
  apply nodeValid_prime [2, 373] ⟨23873, 3, [(2, 6), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_373
  · decide +kernel

theorem prime_31517 : Nat.Prime 31517 := by
  apply nodeValid_prime [2, 7879] ⟨31517, 2, [(2, 2), (7879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7879
  · decide +kernel

theorem prime_34781 : Nat.Prime 34781 := by
  apply nodeValid_prime [2, 5, 37, 47] ⟨34781, 2, [(2, 2), (5, 1), (37, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_47
  · decide +kernel

theorem prime_37253 : Nat.Prime 37253 := by
  apply nodeValid_prime [2, 67, 139] ⟨37253, 2, [(2, 2), (67, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_139
  · decide +kernel

theorem prime_38557 : Nat.Prime 38557 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨38557, 2, [(2, 2), (3, 4), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_42157 : Nat.Prime 42157 := by
  apply nodeValid_prime [2, 3, 1171] ⟨42157, 2, [(2, 2), (3, 2), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1171
  · decide +kernel

theorem prime_42703 : Nat.Prime 42703 := by
  apply nodeValid_prime [2, 3, 11, 647] ⟨42703, 5, [(2, 1), (3, 1), (11, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_647
  · decide +kernel

theorem prime_57163 : Nat.Prime 57163 := by
  apply nodeValid_prime [2, 3, 7, 1361] ⟨57163, 2, [(2, 1), (3, 1), (7, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1361
  · decide +kernel

theorem prime_57901 : Nat.Prime 57901 := by
  apply nodeValid_prime [2, 3, 5, 193] ⟨57901, 2, [(2, 2), (3, 1), (5, 2), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_193
  · decide +kernel

theorem prime_60167 : Nat.Prime 60167 := by
  apply nodeValid_prime [2, 67, 449] ⟨60167, 5, [(2, 1), (67, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_449
  · decide +kernel

theorem prime_66377 : Nat.Prime 66377 := by
  apply nodeValid_prime [2, 8297] ⟨66377, 3, [(2, 3), (8297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8297
  · decide +kernel

theorem prime_74507 : Nat.Prime 74507 := by
  apply nodeValid_prime [2, 37253] ⟨74507, 2, [(2, 1), (37253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37253
  · decide +kernel

theorem prime_81031 : Nat.Prime 81031 := by
  apply nodeValid_prime [2, 3, 5, 37, 73] ⟨81031, 6, [(2, 1), (3, 1), (5, 1), (37, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_73
  · decide +kernel

theorem prime_81629 : Nat.Prime 81629 := by
  apply nodeValid_prime [2, 20407] ⟨81629, 2, [(2, 2), (20407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20407
  · decide +kernel

theorem prime_83177 : Nat.Prime 83177 := by
  apply nodeValid_prime [2, 37, 281] ⟨83177, 3, [(2, 3), (37, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_281
  · decide +kernel

theorem prime_86599 : Nat.Prime 86599 := by
  apply nodeValid_prime [2, 3, 17, 283] ⟨86599, 3, [(2, 1), (3, 2), (17, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_283
  · decide +kernel

theorem prime_87119 : Nat.Prime 87119 := by
  apply nodeValid_prime [2, 43, 1013] ⟨87119, 7, [(2, 1), (43, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1013
  · decide +kernel

theorem prime_96581 : Nat.Prime 96581 := by
  apply nodeValid_prime [2, 5, 11, 439] ⟨96581, 2, [(2, 2), (5, 1), (11, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_439
  · decide +kernel

theorem prime_97549 : Nat.Prime 97549 := by
  apply nodeValid_prime [2, 3, 11, 739] ⟨97549, 2, [(2, 2), (3, 1), (11, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_739
  · decide +kernel

theorem prime_107071 : Nat.Prime 107071 := by
  apply nodeValid_prime [2, 3, 5, 43, 83] ⟨107071, 3, [(2, 1), (3, 1), (5, 1), (43, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_83
  · decide +kernel

theorem prime_118057 : Nat.Prime 118057 := by
  apply nodeValid_prime [2, 3, 4919] ⟨118057, 10, [(2, 3), (3, 1), (4919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4919
  · decide +kernel

theorem prime_127733 : Nat.Prime 127733 := by
  apply nodeValid_prime [2, 11, 2903] ⟨127733, 2, [(2, 2), (11, 1), (2903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2903
  · decide +kernel

theorem prime_130337 : Nat.Prime 130337 := by
  apply nodeValid_prime [2, 4073] ⟨130337, 3, [(2, 5), (4073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4073
  · decide +kernel

theorem prime_145091 : Nat.Prime 145091 := by
  apply nodeValid_prime [2, 5, 11, 1319] ⟨145091, 2, [(2, 1), (5, 1), (11, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1319
  · decide +kernel

theorem prime_168629 : Nat.Prime 168629 := by
  apply nodeValid_prime [2, 42157] ⟨168629, 2, [(2, 2), (42157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42157
  · decide +kernel

theorem prime_193013 : Nat.Prime 193013 := by
  apply nodeValid_prime [2, 73, 661] ⟨193013, 2, [(2, 2), (73, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_661
  · decide +kernel

theorem prime_198701 : Nat.Prime 198701 := by
  apply nodeValid_prime [2, 5, 1987] ⟨198701, 2, [(2, 2), (5, 2), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1987
  · decide +kernel

theorem prime_224071 : Nat.Prime 224071 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 97] ⟨224071, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_259667 : Nat.Prime 259667 := by
  apply nodeValid_prime [2, 11, 29, 37] ⟨259667, 2, [(2, 1), (11, 2), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_262049 : Nat.Prime 262049 := by
  apply nodeValid_prime [2, 19, 431] ⟨262049, 3, [(2, 5), (19, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_431
  · decide +kernel

theorem prime_270953 : Nat.Prime 270953 := by
  apply nodeValid_prime [2, 11, 3079] ⟨270953, 3, [(2, 3), (11, 1), (3079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3079
  · decide +kernel

theorem prime_275837 : Nat.Prime 275837 := by
  apply nodeValid_prime [2, 11, 6269] ⟨275837, 2, [(2, 2), (11, 1), (6269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6269
  · decide +kernel

theorem prime_296713 : Nat.Prime 296713 := by
  apply nodeValid_prime [2, 3, 13, 317] ⟨296713, 5, [(2, 3), (3, 2), (13, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_317
  · decide +kernel

theorem prime_304303 : Nat.Prime 304303 := by
  apply nodeValid_prime [2, 3, 41, 1237] ⟨304303, 3, [(2, 1), (3, 1), (41, 1), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1237
  · decide +kernel

theorem prime_336499 : Nat.Prime 336499 := by
  apply nodeValid_prime [2, 3, 17, 3299] ⟨336499, 3, [(2, 1), (3, 1), (17, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3299
  · decide +kernel

theorem prime_387017 : Nat.Prime 387017 := by
  apply nodeValid_prime [2, 7, 6911] ⟨387017, 3, [(2, 3), (7, 1), (6911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6911
  · decide +kernel

theorem prime_445537 : Nat.Prime 445537 := by
  apply nodeValid_prime [2, 3, 7, 13, 17] ⟨445537, 29, [(2, 5), (3, 2), (7, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_533111 : Nat.Prime 533111 := by
  apply nodeValid_prime [2, 5, 89, 599] ⟨533111, 13, [(2, 1), (5, 1), (89, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_599
  · decide +kernel

theorem prime_669673 : Nat.Prime 669673 := by
  apply nodeValid_prime [2, 3, 71, 131] ⟨669673, 5, [(2, 3), (3, 2), (71, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_131
  · decide +kernel

theorem prime_705829 : Nat.Prime 705829 := by
  apply nodeValid_prime [2, 3, 131, 449] ⟨705829, 2, [(2, 2), (3, 1), (131, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_449
  · decide +kernel

theorem prime_723617 : Nat.Prime 723617 := by
  apply nodeValid_prime [2, 22613] ⟨723617, 3, [(2, 5), (22613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22613
  · decide +kernel

theorem prime_727877 : Nat.Prime 727877 := by
  apply nodeValid_prime [2, 283, 643] ⟨727877, 2, [(2, 2), (283, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_643
  · decide +kernel

theorem prime_737537 : Nat.Prime 737537 := by
  apply nodeValid_prime [2, 43, 67] ⟨737537, 3, [(2, 8), (43, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_67
  · decide +kernel

theorem prime_819443 : Nat.Prime 819443 := by
  apply nodeValid_prime [2, 13, 31517] ⟨819443, 2, [(2, 1), (13, 1), (31517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31517
  · decide +kernel

theorem prime_905189 : Nat.Prime 905189 := by
  apply nodeValid_prime [2, 23, 9839] ⟨905189, 2, [(2, 2), (23, 1), (9839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_9839
  · decide +kernel

theorem prime_966781 : Nat.Prime 966781 := by
  apply nodeValid_prime [2, 3, 5, 41, 131] ⟨966781, 6, [(2, 2), (3, 2), (5, 1), (41, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_131
  · decide +kernel

theorem prime_999499 : Nat.Prime 999499 := by
  apply nodeValid_prime [2, 3, 17, 41, 239] ⟨999499, 2, [(2, 1), (3, 1), (17, 1), (41, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_239
  · decide +kernel

theorem prime_1173743 : Nat.Prime 1173743 := by
  apply nodeValid_prime [2, 586871] ⟨1173743, 5, [(2, 1), (586871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_586871
  · decide +kernel

theorem prime_1275319 : Nat.Prime 1275319 := by
  apply nodeValid_prime [2, 3, 11, 19, 113] ⟨1275319, 6, [(2, 1), (3, 3), (11, 1), (19, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_113
  · decide +kernel

theorem prime_1625719 : Nat.Prime 1625719 := by
  apply nodeValid_prime [2, 3, 270953] ⟨1625719, 3, [(2, 1), (3, 1), (270953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_270953
  · decide +kernel

theorem prime_1759103 : Nat.Prime 1759103 := by
  apply nodeValid_prime [2, 83, 10597] ⟨1759103, 5, [(2, 1), (83, 1), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_10597
  · decide +kernel

theorem prime_1878419 : Nat.Prime 1878419 := by
  apply nodeValid_prime [2, 181, 5189] ⟨1878419, 2, [(2, 1), (181, 1), (5189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_5189
  · decide +kernel

theorem prime_1906139 : Nat.Prime 1906139 := by
  apply nodeValid_prime [2, 13, 167, 439] ⟨1906139, 2, [(2, 1), (13, 1), (167, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_167
    · exact prime_439
  · decide +kernel

theorem prime_2219887 : Nat.Prime 2219887 := by
  apply nodeValid_prime [2, 3, 71, 193] ⟨2219887, 5, [(2, 1), (3, 4), (71, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_193
  · decide +kernel

theorem prime_2274959 : Nat.Prime 2274959 := by
  apply nodeValid_prime [2, 7, 43, 3779] ⟨2274959, 7, [(2, 1), (7, 1), (43, 1), (3779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_3779
  · decide +kernel

theorem prime_2342953 : Nat.Prime 2342953 := by
  apply nodeValid_prime [2, 3, 10847] ⟨2342953, 5, [(2, 3), (3, 3), (10847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10847
  · decide +kernel

theorem prime_3283141 : Nat.Prime 3283141 := by
  apply nodeValid_prime [2, 3, 5, 7, 7817] ⟨3283141, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (7817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_7817
  · decide +kernel

theorem prime_3756839 : Nat.Prime 3756839 := by
  apply nodeValid_prime [2, 1878419] ⟨3756839, 7, [(2, 1), (1878419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1878419
  · decide +kernel

theorem prime_4034893 : Nat.Prime 4034893 := by
  apply nodeValid_prime [2, 3, 41, 59, 139] ⟨4034893, 2, [(2, 2), (3, 1), (41, 1), (59, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_59
    · exact prime_139
  · decide +kernel

theorem prime_4342571 : Nat.Prime 4342571 := by
  apply nodeValid_prime [2, 5, 43, 10099] ⟨4342571, 6, [(2, 1), (5, 1), (43, 1), (10099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_10099
  · decide +kernel

theorem prime_5572981 : Nat.Prime 5572981 := by
  apply nodeValid_prime [2, 3, 5, 7, 4423] ⟨5572981, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_4423
  · decide +kernel

theorem prime_6502877 : Nat.Prime 6502877 := by
  apply nodeValid_prime [2, 1625719] ⟨6502877, 2, [(2, 2), (1625719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1625719
  · decide +kernel

theorem prime_6585673 : Nat.Prime 6585673 := by
  apply nodeValid_prime [2, 3, 274403] ⟨6585673, 5, [(2, 3), (3, 1), (274403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_274403
  · decide +kernel

theorem prime_7121731 : Nat.Prime 7121731 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 3083] ⟨7121731, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (3083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_3083
  · decide +kernel

theorem prime_7513679 : Nat.Prime 7513679 := by
  apply nodeValid_prime [2, 3756839] ⟨7513679, 23, [(2, 1), (3756839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3756839
  · decide +kernel

theorem prime_7965151 : Nat.Prime 7965151 := by
  apply nodeValid_prime [2, 3, 5, 53101] ⟨7965151, 3, [(2, 1), (3, 1), (5, 2), (53101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53101
  · decide +kernel

theorem prime_9837799 : Nat.Prime 9837799 := by
  apply nodeValid_prime [2, 3, 17, 43, 2243] ⟨9837799, 15, [(2, 1), (3, 1), (17, 1), (43, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_2243
  · decide +kernel

theorem prime_10641733 : Nat.Prime 10641733 := by
  apply nodeValid_prime [2, 3, 23, 38557] ⟨10641733, 5, [(2, 2), (3, 1), (23, 1), (38557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_38557
  · decide +kernel

theorem prime_10679737 : Nat.Prime 10679737 := by
  apply nodeValid_prime [2, 3, 373, 1193] ⟨10679737, 7, [(2, 3), (3, 1), (373, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_1193
  · decide +kernel

theorem prime_11396317 : Nat.Prime 11396317 := by
  apply nodeValid_prime [2, 3, 23, 157, 263] ⟨11396317, 2, [(2, 2), (3, 1), (23, 1), (157, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_157
    · exact prime_263
  · decide +kernel

theorem prime_11472203 : Nat.Prime 11472203 := by
  apply nodeValid_prime [2, 7, 819443] ⟨11472203, 2, [(2, 1), (7, 1), (819443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_819443
  · decide +kernel

theorem prime_12182003 : Nat.Prime 12182003 := by
  apply nodeValid_prime [2, 7, 19, 41, 1117] ⟨12182003, 5, [(2, 1), (7, 1), (19, 1), (41, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_41
    · exact prime_1117
  · decide +kernel

theorem prime_12699461 : Nat.Prime 12699461 := by
  apply nodeValid_prime [2, 5, 31, 20483] ⟨12699461, 2, [(2, 2), (5, 1), (31, 1), (20483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_20483
  · decide +kernel

theorem prime_14047057 : Nat.Prime 14047057 := by
  apply nodeValid_prime [2, 3, 97549] ⟨14047057, 5, [(2, 4), (3, 2), (97549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97549
  · decide +kernel

theorem prime_15163147 : Nat.Prime 15163147 := by
  apply nodeValid_prime [2, 3, 227, 1237] ⟨15163147, 2, [(2, 1), (3, 3), (227, 1), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_1237
  · decide +kernel

theorem prime_20748997 : Nat.Prime 20748997 := by
  apply nodeValid_prime [2, 3, 47, 12263] ⟨20748997, 7, [(2, 2), (3, 2), (47, 1), (12263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_12263
  · decide +kernel

theorem prime_26313731 : Nat.Prime 26313731 := by
  apply nodeValid_prime [2, 5, 29, 31, 2927] ⟨26313731, 2, [(2, 1), (5, 1), (29, 1), (31, 1), (2927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_31
    · exact prime_2927
  · decide +kernel

theorem prime_34192849 : Nat.Prime 34192849 := by
  apply nodeValid_prime [2, 3, 17, 41903] ⟨34192849, 13, [(2, 4), (3, 1), (17, 1), (41903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41903
  · decide +kernel

theorem prime_39826999 : Nat.Prime 39826999 := by
  apply nodeValid_prime [2, 3, 737537] ⟨39826999, 3, [(2, 1), (3, 3), (737537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_737537
  · decide +kernel

theorem prime_44844377 : Nat.Prime 44844377 := by
  apply nodeValid_prime [2, 1031, 5437] ⟨44844377, 3, [(2, 3), (1031, 1), (5437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1031
    · exact prime_5437
  · decide +kernel

theorem prime_47386453 : Nat.Prime 47386453 := by
  apply nodeValid_prime [2, 3, 53, 74507] ⟨47386453, 14, [(2, 2), (3, 1), (53, 1), (74507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_74507
  · decide +kernel

theorem prime_52023017 : Nat.Prime 52023017 := by
  apply nodeValid_prime [2, 6502877] ⟨52023017, 3, [(2, 3), (6502877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6502877
  · decide +kernel

theorem prime_53921137 : Nat.Prime 53921137 := by
  apply nodeValid_prime [2, 3, 37, 97, 313] ⟨53921137, 5, [(2, 4), (3, 1), (37, 1), (97, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_97
    · exact prime_313
  · decide +kernel

theorem prime_56291297 : Nat.Prime 56291297 := by
  apply nodeValid_prime [2, 1759103] ⟨56291297, 3, [(2, 5), (1759103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1759103
  · decide +kernel

theorem prime_58253057 : Nat.Prime 58253057 := by
  apply nodeValid_prime [2, 313, 727] ⟨58253057, 3, [(2, 8), (313, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_727
  · decide +kernel

theorem prime_89083073 : Nat.Prime 89083073 := by
  apply nodeValid_prime [2, 13, 107071] ⟨89083073, 3, [(2, 6), (13, 1), (107071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_107071
  · decide +kernel

theorem prime_95610247 : Nat.Prime 95610247 := by
  apply nodeValid_prime [2, 3, 1103, 14447] ⟨95610247, 5, [(2, 1), (3, 1), (1103, 1), (14447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1103
    · exact prime_14447
  · decide +kernel

theorem prime_98320361 : Nat.Prime 98320361 := by
  apply nodeValid_prime [2, 5, 43, 57163] ⟨98320361, 6, [(2, 3), (5, 1), (43, 1), (57163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_57163
  · decide +kernel

theorem prime_114080159 : Nat.Prime 114080159 := by
  apply nodeValid_prime [2, 59, 966781] ⟨114080159, 7, [(2, 1), (59, 1), (966781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_966781
  · decide +kernel

theorem prime_137666437 : Nat.Prime 137666437 := by
  apply nodeValid_prime [2, 3, 11472203] ⟨137666437, 2, [(2, 2), (3, 1), (11472203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11472203
  · decide +kernel

theorem prime_183821171 : Nat.Prime 183821171 := by
  apply nodeValid_prime [2, 5, 13, 17, 83177] ⟨183821171, 2, [(2, 1), (5, 1), (13, 1), (17, 1), (83177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_83177
  · decide +kernel

theorem prime_215684549 : Nat.Prime 215684549 := by
  apply nodeValid_prime [2, 53921137] ⟨215684549, 2, [(2, 2), (53921137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53921137
  · decide +kernel

theorem prime_279373607 : Nat.Prime 279373607 := by
  apply nodeValid_prime [2, 19, 37, 198701] ⟨279373607, 5, [(2, 1), (19, 1), (37, 1), (198701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_198701
  · decide +kernel

theorem prime_414973903 : Nat.Prime 414973903 := by
  apply nodeValid_prime [2, 3, 7, 73, 135347] ⟨414973903, 6, [(2, 1), (3, 1), (7, 1), (73, 1), (135347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_135347
  · decide +kernel

theorem prime_576705799 : Nat.Prime 576705799 := by
  apply nodeValid_prime [2, 3, 10679737] ⟨576705799, 3, [(2, 1), (3, 3), (10679737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10679737
  · decide +kernel

theorem prime_1239760409 : Nat.Prime 1239760409 := by
  apply nodeValid_prime [2, 919, 168629] ⟨1239760409, 3, [(2, 3), (919, 1), (168629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_919
    · exact prime_168629
  · decide +kernel

theorem prime_1473568937 : Nat.Prime 1473568937 := by
  apply nodeValid_prime [2, 7, 26313731] ⟨1473568937, 3, [(2, 3), (7, 1), (26313731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_26313731
  · decide +kernel

theorem prime_1494886651 : Nat.Prime 1494886651 := by
  apply nodeValid_prime [2, 3, 5, 31, 41, 7841] ⟨1494886651, 2, [(2, 1), (3, 1), (5, 2), (31, 1), (41, 1), (7841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_41
    · exact prime_7841
  · decide +kernel

theorem prime_5510436229 : Nat.Prime 5510436229 := by
  apply nodeValid_prime [2, 3, 11, 47, 107, 2767] ⟨5510436229, 2, [(2, 2), (3, 2), (11, 1), (47, 1), (107, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_107
    · exact prime_2767
  · decide +kernel

theorem prime_7774477889 : Nat.Prime 7774477889 := by
  apply nodeValid_prime [2, 37, 3283141] ⟨7774477889, 3, [(2, 6), (37, 1), (3283141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_3283141
  · decide +kernel

theorem prime_10352858353 : Nat.Prime 10352858353 := by
  apply nodeValid_prime [2, 3, 215684549] ⟨10352858353, 11, [(2, 4), (3, 1), (215684549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_215684549
  · decide +kernel

theorem prime_11363106421 : Nat.Prime 11363106421 := by
  apply nodeValid_prime [2, 3, 5, 31, 433, 4703] ⟨11363106421, 2, [(2, 2), (3, 2), (5, 1), (31, 1), (433, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_433
    · exact prime_4703
  · decide +kernel

theorem prime_11919467579 : Nat.Prime 11919467579 := by
  apply nodeValid_prime [2, 89, 199, 336499] ⟨11919467579, 2, [(2, 1), (89, 1), (199, 1), (336499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_199
    · exact prime_336499
  · decide +kernel

theorem prime_13084272671 : Nat.Prime 13084272671 := by
  apply nodeValid_prime [2, 5, 7, 19, 9837799] ⟨13084272671, 7, [(2, 1), (5, 1), (7, 1), (19, 1), (9837799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_9837799
  · decide +kernel

theorem prime_13132905959 : Nat.Prime 13132905959 := by
  apply nodeValid_prime [2, 313, 3793, 5531] ⟨13132905959, 23, [(2, 1), (313, 1), (3793, 1), (5531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_3793
    · exact prime_5531
  · decide +kernel

theorem prime_16722835631 : Nat.Prime 16722835631 := by
  apply nodeValid_prime [2, 5, 23, 101, 139, 5179] ⟨16722835631, 17, [(2, 1), (5, 1), (23, 1), (101, 1), (139, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_101
    · exact prime_139
    · exact prime_5179
  · decide +kernel

theorem prime_22418540699 : Nat.Prime 22418540699 := by
  apply nodeValid_prime [2, 15881, 705829] ⟨22418540699, 2, [(2, 1), (15881, 1), (705829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15881
    · exact prime_705829
  · decide +kernel

theorem prime_27340128293 : Nat.Prime 27340128293 := by
  apply nodeValid_prime [2, 3079, 2219887] ⟨27340128293, 2, [(2, 2), (3079, 1), (2219887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3079
    · exact prime_2219887
  · decide +kernel

theorem prime_27575370379 : Nat.Prime 27575370379 := by
  apply nodeValid_prime [2, 3, 571, 677, 1321] ⟨27575370379, 2, [(2, 1), (3, 3), (571, 1), (677, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
    · exact prime_677
    · exact prime_1321
  · decide +kernel

theorem prime_29048173211 : Nat.Prime 29048173211 := by
  apply nodeValid_prime [2, 5, 7, 414973903] ⟨29048173211, 6, [(2, 1), (5, 1), (7, 1), (414973903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_414973903
  · decide +kernel

theorem prime_32519202713 : Nat.Prime 32519202713 := by
  apply nodeValid_prime [2, 541, 7513679] ⟨32519202713, 3, [(2, 3), (541, 1), (7513679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_541
    · exact prime_7513679
  · decide +kernel

theorem prime_35644660049 : Nat.Prime 35644660049 := by
  apply nodeValid_prime [2, 107, 163, 127733] ⟨35644660049, 3, [(2, 4), (107, 1), (163, 1), (127733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_163
    · exact prime_127733
  · decide +kernel

theorem prime_49902524377 : Nat.Prime 49902524377 := by
  apply nodeValid_prime [2, 3, 71, 5347, 5477] ⟨49902524377, 7, [(2, 3), (3, 1), (71, 1), (5347, 1), (5477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_5347
    · exact prime_5477
  · decide +kernel

theorem prime_64001390051 : Nat.Prime 64001390051 := by
  apply nodeValid_prime [2, 5, 13, 17, 445537] ⟨64001390051, 2, [(2, 1), (5, 2), (13, 2), (17, 1), (445537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_445537
  · decide +kernel

theorem prime_72548387641 : Nat.Prime 72548387641 := by
  apply nodeValid_prime [2, 3, 5, 569, 118057] ⟨72548387641, 13, [(2, 3), (3, 3), (5, 1), (569, 1), (118057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_569
    · exact prime_118057
  · decide +kernel

theorem prime_140503077313 : Nat.Prime 140503077313 := by
  apply nodeValid_prime [2, 3, 13, 56291297] ⟨140503077313, 10, [(2, 6), (3, 1), (13, 1), (56291297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_56291297
  · decide +kernel

theorem prime_196126609429 : Nat.Prime 196126609429 := by
  apply nodeValid_prime [2, 3, 29, 109, 487, 3539] ⟨196126609429, 2, [(2, 2), (3, 2), (29, 1), (109, 1), (487, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_109
    · exact prime_487
    · exact prime_3539
  · decide +kernel

theorem prime_198153595231 : Nat.Prime 198153595231 := by
  apply nodeValid_prime [2, 3, 5, 1637, 4034893] ⟨198153595231, 3, [(2, 1), (3, 1), (5, 1), (1637, 1), (4034893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1637
    · exact prime_4034893
  · decide +kernel

theorem prime_198298920499 : Nat.Prime 198298920499 := by
  apply nodeValid_prime [2, 3, 7, 53, 89083073] ⟨198298920499, 2, [(2, 1), (3, 1), (7, 1), (53, 1), (89083073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_89083073
  · decide +kernel

theorem prime_199610097509 : Nat.Prime 199610097509 := by
  apply nodeValid_prime [2, 49902524377] ⟨199610097509, 2, [(2, 2), (49902524377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49902524377
  · decide +kernel

theorem prime_490316523383 : Nat.Prime 490316523383 := by
  apply nodeValid_prime [2, 7, 307, 114080159] ⟨490316523383, 5, [(2, 1), (7, 1), (307, 1), (114080159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_307
    · exact prime_114080159
  · decide +kernel

theorem prime_492845844461 : Nat.Prime 492845844461 := by
  apply nodeValid_prime [2, 5, 179, 137666437] ⟨492845844461, 2, [(2, 2), (5, 1), (179, 1), (137666437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_137666437
  · decide +kernel

theorem prime_495383996729 : Nat.Prime 495383996729 := by
  apply nodeValid_prime [2, 1063, 58253057] ⟨495383996729, 3, [(2, 3), (1063, 1), (58253057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1063
    · exact prime_58253057
  · decide +kernel

theorem prime_1476366845441 : Nat.Prime 1476366845441 := by
  apply nodeValid_prime [2, 5, 576705799] ⟨1476366845441, 3, [(2, 9), (5, 1), (576705799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_576705799
  · decide +kernel

theorem prime_2946229735181 : Nat.Prime 2946229735181 := by
  apply nodeValid_prime [2, 5, 10487, 14047057] ⟨2946229735181, 2, [(2, 2), (5, 1), (10487, 1), (14047057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10487
    · exact prime_14047057
  · decide +kernel

theorem prime_2952733690883 : Nat.Prime 2952733690883 := by
  apply nodeValid_prime [2, 1476366845441] ⟨2952733690883, 2, [(2, 1), (1476366845441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1476366845441
  · decide +kernel

theorem prime_2957075021753 : Nat.Prime 2957075021753 := by
  apply nodeValid_prime [2, 9281, 39826999] ⟨2957075021753, 3, [(2, 3), (9281, 1), (39826999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9281
    · exact prime_39826999
  · decide +kernel

theorem prime_2957075021909 : Nat.Prime 2957075021909 := by
  apply nodeValid_prime [2, 7, 17, 43, 271, 533111] ⟨2957075021909, 2, [(2, 2), (7, 1), (17, 1), (43, 1), (271, 1), (533111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_271
    · exact prime_533111
  · decide +kernel

theorem prime_5883798280597 : Nat.Prime 5883798280597 := by
  apply nodeValid_prime [2, 3, 490316523383] ⟨5883798280597, 5, [(2, 2), (3, 1), (490316523383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_490316523383
  · decide +kernel

theorem prime_5883798282871 : Nat.Prime 5883798282871 := by
  apply nodeValid_prime [2, 3, 5, 196126609429] ⟨5883798282871, 3, [(2, 1), (3, 1), (5, 1), (196126609429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_196126609429
  · decide +kernel

theorem prime_5883798314353 : Nat.Prime 5883798314353 := by
  apply nodeValid_prime [2, 3, 7, 2659, 6585673] ⟨5883798314353, 5, [(2, 4), (3, 1), (7, 1), (2659, 1), (6585673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2659
    · exact prime_6585673
  · decide +kernel

theorem prime_5888127814027 : Nat.Prime 5888127814027 := by
  apply nodeValid_prime [2, 3, 761, 21433, 60167] ⟨5888127814027, 2, [(2, 1), (3, 1), (761, 1), (21433, 1), (60167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_761
    · exact prime_21433
    · exact prime_60167
  · decide +kernel

theorem prime_5888127884693 : Nat.Prime 5888127884693 := by
  apply nodeValid_prime [2, 23, 64001390051] ⟨5888127884693, 2, [(2, 2), (23, 1), (64001390051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_64001390051
  · decide +kernel

theorem prime_5888127885377 : Nat.Prime 5888127885377 := by
  apply nodeValid_prime [2, 11, 86599, 96581] ⟨5888127885377, 3, [(2, 6), (11, 1), (86599, 1), (96581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_86599
    · exact prime_96581
  · decide +kernel

theorem prime_5892459470363 : Nat.Prime 5892459470363 := by
  apply nodeValid_prime [2, 2946229735181] ⟨5892459470363, 2, [(2, 1), (2946229735181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2946229735181
  · decide +kernel

theorem prime_5892459521441 : Nat.Prime 5892459521441 := by
  apply nodeValid_prime [2, 5, 29, 23003, 55207] ⟨5892459521441, 6, [(2, 5), (5, 1), (29, 1), (23003, 1), (55207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_23003
    · exact prime_55207
  · decide +kernel

theorem prime_5892459522611 : Nat.Prime 5892459522611 := by
  apply nodeValid_prime [2, 5, 6163, 95610247] ⟨5892459522611, 2, [(2, 1), (5, 1), (6163, 1), (95610247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6163
    · exact prime_95610247
  · decide +kernel

theorem prime_5896793268001 : Nat.Prime 5896793268001 := by
  apply nodeValid_prime [2, 3, 5, 23, 7121731] ⟨5896793268001, 21, [(2, 5), (3, 2), (5, 3), (23, 1), (7121731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_7121731
  · decide +kernel

theorem prime_5896793269387 : Nat.Prime 5896793269387 := by
  apply nodeValid_prime [2, 3, 19, 193, 331, 29989] ⟨5896793269387, 2, [(2, 1), (3, 4), (19, 1), (193, 1), (331, 1), (29989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_193
    · exact prime_331
    · exact prime_29989
  · decide +kernel

theorem prime_5896793280047 : Nat.Prime 5896793280047 := by
  apply nodeValid_prime [2, 31, 81031, 1173743] ⟨5896793280047, 5, [(2, 1), (31, 1), (81031, 1), (1173743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_81031
    · exact prime_1173743
  · decide +kernel

theorem prime_5901129247147 : Nat.Prime 5901129247147 := by
  apply nodeValid_prime [2, 3, 7, 140503077313] ⟨5901129247147, 2, [(2, 1), (3, 1), (7, 1), (140503077313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_140503077313
  · decide +kernel

theorem prime_5901129261107 : Nat.Prime 5901129261107 := by
  apply nodeValid_prime [2, 107, 27575370379] ⟨5901129261107, 2, [(2, 1), (107, 1), (27575370379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_27575370379
  · decide +kernel

theorem prime_5901129261211 : Nat.Prime 5901129261211 := by
  apply nodeValid_prime [2, 3, 5, 19, 10352858353] ⟨5901129261211, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (10352858353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_10352858353
  · decide +kernel

theorem prime_5905467381767 : Nat.Prime 5905467381767 := by
  apply nodeValid_prime [2, 2952733690883] ⟨5905467381767, 5, [(2, 1), (2952733690883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2952733690883
  · decide +kernel

theorem prime_5905467711289 : Nat.Prime 5905467711289 := by
  apply nodeValid_prime [2, 3, 27340128293] ⟨5905467711289, 14, [(2, 3), (3, 3), (27340128293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27340128293
  · decide +kernel

theorem prime_5905467712201 : Nat.Prime 5905467712201 := by
  apply nodeValid_prime [2, 3, 5, 7, 83, 89, 131, 1453] ⟨5905467712201, 11, [(2, 3), (3, 1), (5, 2), (7, 1), (83, 1), (89, 1), (131, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_83
    · exact prime_89
    · exact prime_131
    · exact prime_1453
  · decide +kernel

theorem prime_5909807681551 : Nat.Prime 5909807681551 := by
  apply nodeValid_prime [2, 3, 5, 13132905959] ⟨5909807681551, 6, [(2, 1), (3, 2), (5, 2), (13132905959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13132905959
  · decide +kernel

theorem prime_5909807702231 : Nat.Prime 5909807702231 := by
  apply nodeValid_prime [2, 5, 17, 34781, 999499] ⟨5909807702231, 11, [(2, 1), (5, 1), (17, 1), (34781, 1), (999499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_34781
    · exact prime_999499
  · decide +kernel

theorem prime_5909807702401 : Nat.Prime 5909807702401 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 304303] ⟨5909807702401, 23, [(2, 7), (3, 1), (5, 2), (7, 1), (17, 2), (304303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_304303
  · decide +kernel

theorem prime_5914150043507 : Nat.Prime 5914150043507 := by
  apply nodeValid_prime [2, 2957075021753] ⟨5914150043507, 2, [(2, 1), (2957075021753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2957075021753
  · decide +kernel

theorem prime_5914150043819 : Nat.Prime 5914150043819 := by
  apply nodeValid_prime [2, 2957075021909] ⟨5914150043819, 2, [(2, 1), (2957075021909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2957075021909
  · decide +kernel

theorem prime_5914150133533 : Nat.Prime 5914150133533 := by
  apply nodeValid_prime [2, 3, 492845844461] ⟨5914150133533, 2, [(2, 2), (3, 1), (492845844461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_492845844461
  · decide +kernel

theorem prime_5918494744537 : Nat.Prime 5918494744537 := by
  apply nodeValid_prime [2, 3, 11, 22418540699] ⟨5918494744537, 5, [(2, 3), (3, 1), (11, 1), (22418540699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_22418540699
  · decide +kernel

theorem prime_5918494892879 : Nat.Prime 5918494892879 := by
  apply nodeValid_prime [2, 259667, 11396317] ⟨5918494892879, 7, [(2, 1), (259667, 1), (11396317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_259667
    · exact prime_11396317
  · decide +kernel

theorem prime_5918494893767 : Nat.Prime 5918494893767 := by
  apply nodeValid_prime [2, 7, 13, 32519202713] ⟨5918494893767, 5, [(2, 1), (7, 1), (13, 1), (32519202713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_32519202713
  · decide +kernel

theorem prime_5922841516561 : Nat.Prime 5922841516561 := by
  apply nodeValid_prime [2, 3, 5, 31, 4583, 57901] ⟨5922841516561, 11, [(2, 4), (3, 2), (5, 1), (31, 1), (4583, 1), (57901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_4583
    · exact prime_57901
  · decide +kernel

theorem prime_5922841601077 : Nat.Prime 5922841601077 := by
  apply nodeValid_prime [2, 3, 387017, 1275319] ⟨5922841601077, 2, [(2, 2), (3, 1), (387017, 1), (1275319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_387017
    · exact prime_1275319
  · decide +kernel

theorem prime_5922841601219 : Nat.Prime 5922841601219 := by
  apply nodeValid_prime [2, 641, 829, 5572981] ⟨5922841601219, 2, [(2, 1), (641, 1), (829, 1), (5572981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_829
    · exact prime_5572981
  · decide +kernel

theorem prime_5927190418879 : Nat.Prime 5927190418879 := by
  apply nodeValid_prime [2, 3, 17, 1117, 52023017] ⟨5927190418879, 3, [(2, 1), (3, 1), (17, 1), (1117, 1), (52023017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1117
    · exact prime_52023017
  · decide +kernel

theorem prime_5927190421067 : Nat.Prime 5927190421067 := by
  apply nodeValid_prime [2, 41, 262049, 275837] ⟨5927190421067, 2, [(2, 1), (41, 1), (262049, 1), (275837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_262049
    · exact prime_275837
  · decide +kernel

theorem prime_5927190446113 : Nat.Prime 5927190446113 := by
  apply nodeValid_prime [2, 3, 13, 17, 279373607] ⟨5927190446113, 7, [(2, 5), (3, 1), (13, 1), (17, 1), (279373607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_279373607
  · decide +kernel

theorem prime_5931541545829 : Nat.Prime 5931541545829 := by
  apply nodeValid_prime [2, 3, 2689, 183821171] ⟨5931541545829, 2, [(2, 2), (3, 1), (2689, 1), (183821171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2689
    · exact prime_183821171
  · decide +kernel

theorem prime_5931541549963 : Nat.Prime 5931541549963 := by
  apply nodeValid_prime [2, 3, 7, 20693, 2274959] ⟨5931541549963, 5, [(2, 1), (3, 2), (7, 1), (20693, 1), (2274959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_20693
    · exact prime_2274959
  · decide +kernel

theorem prime_5931541551763 : Nat.Prime 5931541551763 := by
  apply nodeValid_prime [2, 3, 29, 11363106421] ⟨5931541551763, 2, [(2, 1), (3, 2), (29, 1), (11363106421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_11363106421
  · decide +kernel

theorem prime_5935894817003 : Nat.Prime 5935894817003 := by
  apply nodeValid_prime [2, 151, 1847, 10641733] ⟨5935894817003, 2, [(2, 1), (151, 1), (1847, 1), (10641733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_1847
    · exact prime_10641733
  · decide +kernel

theorem prime_5935894854343 : Nat.Prime 5935894854343 := by
  apply nodeValid_prime [2, 3, 83, 11919467579] ⟨5935894854343, 5, [(2, 1), (3, 1), (83, 1), (11919467579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_11919467579
  · decide +kernel

theorem prime_5935894855031 : Nat.Prime 5935894855031 := by
  apply nodeValid_prime [2, 5, 7, 17, 2129, 2342953] ⟨5935894855031, 7, [(2, 1), (5, 1), (7, 1), (17, 1), (2129, 1), (2342953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_2129
    · exact prime_2342953
  · decide +kernel

theorem prime_5940250254863 : Nat.Prime 5940250254863 := by
  apply nodeValid_prime [2, 7, 11, 5510436229] ⟨5940250254863, 7, [(2, 1), (7, 2), (11, 1), (5510436229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_5510436229
  · decide +kernel

theorem prime_5940250311539 : Nat.Prime 5940250311539 := by
  apply nodeValid_prime [2, 17, 193013, 905189] ⟨5940250311539, 2, [(2, 1), (17, 1), (193013, 1), (905189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_193013
    · exact prime_905189
  · decide +kernel

theorem prime_5940250312781 : Nat.Prime 5940250312781 := by
  apply nodeValid_prime [2, 5, 7, 761, 7965151] ⟨5940250312781, 2, [(2, 2), (5, 1), (7, 2), (761, 1), (7965151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_761
    · exact prime_7965151
  · decide +kernel

theorem prime_5944607856931 : Nat.Prime 5944607856931 := by
  apply nodeValid_prime [2, 3, 5, 198153595231] ⟨5944607856931, 3, [(2, 1), (3, 1), (5, 1), (198153595231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_198153595231
  · decide +kernel

theorem prime_5944607960251 : Nat.Prime 5944607960251 := by
  apply nodeValid_prime [2, 3, 5, 43, 2777, 66377] ⟨5944607960251, 2, [(2, 1), (3, 1), (5, 3), (43, 1), (2777, 1), (66377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_2777
    · exact prime_66377
  · decide +kernel

theorem prime_5944607960749 : Nat.Prime 5944607960749 := by
  apply nodeValid_prime [2, 3, 495383996729] ⟨5944607960749, 7, [(2, 2), (3, 1), (495383996729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_495383996729
  · decide +kernel

theorem prime_5948967614971 : Nat.Prime 5948967614971 := by
  apply nodeValid_prime [2, 3, 5, 198298920499] ⟨5948967614971, 10, [(2, 1), (3, 1), (5, 1), (198298920499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_198298920499
  · decide +kernel

theorem prime_5948967786563 : Nat.Prime 5948967786563 := by
  apply nodeValid_prime [2, 41, 72548387641] ⟨5948967786563, 2, [(2, 1), (41, 1), (72548387641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_72548387641
  · decide +kernel

theorem prime_5948967788513 : Nat.Prime 5948967788513 := by
  apply nodeValid_prime [2, 7, 79, 331, 145091] ⟨5948967788513, 3, [(2, 5), (7, 2), (79, 1), (331, 1), (145091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_331
    · exact prime_145091
  · decide +kernel

theorem prime_5953329484019 : Nat.Prime 5953329484019 := by
  apply nodeValid_prime [2, 7, 1239760409] ⟨5953329484019, 2, [(2, 1), (7, 4), (1239760409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1239760409
  · decide +kernel

theorem prime_5953329484637 : Nat.Prime 5953329484637 := by
  apply nodeValid_prime [2, 89, 16722835631] ⟨5953329484637, 2, [(2, 2), (89, 1), (16722835631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_16722835631
  · decide +kernel

theorem prime_5953329524347 : Nat.Prime 5953329524347 := by
  apply nodeValid_prime [2, 3, 23, 43, 79, 12699461] ⟨5953329524347, 3, [(2, 1), (3, 1), (23, 1), (43, 1), (79, 1), (12699461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_43
    · exact prime_79
    · exact prime_12699461
  · decide +kernel

theorem prime_5957693615039 : Nat.Prime 5957693615039 := by
  apply nodeValid_prime [2, 11, 59, 6343, 723617] ⟨5957693615039, 11, [(2, 1), (11, 1), (59, 1), (6343, 1), (723617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_6343
    · exact prime_723617
  · decide +kernel

theorem prime_5957693624063 : Nat.Prime 5957693624063 := by
  apply nodeValid_prime [2, 87119, 34192849] ⟨5957693624063, 5, [(2, 1), (87119, 1), (34192849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_87119
    · exact prime_34192849
  · decide +kernel

theorem prime_5957693625557 : Nat.Prime 5957693625557 := by
  apply nodeValid_prime [2, 109, 18773, 727877] ⟨5957693625557, 2, [(2, 2), (109, 1), (18773, 1), (727877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_18773
    · exact prime_727877
  · decide +kernel

theorem prime_5962059877967 : Nat.Prime 5962059877967 := by
  apply nodeValid_prime [2, 29, 153499, 669673] ⟨5962059877967, 5, [(2, 1), (29, 1), (153499, 1), (669673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_153499
    · exact prime_669673
  · decide +kernel

theorem prime_5962059919103 : Nat.Prime 5962059919103 := by
  apply nodeValid_prime [2, 7, 17, 1473568937] ⟨5962059919103, 7, [(2, 1), (7, 1), (17, 2), (1473568937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1473568937
  · decide +kernel

theorem prime_5962059922151 : Nat.Prime 5962059922151 := by
  apply nodeValid_prime [2, 5, 2659, 44844377] ⟨5962059922151, 7, [(2, 1), (5, 2), (2659, 1), (44844377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2659
    · exact prime_44844377
  · decide +kernel

theorem prime_5966428297231 : Nat.Prime 5966428297231 := by
  apply nodeValid_prime [2, 3, 5, 1399, 47386453] ⟨5966428297231, 3, [(2, 1), (3, 2), (5, 1), (1399, 1), (47386453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1399
    · exact prime_47386453
  · decide +kernel

theorem prime_5966428337323 : Nat.Prime 5966428337323 := by
  apply nodeValid_prime [2, 3, 81629, 12182003] ⟨5966428337323, 2, [(2, 1), (3, 1), (81629, 1), (12182003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_81629
    · exact prime_12182003
  · decide +kernel

theorem prime_5966428337977 : Nat.Prime 5966428337977 := by
  apply nodeValid_prime [2, 3, 19, 13084272671] ⟨5966428337977, 10, [(2, 3), (3, 1), (19, 1), (13084272671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_13084272671
  · decide +kernel

theorem prime_5970798882809 : Nat.Prime 5970798882809 := by
  apply nodeValid_prime [2, 7591, 98320361] ⟨5970798882809, 3, [(2, 3), (7591, 1), (98320361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7591
    · exact prime_98320361
  · decide +kernel

theorem prime_5970799018753 : Nat.Prime 5970799018753 := by
  apply nodeValid_prime [2, 3, 7774477889] ⟨5970799018753, 5, [(2, 8), (3, 1), (7774477889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7774477889
  · decide +kernel

theorem prime_5970799019099 : Nat.Prime 5970799019099 := by
  apply nodeValid_prime [2, 53, 229, 829, 296713] ⟨5970799019099, 2, [(2, 1), (53, 1), (229, 1), (829, 1), (296713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_229
    · exact prime_829
    · exact prime_296713
  · decide +kernel

theorem prime_5975171642129 : Nat.Prime 5975171642129 := by
  apply nodeValid_prime [2, 13, 631, 1907, 23873] ⟨5975171642129, 3, [(2, 4), (13, 1), (631, 1), (1907, 1), (23873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_631
    · exact prime_1907
    · exact prime_23873
  · decide +kernel

theorem prime_5975171661761 : Nat.Prime 5975171661761 := by
  apply nodeValid_prime [2, 5, 7, 19, 31, 109, 41549] ⟨5975171661761, 3, [(2, 6), (5, 1), (7, 1), (19, 1), (31, 1), (109, 1), (41549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_31
    · exact prime_109
    · exact prime_41549
  · decide +kernel

theorem prime_5975171662079 : Nat.Prime 5975171662079 := by
  apply nodeValid_prime [2, 137, 1051, 20748997] ⟨5975171662079, 7, [(2, 1), (137, 1), (1051, 1), (20748997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_1051
    · exact prime_20748997
  · decide +kernel

theorem prime_5979546564161 : Nat.Prime 5979546564161 := by
  apply nodeValid_prime [2, 5, 13, 331, 4342571] ⟨5979546564161, 6, [(2, 6), (5, 1), (13, 1), (331, 1), (4342571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_331
    · exact prime_4342571
  · decide +kernel

theorem prime_5979546604001 : Nat.Prime 5979546604001 := by
  apply nodeValid_prime [2, 5, 1494886651] ⟨5979546604001, 3, [(2, 5), (5, 3), (1494886651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1494886651
  · decide +kernel

theorem prime_5979546606167 : Nat.Prime 5979546606167 := by
  apply nodeValid_prime [2, 7, 224071, 1906139] ⟨5979546606167, 5, [(2, 1), (7, 1), (224071, 1), (1906139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_224071
    · exact prime_1906139
  · decide +kernel

theorem prime_5983923642943 : Nat.Prime 5983923642943 := by
  apply nodeValid_prime [2, 3, 7, 79, 101, 137, 130337] ⟨5983923642943, 5, [(2, 1), (3, 1), (7, 1), (79, 1), (101, 1), (137, 1), (130337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_101
    · exact prime_137
    · exact prime_130337
  · decide +kernel

theorem prime_5983923679493 : Nat.Prime 5983923679493 := by
  apply nodeValid_prime [2, 11, 8969, 15163147] ⟨5983923679493, 2, [(2, 2), (11, 1), (8969, 1), (15163147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8969
    · exact prime_15163147
  · decide +kernel

theorem prime_5983923681467 : Nat.Prime 5983923681467 := by
  apply nodeValid_prime [2, 103, 29048173211] ⟨5983923681467, 2, [(2, 1), (103, 1), (29048173211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_29048173211
  · decide +kernel

theorem prime_5988302888233 : Nat.Prime 5988302888233 := by
  apply nodeValid_prime [2, 3, 7, 35644660049] ⟨5988302888233, 5, [(2, 3), (3, 1), (7, 1), (35644660049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_35644660049
  · decide +kernel

theorem prime_5988302925271 : Nat.Prime 5988302925271 := by
  apply nodeValid_prime [2, 3, 5, 199610097509] ⟨5988302925271, 3, [(2, 1), (3, 1), (5, 1), (199610097509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199610097509
  · decide +kernel

theorem prime_5988302926103 : Nat.Prime 5988302926103 := by
  apply nodeValid_prime [2, 7, 367, 557, 42703] ⟨5988302926103, 10, [(2, 1), (7, 3), (367, 1), (557, 1), (42703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_367
    · exact prime_557
    · exact prime_42703
  · decide +kernel

end Sude.Lucas.Generated
