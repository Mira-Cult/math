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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0089

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6967 : Nat.Prime 6967 := by
  apply nodeValid_prime [2, 3, 43] ⟨6967, 5, [(2, 1), (3, 4), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_7213 : Nat.Prime 7213 := by
  apply nodeValid_prime [2, 3, 601] ⟨7213, 5, [(2, 2), (3, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
  · decide +kernel

theorem prime_10267 : Nat.Prime 10267 := by
  apply nodeValid_prime [2, 3, 29, 59] ⟨10267, 2, [(2, 1), (3, 1), (29, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_59
  · decide +kernel

theorem prime_11287 : Nat.Prime 11287 := by
  apply nodeValid_prime [2, 3, 11, 19] ⟨11287, 3, [(2, 1), (3, 3), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_16091 : Nat.Prime 16091 := by
  apply nodeValid_prime [2, 5, 1609] ⟨16091, 6, [(2, 1), (5, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1609
  · decide +kernel

theorem prime_18481 : Nat.Prime 18481 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨18481, 13, [(2, 4), (3, 1), (5, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_21601 : Nat.Prime 21601 := by
  apply nodeValid_prime [2, 3, 5] ⟨21601, 7, [(2, 5), (3, 3), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_23357 : Nat.Prime 23357 := by
  apply nodeValid_prime [2, 5839] ⟨23357, 2, [(2, 2), (5839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5839
  · decide +kernel

theorem prime_30103 : Nat.Prime 30103 := by
  apply nodeValid_prime [2, 3, 29, 173] ⟨30103, 3, [(2, 1), (3, 1), (29, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_173
  · decide +kernel

theorem prime_36563 : Nat.Prime 36563 := by
  apply nodeValid_prime [2, 101, 181] ⟨36563, 2, [(2, 1), (101, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_181
  · decide +kernel

theorem prime_47779 : Nat.Prime 47779 := by
  apply nodeValid_prime [2, 3, 7963] ⟨47779, 3, [(2, 1), (3, 1), (7963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7963
  · decide +kernel

theorem prime_54581 : Nat.Prime 54581 := by
  apply nodeValid_prime [2, 5, 2729] ⟨54581, 10, [(2, 2), (5, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2729
  · decide +kernel

theorem prime_58453 : Nat.Prime 58453 := by
  apply nodeValid_prime [2, 3, 4871] ⟨58453, 2, [(2, 2), (3, 1), (4871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4871
  · decide +kernel

theorem prime_61603 : Nat.Prime 61603 := by
  apply nodeValid_prime [2, 3, 10267] ⟨61603, 2, [(2, 1), (3, 1), (10267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10267
  · decide +kernel

theorem prime_65437 : Nat.Prime 65437 := by
  apply nodeValid_prime [2, 3, 7, 19, 41] ⟨65437, 6, [(2, 2), (3, 1), (7, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_71233 : Nat.Prime 71233 := by
  apply nodeValid_prime [2, 3, 7, 53] ⟨71233, 11, [(2, 6), (3, 1), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_78901 : Nat.Prime 78901 := by
  apply nodeValid_prime [2, 3, 5, 263] ⟨78901, 10, [(2, 2), (3, 1), (5, 2), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_91309 : Nat.Prime 91309 := by
  apply nodeValid_prime [2, 3, 7, 1087] ⟨91309, 10, [(2, 2), (3, 1), (7, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1087
  · decide +kernel

theorem prime_92899 : Nat.Prime 92899 := by
  apply nodeValid_prime [2, 3, 13, 397] ⟨92899, 7, [(2, 1), (3, 2), (13, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_397
  · decide +kernel

theorem prime_98711 : Nat.Prime 98711 := by
  apply nodeValid_prime [2, 5, 9871] ⟨98711, 13, [(2, 1), (5, 1), (9871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9871
  · decide +kernel

theorem prime_110819 : Nat.Prime 110819 := by
  apply nodeValid_prime [2, 67, 827] ⟨110819, 2, [(2, 1), (67, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_827
  · decide +kernel

theorem prime_113723 : Nat.Prime 113723 := by
  apply nodeValid_prime [2, 7, 8123] ⟨113723, 5, [(2, 1), (7, 1), (8123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8123
  · decide +kernel

theorem prime_124433 : Nat.Prime 124433 := by
  apply nodeValid_prime [2, 7, 11, 101] ⟨124433, 6, [(2, 4), (7, 1), (11, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_101
  · decide +kernel

theorem prime_127691 : Nat.Prime 127691 := by
  apply nodeValid_prime [2, 5, 113] ⟨127691, 2, [(2, 1), (5, 1), (113, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_139121 : Nat.Prime 139121 := by
  apply nodeValid_prime [2, 5, 37, 47] ⟨139121, 3, [(2, 4), (5, 1), (37, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_47
  · decide +kernel

theorem prime_139369 : Nat.Prime 139369 := by
  apply nodeValid_prime [2, 3, 5807] ⟨139369, 11, [(2, 3), (3, 1), (5807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5807
  · decide +kernel

theorem prime_150247 : Nat.Prime 150247 := by
  apply nodeValid_prime [2, 3, 17, 491] ⟨150247, 3, [(2, 1), (3, 2), (17, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_491
  · decide +kernel

theorem prime_169891 : Nat.Prime 169891 := by
  apply nodeValid_prime [2, 3, 5, 7, 809] ⟨169891, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_809
  · decide +kernel

theorem prime_177907 : Nat.Prime 177907 := by
  apply nodeValid_prime [2, 3, 149, 199] ⟨177907, 2, [(2, 1), (3, 1), (149, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_199
  · decide +kernel

theorem prime_197311 : Nat.Prime 197311 := by
  apply nodeValid_prime [2, 3, 5, 6577] ⟨197311, 7, [(2, 1), (3, 1), (5, 1), (6577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6577
  · decide +kernel

theorem prime_208379 : Nat.Prime 208379 := by
  apply nodeValid_prime [2, 43, 2423] ⟨208379, 2, [(2, 1), (43, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2423
  · decide +kernel

theorem prime_215483 : Nat.Prime 215483 := by
  apply nodeValid_prime [2, 107741] ⟨215483, 2, [(2, 1), (107741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_107741
  · decide +kernel

theorem prime_222293 : Nat.Prime 222293 := by
  apply nodeValid_prime [2, 7, 17, 467] ⟨222293, 2, [(2, 2), (7, 1), (17, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_467
  · decide +kernel

theorem prime_255383 : Nat.Prime 255383 := by
  apply nodeValid_prime [2, 127691] ⟨255383, 5, [(2, 1), (127691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_127691
  · decide +kernel

theorem prime_274529 : Nat.Prime 274529 := by
  apply nodeValid_prime [2, 23, 373] ⟨274529, 3, [(2, 5), (23, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_373
  · decide +kernel

theorem prime_279029 : Nat.Prime 279029 := by
  apply nodeValid_prime [2, 79, 883] ⟨279029, 2, [(2, 2), (79, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_883
  · decide +kernel

theorem prime_281339 : Nat.Prime 281339 := by
  apply nodeValid_prime [2, 163, 863] ⟨281339, 2, [(2, 1), (163, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_863
  · decide +kernel

theorem prime_295417 : Nat.Prime 295417 := by
  apply nodeValid_prime [2, 3, 11, 373] ⟨295417, 5, [(2, 3), (3, 2), (11, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_373
  · decide +kernel

theorem prime_320821 : Nat.Prime 320821 := by
  apply nodeValid_prime [2, 3, 5, 5347] ⟨320821, 2, [(2, 2), (3, 1), (5, 1), (5347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5347
  · decide +kernel

theorem prime_390781 : Nat.Prime 390781 := by
  apply nodeValid_prime [2, 3, 5, 13, 167] ⟨390781, 6, [(2, 2), (3, 2), (5, 1), (13, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_167
  · decide +kernel

theorem prime_407947 : Nat.Prime 407947 := by
  apply nodeValid_prime [2, 3, 7, 11, 883] ⟨407947, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_883
  · decide +kernel

theorem prime_507953 : Nat.Prime 507953 := by
  apply nodeValid_prime [2, 53, 599] ⟨507953, 3, [(2, 4), (53, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_599
  · decide +kernel

theorem prime_556849 : Nat.Prime 556849 := by
  apply nodeValid_prime [2, 3, 1289] ⟨556849, 11, [(2, 4), (3, 3), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1289
  · decide +kernel

theorem prime_571339 : Nat.Prime 571339 := by
  apply nodeValid_prime [2, 3, 31741] ⟨571339, 3, [(2, 1), (3, 2), (31741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31741
  · decide +kernel

theorem prime_588383 : Nat.Prime 588383 := by
  apply nodeValid_prime [2, 109, 2699] ⟨588383, 5, [(2, 1), (109, 1), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_2699
  · decide +kernel

theorem prime_697999 : Nat.Prime 697999 := by
  apply nodeValid_prime [2, 3, 7, 16619] ⟨697999, 3, [(2, 1), (3, 1), (7, 1), (16619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_16619
  · decide +kernel

theorem prime_705259 : Nat.Prime 705259 := by
  apply nodeValid_prime [2, 3, 39181] ⟨705259, 2, [(2, 1), (3, 2), (39181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39181
  · decide +kernel

theorem prime_789689 : Nat.Prime 789689 := by
  apply nodeValid_prime [2, 98711] ⟨789689, 3, [(2, 3), (98711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_98711
  · decide +kernel

theorem prime_832933 : Nat.Prime 832933 := by
  apply nodeValid_prime [2, 3, 17, 1361] ⟨832933, 2, [(2, 2), (3, 2), (17, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1361
  · decide +kernel

theorem prime_980773 : Nat.Prime 980773 := by
  apply nodeValid_prime [2, 3, 13, 6287] ⟨980773, 2, [(2, 2), (3, 1), (13, 1), (6287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6287
  · decide +kernel

theorem prime_1025561 : Nat.Prime 1025561 := by
  apply nodeValid_prime [2, 5, 25639] ⟨1025561, 3, [(2, 3), (5, 1), (25639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25639
  · decide +kernel

theorem prime_1054219 : Nat.Prime 1054219 := by
  apply nodeValid_prime [2, 3, 11, 15973] ⟨1054219, 2, [(2, 1), (3, 1), (11, 1), (15973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_15973
  · decide +kernel

theorem prime_1176767 : Nat.Prime 1176767 := by
  apply nodeValid_prime [2, 588383] ⟨1176767, 5, [(2, 1), (588383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_588383
  · decide +kernel

theorem prime_1257457 : Nat.Prime 1257457 := by
  apply nodeValid_prime [2, 3, 17, 23, 67] ⟨1257457, 5, [(2, 4), (3, 1), (17, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_1485889 : Nat.Prime 1485889 := by
  apply nodeValid_prime [2, 3, 71, 109] ⟨1485889, 7, [(2, 6), (3, 1), (71, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_109
  · decide +kernel

theorem prime_1502471 : Nat.Prime 1502471 := by
  apply nodeValid_prime [2, 5, 150247] ⟨1502471, 11, [(2, 1), (5, 1), (150247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_150247
  · decide +kernel

theorem prime_1567127 : Nat.Prime 1567127 := by
  apply nodeValid_prime [2, 11, 71233] ⟨1567127, 5, [(2, 1), (11, 1), (71233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71233
  · decide +kernel

theorem prime_1661557 : Nat.Prime 1661557 := by
  apply nodeValid_prime [2, 3, 13, 10651] ⟨1661557, 2, [(2, 2), (3, 1), (13, 1), (10651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_10651
  · decide +kernel

theorem prime_1662781 : Nat.Prime 1662781 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 107] ⟨1662781, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (37, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_107
  · decide +kernel

theorem prime_1742063 : Nat.Prime 1742063 := by
  apply nodeValid_prime [2, 7, 124433] ⟨1742063, 5, [(2, 1), (7, 1), (124433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_124433
  · decide +kernel

theorem prime_2126897 : Nat.Prime 2126897 := by
  apply nodeValid_prime [2, 307, 433] ⟨2126897, 3, [(2, 4), (307, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_433
  · decide +kernel

theorem prime_2285357 : Nat.Prime 2285357 := by
  apply nodeValid_prime [2, 571339] ⟨2285357, 2, [(2, 2), (571339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_571339
  · decide +kernel

theorem prime_2401253 : Nat.Prime 2401253 := by
  apply nodeValid_prime [2, 7, 191, 449] ⟨2401253, 2, [(2, 2), (7, 1), (191, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_191
    · exact prime_449
  · decide +kernel

theorem prime_2733781 : Nat.Prime 2733781 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 283] ⟨2733781, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (23, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_283
  · decide +kernel

theorem prime_3004943 : Nat.Prime 3004943 := by
  apply nodeValid_prime [2, 1502471] ⟨3004943, 5, [(2, 1), (1502471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1502471
  · decide +kernel

theorem prime_3025487 : Nat.Prime 3025487 := by
  apply nodeValid_prime [2, 593, 2551] ⟨3025487, 5, [(2, 1), (593, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_593
    · exact prime_2551
  · decide +kernel

theorem prime_3552667 : Nat.Prime 3552667 := by
  apply nodeValid_prime [2, 3, 13, 37, 1231] ⟨3552667, 3, [(2, 1), (3, 1), (13, 1), (37, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_1231
  · decide +kernel

theorem prime_3686027 : Nat.Prime 3686027 := by
  apply nodeValid_prime [2, 23, 227, 353] ⟨3686027, 2, [(2, 1), (23, 1), (227, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_227
    · exact prime_353
  · decide +kernel

theorem prime_4181071 : Nat.Prime 4181071 := by
  apply nodeValid_prime [2, 3, 5, 139369] ⟨4181071, 11, [(2, 1), (3, 1), (5, 1), (139369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139369
  · decide +kernel

theorem prime_4329041 : Nat.Prime 4329041 := by
  apply nodeValid_prime [2, 5, 53, 1021] ⟨4329041, 3, [(2, 4), (5, 1), (53, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_1021
  · decide +kernel

theorem prime_4552087 : Nat.Prime 4552087 := by
  apply nodeValid_prime [2, 3, 7, 11, 59, 167] ⟨4552087, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (59, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_59
    · exact prime_167
  · decide +kernel

theorem prime_4959583 : Nat.Prime 4959583 := by
  apply nodeValid_prime [2, 3, 23, 83, 433] ⟨4959583, 3, [(2, 1), (3, 1), (23, 1), (83, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_83
    · exact prime_433
  · decide +kernel

theorem prime_4970249 : Nat.Prime 4970249 := by
  apply nodeValid_prime [2, 19, 1721] ⟨4970249, 3, [(2, 3), (19, 2), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1721
  · decide +kernel

theorem prime_5432417 : Nat.Prime 5432417 := by
  apply nodeValid_prime [2, 11, 23, 61] ⟨5432417, 3, [(2, 5), (11, 2), (23, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_61
  · decide +kernel

theorem prime_5668447 : Nat.Prime 5668447 := by
  apply nodeValid_prime [2, 3, 7, 17, 467] ⟨5668447, 3, [(2, 1), (3, 1), (7, 1), (17, 2), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_467
  · decide +kernel

theorem prime_8675521 : Nat.Prime 8675521 := by
  apply nodeValid_prime [2, 3, 5, 7, 1291] ⟨8675521, 33, [(2, 6), (3, 1), (5, 1), (7, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1291
  · decide +kernel

theorem prime_8784929 : Nat.Prime 8784929 := by
  apply nodeValid_prime [2, 274529] ⟨8784929, 3, [(2, 5), (274529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_274529
  · decide +kernel

theorem prime_8939701 : Nat.Prime 8939701 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 43] ⟨8939701, 6, [(2, 2), (3, 3), (5, 2), (7, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_9276989 : Nat.Prime 9276989 := by
  apply nodeValid_prime [2, 7, 41, 8081] ⟨9276989, 2, [(2, 2), (7, 1), (41, 1), (8081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_8081
  · decide +kernel

theorem prime_9559349 : Nat.Prime 9559349 := by
  apply nodeValid_prime [2, 113, 21149] ⟨9559349, 2, [(2, 2), (113, 1), (21149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_21149
  · decide +kernel

theorem prime_17830669 : Nat.Prime 17830669 := by
  apply nodeValid_prime [2, 3, 1485889] ⟨17830669, 2, [(2, 2), (3, 1), (1485889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1485889
  · decide +kernel

theorem prime_21577007 : Nat.Prime 21577007 := by
  apply nodeValid_prime [2, 11, 980773] ⟨21577007, 5, [(2, 1), (11, 1), (980773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_980773
  · decide +kernel

theorem prime_49846711 : Nat.Prime 49846711 := by
  apply nodeValid_prime [2, 3, 5, 1661557] ⟨49846711, 6, [(2, 1), (3, 1), (5, 1), (1661557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1661557
  · decide +kernel

theorem prime_54274793 : Nat.Prime 54274793 := by
  apply nodeValid_prime [2, 11, 13, 19, 227] ⟨54274793, 3, [(2, 3), (11, 2), (13, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_58489297 : Nat.Prime 58489297 := by
  apply nodeValid_prime [2, 3, 19, 59, 1087] ⟨58489297, 5, [(2, 4), (3, 1), (19, 1), (59, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
    · exact prime_1087
  · decide +kernel

theorem prime_62923759 : Nat.Prime 62923759 := by
  apply nodeValid_prime [2, 3, 449, 23357] ⟨62923759, 3, [(2, 1), (3, 1), (449, 1), (23357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
    · exact prime_23357
  · decide +kernel

theorem prime_119885551 : Nat.Prime 119885551 := by
  apply nodeValid_prime [2, 3, 5, 37, 21601] ⟨119885551, 6, [(2, 1), (3, 1), (5, 2), (37, 1), (21601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_21601
  · decide +kernel

theorem prime_160914619 : Nat.Prime 160914619 := by
  apply nodeValid_prime [2, 3, 8939701] ⟨160914619, 2, [(2, 1), (3, 2), (8939701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8939701
  · decide +kernel

theorem prime_174054059 : Nat.Prime 174054059 := by
  apply nodeValid_prime [2, 17, 277, 18481] ⟨174054059, 2, [(2, 1), (17, 1), (277, 1), (18481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_277
    · exact prime_18481
  · decide +kernel

theorem prime_253944371 : Nat.Prime 253944371 := by
  apply nodeValid_prime [2, 5, 73, 233, 1493] ⟨253944371, 2, [(2, 1), (5, 1), (73, 1), (233, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_233
    · exact prime_1493
  · decide +kernel

theorem prime_281379101 : Nat.Prime 281379101 := by
  apply nodeValid_prime [2, 5, 43, 65437] ⟨281379101, 2, [(2, 2), (5, 2), (43, 1), (65437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_65437
  · decide +kernel

theorem prime_307181869 : Nat.Prime 307181869 := by
  apply nodeValid_prime [2, 3, 7, 67, 54581] ⟨307181869, 2, [(2, 2), (3, 1), (7, 1), (67, 1), (54581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
    · exact prime_54581
  · decide +kernel

theorem prime_392869249 : Nat.Prime 392869249 := by
  apply nodeValid_prime [2, 3, 613, 1669] ⟨392869249, 7, [(2, 7), (3, 1), (613, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_1669
  · decide +kernel

theorem prime_801428363 : Nat.Prime 801428363 := by
  apply nodeValid_prime [2, 7, 37, 313, 4943] ⟨801428363, 5, [(2, 1), (7, 1), (37, 1), (313, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_313
    · exact prime_4943
  · decide +kernel

theorem prime_1329580579 : Nat.Prime 1329580579 := by
  apply nodeValid_prime [2, 3, 53, 4181071] ⟨1329580579, 2, [(2, 1), (3, 1), (53, 1), (4181071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_4181071
  · decide +kernel

theorem prime_1523666227 : Nat.Prime 1523666227 := by
  apply nodeValid_prime [2, 3, 253944371] ⟨1523666227, 3, [(2, 1), (3, 1), (253944371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_253944371
  · decide +kernel

theorem prime_1714883869 : Nat.Prime 1714883869 := by
  apply nodeValid_prime [2, 3, 997, 47779] ⟨1714883869, 2, [(2, 2), (3, 2), (997, 1), (47779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_997
    · exact prime_47779
  · decide +kernel

theorem prime_3026950699 : Nat.Prime 3026950699 := by
  apply nodeValid_prime [2, 3, 89, 5668447] ⟨3026950699, 2, [(2, 1), (3, 1), (89, 1), (5668447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_5668447
  · decide +kernel

theorem prime_3285194401 : Nat.Prime 3285194401 := by
  apply nodeValid_prime [2, 3, 5, 53, 8609] ⟨3285194401, 7, [(2, 5), (3, 2), (5, 2), (53, 1), (8609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_8609
  · decide +kernel

theorem prime_3888043459 : Nat.Prime 3888043459 := by
  apply nodeValid_prime [2, 3, 13, 49846711] ⟨3888043459, 2, [(2, 1), (3, 1), (13, 1), (49846711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_49846711
  · decide +kernel

theorem prime_4994714161 : Nat.Prime 4994714161 := by
  apply nodeValid_prime [2, 3, 5, 61, 113723] ⟨4994714161, 14, [(2, 4), (3, 2), (5, 1), (61, 1), (113723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_113723
  · decide +kernel

theorem prime_6520771853 : Nat.Prime 6520771853 := by
  apply nodeValid_prime [2, 7, 211, 919, 1201] ⟨6520771853, 2, [(2, 2), (7, 1), (211, 1), (919, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
    · exact prime_919
    · exact prime_1201
  · decide +kernel

theorem prime_7980915703 : Nat.Prime 7980915703 := by
  apply nodeValid_prime [2, 3, 1297, 1025561] ⟨7980915703, 3, [(2, 1), (3, 1), (1297, 1), (1025561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1297
    · exact prime_1025561
  · decide +kernel

theorem prime_8699061829 : Nat.Prime 8699061829 := by
  apply nodeValid_prime [2, 3, 1777, 407947] ⟨8699061829, 6, [(2, 2), (3, 1), (1777, 1), (407947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1777
    · exact prime_407947
  · decide +kernel

theorem prime_26820816931 : Nat.Prime 26820816931 := by
  apply nodeValid_prime [2, 3, 5, 1259, 78901] ⟨26820816931, 3, [(2, 1), (3, 3), (5, 1), (1259, 1), (78901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1259
    · exact prime_78901
  · decide +kernel

theorem prime_27745686299 : Nat.Prime 27745686299 := by
  apply nodeValid_prime [2, 11, 17, 2029, 36563] ⟨27745686299, 2, [(2, 1), (11, 1), (17, 1), (2029, 1), (36563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_2029
    · exact prime_36563
  · decide +kernel

theorem prime_32851944011 : Nat.Prime 32851944011 := by
  apply nodeValid_prime [2, 5, 3285194401] ⟨32851944011, 2, [(2, 1), (5, 1), (3285194401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3285194401
  · decide +kernel

theorem prime_42625402933 : Nat.Prime 42625402933 := by
  apply nodeValid_prime [2, 3, 7, 727, 697999] ⟨42625402933, 5, [(2, 2), (3, 1), (7, 1), (727, 1), (697999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_727
    · exact prime_697999
  · decide +kernel

theorem prime_92754421471 : Nat.Prime 92754421471 := by
  apply nodeValid_prime [2, 3, 5, 11287, 91309] ⟨92754421471, 15, [(2, 1), (3, 2), (5, 1), (11287, 1), (91309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11287
    · exact prime_91309
  · decide +kernel

theorem prime_106460954057 : Nat.Prime 106460954057 := by
  apply nodeValid_prime [2, 7639, 1742063] ⟨106460954057, 3, [(2, 3), (7639, 1), (1742063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7639
    · exact prime_1742063
  · decide +kernel

theorem prime_160924901587 : Nat.Prime 160924901587 := by
  apply nodeValid_prime [2, 3, 26820816931] ⟨160924901587, 2, [(2, 1), (3, 1), (26820816931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26820816931
  · decide +kernel

theorem prime_214360483541 : Nat.Prime 214360483541 := by
  apply nodeValid_prime [2, 5, 7, 71, 73, 295417] ⟨214360483541, 3, [(2, 2), (5, 1), (7, 1), (71, 1), (73, 1), (295417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_73
    · exact prime_295417
  · decide +kernel

theorem prime_424614759841 : Nat.Prime 424614759841 := by
  apply nodeValid_prime [2, 3, 5, 83, 3552667] ⟨424614759841, 7, [(2, 5), (3, 2), (5, 1), (83, 1), (3552667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_3552667
  · decide +kernel

theorem prime_424614759887 : Nat.Prime 424614759887 := by
  apply nodeValid_prime [2, 92899, 2285357] ⟨424614759887, 5, [(2, 1), (92899, 1), (2285357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_92899
    · exact prime_2285357
  · decide +kernel

theorem prime_427486297103 : Nat.Prime 427486297103 := by
  apply nodeValid_prime [2, 71, 607, 4959583] ⟨427486297103, 5, [(2, 1), (71, 1), (607, 1), (4959583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_607
    · exact prime_4959583
  · decide +kernel

theorem prime_428720967083 : Nat.Prime 428720967083 := by
  apply nodeValid_prime [2, 214360483541] ⟨428720967083, 2, [(2, 1), (214360483541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_214360483541
  · decide +kernel

theorem prime_430784107597 : Nat.Prime 430784107597 := by
  apply nodeValid_prime [2, 3, 1329580579] ⟨430784107597, 2, [(2, 2), (3, 4), (1329580579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1329580579
  · decide +kernel

theorem prime_1272616840853 : Nat.Prime 1272616840853 := by
  apply nodeValid_prime [2, 7, 10499, 4329041] ⟨1272616840853, 3, [(2, 2), (7, 1), (10499, 1), (4329041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10499
    · exact prime_4329041
  · decide +kernel

theorem prime_2540328567047 : Nat.Prime 2540328567047 := by
  apply nodeValid_prime [2, 279029, 4552087] ⟨2540328567047, 5, [(2, 1), (279029, 1), (4552087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_279029
    · exact prime_4552087
  · decide +kernel

theorem prime_2540328567209 : Nat.Prime 2540328567209 := by
  apply nodeValid_prime [2, 58453, 5432417] ⟨2540328567209, 3, [(2, 3), (58453, 1), (5432417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_58453
    · exact prime_5432417
  · decide +kernel

theorem prime_2540328715807 : Nat.Prime 2540328715807 := by
  apply nodeValid_prime [2, 3, 7, 61, 269, 3686027] ⟨2540328715807, 3, [(2, 1), (3, 1), (7, 1), (61, 1), (269, 1), (3686027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_269
    · exact prime_3686027
  · decide +kernel

theorem prime_2542780399871 : Nat.Prime 2542780399871 := by
  apply nodeValid_prime [2, 5, 223, 5779, 197311] ⟨2542780399871, 67, [(2, 1), (5, 1), (223, 1), (5779, 1), (197311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_223
    · exact prime_5779
    · exact prime_197311
  · decide +kernel

theorem prime_2542780421609 : Nat.Prime 2542780421609 := by
  apply nodeValid_prime [2, 7, 30103, 215483] ⟨2542780421609, 3, [(2, 3), (7, 2), (30103, 1), (215483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_30103
    · exact prime_215483
  · decide +kernel

theorem prime_2542780422187 : Nat.Prime 2542780422187 := by
  apply nodeValid_prime [2, 3, 109, 3888043459] ⟨2542780422187, 2, [(2, 1), (3, 1), (109, 1), (3888043459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_3888043459
  · decide +kernel

theorem prime_2545233644467 : Nat.Prime 2545233644467 := by
  apply nodeValid_prime [2, 3, 379, 2647, 15661] ⟨2545233644467, 2, [(2, 1), (3, 4), (379, 1), (2647, 1), (15661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_2647
    · exact prime_15661
  · decide +kernel

theorem prime_2545233645781 : Nat.Prime 2545233645781 := by
  apply nodeValid_prime [2, 3, 5, 7, 1289, 1567127] ⟨2545233645781, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (1289, 1), (1567127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1289
    · exact prime_1567127
  · decide +kernel

theorem prime_2545233681707 : Nat.Prime 2545233681707 := by
  apply nodeValid_prime [2, 1272616840853] ⟨2545233681707, 2, [(2, 1), (1272616840853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1272616840853
  · decide +kernel

theorem prime_2547688559047 : Nat.Prime 2547688559047 := by
  apply nodeValid_prime [2, 3, 424614759841] ⟨2547688559047, 6, [(2, 1), (3, 1), (424614759841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_424614759841
  · decide +kernel

theorem prime_2547688559323 : Nat.Prime 2547688559323 := by
  apply nodeValid_prime [2, 3, 424614759887] ⟨2547688559323, 2, [(2, 1), (3, 1), (424614759887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_424614759887
  · decide +kernel

theorem prime_2547688563923 : Nat.Prime 2547688563923 := by
  apply nodeValid_prime [2, 31, 43, 241, 1453, 2729] ⟨2547688563923, 2, [(2, 1), (31, 1), (43, 1), (241, 1), (1453, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_241
    · exact prime_1453
    · exact prime_2729
  · decide +kernel

theorem prime_2550145051067 : Nat.Prime 2550145051067 := by
  apply nodeValid_prime [2, 37, 43, 801428363] ⟨2550145051067, 2, [(2, 1), (37, 1), (43, 1), (801428363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
    · exact prime_801428363
  · decide +kernel

theorem prime_2550145093519 : Nat.Prime 2550145093519 := by
  apply nodeValid_prime [2, 3, 11, 16091, 2401253] ⟨2550145093519, 3, [(2, 1), (3, 1), (11, 1), (16091, 1), (2401253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_16091
    · exact prime_2401253
  · decide +kernel

theorem prime_2550145093939 : Nat.Prime 2550145093939 := by
  apply nodeValid_prime [2, 3, 13, 29, 47, 83, 163, 197] ⟨2550145093939, 7, [(2, 1), (3, 3), (13, 1), (29, 1), (47, 1), (83, 1), (163, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_47
    · exact prime_83
    · exact prime_163
    · exact prime_197
  · decide +kernel

theorem prime_2552603139509 : Nat.Prime 2552603139509 := by
  apply nodeValid_prime [2, 23, 27745686299] ⟨2552603139509, 2, [(2, 2), (23, 1), (27745686299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_27745686299
  · decide +kernel

theorem prime_2552603140069 : Nat.Prime 2552603140069 := by
  apply nodeValid_prime [2, 3, 255383, 832933] ⟨2552603140069, 6, [(2, 2), (3, 1), (255383, 1), (832933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_255383
    · exact prime_832933
  · decide +kernel

theorem prime_2552603151893 : Nat.Prime 2552603151893 := by
  apply nodeValid_prime [2, 5323, 119885551] ⟨2552603151893, 2, [(2, 2), (5323, 1), (119885551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5323
    · exact prime_119885551
  · decide +kernel

theorem prime_2555062860913 : Nat.Prime 2555062860913 := by
  apply nodeValid_prime [2, 3, 2467, 21577007] ⟨2555062860913, 5, [(2, 4), (3, 1), (2467, 1), (21577007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2467
    · exact prime_21577007
  · decide +kernel

theorem prime_2555062896961 : Nat.Prime 2555062896961 := by
  apply nodeValid_prime [2, 3, 5, 7, 911, 139121] ⟨2555062896961, 23, [(2, 6), (3, 2), (5, 1), (7, 1), (911, 1), (139121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_911
    · exact prime_139121
  · decide +kernel

theorem prime_2555062897369 : Nat.Prime 2555062897369 := by
  apply nodeValid_prime [2, 3, 106460954057] ⟨2555062897369, 7, [(2, 3), (3, 1), (106460954057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_106460954057
  · decide +kernel

theorem prime_2557524175981 : Nat.Prime 2557524175981 := by
  apply nodeValid_prime [2, 3, 5, 42625402933] ⟨2557524175981, 7, [(2, 2), (3, 1), (5, 1), (42625402933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_42625402933
  · decide +kernel

theorem prime_2557524177347 : Nat.Prime 2557524177347 := by
  apply nodeValid_prime [2, 29, 2473, 17830669] ⟨2557524177347, 2, [(2, 1), (29, 1), (2473, 1), (17830669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_2473
    · exact prime_17830669
  · decide +kernel

theorem prime_2557524177727 : Nat.Prime 2557524177727 := by
  apply nodeValid_prime [2, 3, 7, 8699061829] ⟨2557524177727, 6, [(2, 1), (3, 1), (7, 2), (8699061829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8699061829
  · decide +kernel

theorem prime_2559987060899 : Nat.Prime 2559987060899 := by
  apply nodeValid_prime [2, 4549, 281379101] ⟨2559987060899, 2, [(2, 1), (4549, 1), (281379101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4549
    · exact prime_281379101
  · decide +kernel

theorem prime_2559987061409 : Nat.Prime 2559987061409 := by
  apply nodeValid_prime [2, 7, 499, 1283, 17851] ⟨2559987061409, 3, [(2, 5), (7, 1), (499, 1), (1283, 1), (17851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_499
    · exact prime_1283
    · exact prime_17851
  · decide +kernel

theorem prime_2559987099773 : Nat.Prime 2559987099773 := by
  apply nodeValid_prime [2, 3677, 174054059] ⟨2559987099773, 2, [(2, 2), (3677, 1), (174054059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3677
    · exact prime_174054059
  · decide +kernel

theorem prime_2562451632859 : Nat.Prime 2562451632859 := by
  apply nodeValid_prime [2, 3, 13, 32851944011] ⟨2562451632859, 3, [(2, 1), (3, 1), (13, 1), (32851944011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_32851944011
  · decide +kernel

theorem prime_2562451633711 : Nat.Prime 2562451633711 := by
  apply nodeValid_prime [2, 3, 5, 89, 163, 193, 10169] ⟨2562451633711, 12, [(2, 1), (3, 2), (5, 1), (89, 1), (163, 1), (193, 1), (10169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_163
    · exact prime_193
    · exact prime_10169
  · decide +kernel

theorem prime_2562451633943 : Nat.Prime 2562451633943 := by
  apply nodeValid_prime [2, 37, 6967, 4970249] ⟨2562451633943, 5, [(2, 1), (37, 1), (6967, 1), (4970249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_6967
    · exact prime_4970249
  · decide +kernel

theorem prime_2564917768891 : Nat.Prime 2564917768891 := by
  apply nodeValid_prime [2, 3, 5, 151, 239, 789689] ⟨2564917768891, 3, [(2, 1), (3, 2), (5, 1), (151, 1), (239, 1), (789689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_239
    · exact prime_789689
  · decide +kernel

theorem prime_2564917782619 : Nat.Prime 2564917782619 := by
  apply nodeValid_prime [2, 3, 427486297103] ⟨2564917782619, 2, [(2, 1), (3, 1), (427486297103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_427486297103
  · decide +kernel

theorem prime_2564917783651 : Nat.Prime 2564917783651 := by
  apply nodeValid_prime [2, 3, 5, 73, 8675521] ⟨2564917783651, 2, [(2, 1), (3, 4), (5, 2), (73, 1), (8675521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_8675521
  · decide +kernel

theorem prime_2567385451909 : Nat.Prime 2567385451909 := by
  apply nodeValid_prime [2, 3, 222293, 320821] ⟨2567385451909, 2, [(2, 2), (3, 2), (222293, 1), (320821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_222293
    · exact prime_320821
  · decide +kernel

theorem prime_2567385452053 : Nat.Prime 2567385452053 := by
  apply nodeValid_prime [2, 3, 19, 83, 137, 36677] ⟨2567385452053, 5, [(2, 2), (3, 4), (19, 1), (83, 1), (137, 1), (36677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_83
    · exact prime_137
    · exact prime_36677
  · decide +kernel

theorem prime_2567385513377 : Nat.Prime 2567385513377 := by
  apply nodeValid_prime [2, 29, 2351, 1176767] ⟨2567385513377, 3, [(2, 5), (29, 1), (2351, 1), (1176767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_2351
    · exact prime_1176767
  · decide +kernel

theorem prime_2569854793763 : Nat.Prime 2569854793763 := by
  apply nodeValid_prime [2, 523, 6287, 390781] ⟨2569854793763, 2, [(2, 1), (523, 1), (6287, 1), (390781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_523
    · exact prime_6287
    · exact prime_390781
  · decide +kernel

theorem prime_2569854793907 : Nat.Prime 2569854793907 := by
  apply nodeValid_prime [2, 587, 3931, 556849] ⟨2569854793907, 2, [(2, 1), (587, 1), (3931, 1), (556849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_587
    · exact prime_3931
    · exact prime_556849
  · decide +kernel

theorem prime_2569854856367 : Nat.Prime 2569854856367 := by
  apply nodeValid_prime [2, 7, 23, 7980915703] ⟨2569854856367, 5, [(2, 1), (7, 1), (23, 1), (7980915703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_7980915703
  · decide +kernel

theorem prime_2572325802499 : Nat.Prime 2572325802499 := by
  apply nodeValid_prime [2, 3, 428720967083] ⟨2572325802499, 10, [(2, 1), (3, 1), (428720967083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_428720967083
  · decide +kernel

theorem prime_2572325803207 : Nat.Prime 2572325803207 := by
  apply nodeValid_prime [2, 3, 281339, 507953] ⟨2572325803207, 5, [(2, 1), (3, 2), (281339, 1), (507953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281339
    · exact prime_507953
  · decide +kernel

theorem prime_2572325803501 : Nat.Prime 2572325803501 := by
  apply nodeValid_prime [2, 3, 5, 1714883869] ⟨2572325803501, 7, [(2, 2), (3, 1), (5, 3), (1714883869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1714883869
  · decide +kernel

theorem prime_2574798354533 : Nat.Prime 2574798354533 := by
  apply nodeValid_prime [2, 151, 1409, 3025487] ⟨2574798354533, 2, [(2, 2), (151, 1), (1409, 1), (3025487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_1409
    · exact prime_3025487
  · decide +kernel

theorem prime_2574798425393 : Nat.Prime 2574798425393 := by
  apply nodeValid_prime [2, 160924901587] ⟨2574798425393, 3, [(2, 4), (160924901587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160924901587
  · decide +kernel

theorem prime_2574798425959 : Nat.Prime 2574798425959 := by
  apply nodeValid_prime [2, 3, 11, 127, 307181869] ⟨2574798425959, 3, [(2, 1), (3, 1), (11, 1), (127, 1), (307181869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_127
    · exact prime_307181869
  · decide +kernel

theorem prime_2577272382119 : Nat.Prime 2577272382119 := by
  apply nodeValid_prime [2, 7, 31, 43, 131, 1054219] ⟨2577272382119, 7, [(2, 1), (7, 1), (31, 1), (43, 1), (131, 1), (1054219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_43
    · exact prime_131
    · exact prime_1054219
  · decide +kernel

theorem prime_2577272383009 : Nat.Prime 2577272383009 := by
  apply nodeValid_prime [2, 3, 17, 58489297] ⟨2577272383009, 29, [(2, 5), (3, 4), (17, 1), (58489297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_58489297
  · decide +kernel

theorem prime_2577272507077 : Nat.Prime 2577272507077 := by
  apply nodeValid_prime [2, 3, 43, 4994714161] ⟨2577272507077, 2, [(2, 2), (3, 1), (43, 1), (4994714161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_4994714161
  · decide +kernel

theorem prime_2579748186947 : Nat.Prime 2579748186947 := by
  apply nodeValid_prime [2, 7, 110819, 1662781] ⟨2579748186947, 2, [(2, 1), (7, 1), (110819, 1), (1662781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_110819
    · exact prime_1662781
  · decide +kernel

theorem prime_2579748187493 : Nat.Prime 2579748187493 := by
  apply nodeValid_prime [2, 7, 79, 281, 577, 7193] ⟨2579748187493, 2, [(2, 2), (7, 1), (79, 1), (281, 1), (577, 1), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_281
    · exact prime_577
    · exact prime_7193
  · decide +kernel

theorem prime_2579748271483 : Nat.Prime 2579748271483 := by
  apply nodeValid_prime [2, 3, 6833, 62923759] ⟨2579748271483, 2, [(2, 1), (3, 1), (6833, 1), (62923759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6833
    · exact prime_62923759
  · decide +kernel

theorem prime_2582225648419 : Nat.Prime 2582225648419 := by
  apply nodeValid_prime [2, 3, 13, 23, 479, 3004943] ⟨2582225648419, 3, [(2, 1), (3, 1), (13, 1), (23, 1), (479, 1), (3004943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_479
    · exact prime_3004943
  · decide +kernel

theorem prime_2582225648923 : Nat.Prime 2582225648923 := by
  apply nodeValid_prime [2, 3, 157427, 2733781] ⟨2582225648923, 2, [(2, 1), (3, 1), (157427, 1), (2733781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157427
    · exact prime_2733781
  · decide +kernel

theorem prime_2582225653789 : Nat.Prime 2582225653789 := by
  apply nodeValid_prime [2, 3, 11, 6520771853] ⟨2582225653789, 2, [(2, 2), (3, 2), (11, 1), (6520771853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6520771853
  · decide +kernel

theorem prime_2584704645583 : Nat.Prime 2584704645583 := by
  apply nodeValid_prime [2, 3, 430784107597] ⟨2584704645583, 5, [(2, 1), (3, 1), (430784107597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_430784107597
  · decide +kernel

theorem prime_2584704716059 : Nat.Prime 2584704716059 := by
  apply nodeValid_prime [2, 3, 257, 661, 743, 3413] ⟨2584704716059, 2, [(2, 1), (3, 1), (257, 1), (661, 1), (743, 1), (3413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_661
    · exact prime_743
    · exact prime_3413
  · decide +kernel

theorem prime_2584704716161 : Nat.Prime 2584704716161 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 73, 16363] ⟨2584704716161, 77, [(2, 7), (3, 1), (5, 1), (7, 2), (23, 1), (73, 1), (16363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_73
    · exact prime_16363
  · decide +kernel

theorem prime_2587185244283 : Nat.Prime 2587185244283 := by
  apply nodeValid_prime [2, 8039, 160914619] ⟨2587185244283, 2, [(2, 1), (8039, 1), (160914619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8039
    · exact prime_160914619
  · decide +kernel

theorem prime_2587185246299 : Nat.Prime 2587185246299 := by
  apply nodeValid_prime [2, 19, 41, 179, 9276989] ⟨2587185246299, 2, [(2, 1), (19, 1), (41, 1), (179, 1), (9276989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_179
    · exact prime_9276989
  · decide +kernel

theorem prime_2587185253447 : Nat.Prime 2587185253447 := by
  apply nodeValid_prime [2, 3, 283, 1523666227] ⟨2587185253447, 5, [(2, 1), (3, 1), (283, 1), (1523666227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1523666227
  · decide +kernel

theorem prime_2589667473203 : Nat.Prime 2589667473203 := by
  apply nodeValid_prime [2, 23857, 54274793] ⟨2589667473203, 2, [(2, 1), (23857, 1), (54274793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23857
    · exact prime_54274793
  · decide +kernel

theorem prime_2589667530031 : Nat.Prime 2589667530031 := by
  apply nodeValid_prime [2, 3, 5, 7, 53, 1259, 61603] ⟨2589667530031, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (53, 1), (1259, 1), (61603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_1259
    · exact prime_61603
  · decide +kernel

theorem prime_2589667530721 : Nat.Prime 2589667530721 := by
  apply nodeValid_prime [2, 3, 5, 17, 1523, 208379] ⟨2589667530721, 14, [(2, 5), (3, 1), (5, 1), (17, 1), (1523, 1), (208379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1523
    · exact prime_208379
  · decide +kernel

theorem prime_2592151244141 : Nat.Prime 2592151244141 := by
  apply nodeValid_prime [2, 5, 29, 6337, 705259] ⟨2592151244141, 2, [(2, 2), (5, 1), (29, 1), (6337, 1), (705259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_6337
    · exact prime_705259
  · decide +kernel

theorem prime_2592151245821 : Nat.Prime 2592151245821 := by
  apply nodeValid_prime [2, 5, 101, 7213, 177907] ⟨2592151245821, 2, [(2, 2), (5, 1), (101, 1), (7213, 1), (177907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_7213
    · exact prime_177907
  · decide +kernel

theorem prime_2592151304903 : Nat.Prime 2592151304903 := by
  apply nodeValid_prime [2, 3299, 392869249] ⟨2592151304903, 5, [(2, 1), (3299, 1), (392869249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3299
    · exact prime_392869249
  · decide +kernel

theorem prime_2594636742977 : Nat.Prime 2594636742977 := by
  apply nodeValid_prime [2, 4241, 9559349] ⟨2594636742977, 3, [(2, 6), (4241, 1), (9559349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4241
    · exact prime_9559349
  · decide +kernel

theorem prime_2594636773801 : Nat.Prime 2594636773801 := by
  apply nodeValid_prime [2, 3, 5, 19, 181, 1257457] ⟨2594636773801, 22, [(2, 3), (3, 1), (5, 2), (19, 1), (181, 1), (1257457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_181
    · exact prime_1257457
  · decide +kernel

theorem prime_2594636774347 : Nat.Prime 2594636774347 := by
  apply nodeValid_prime [2, 3, 139, 409, 1471, 5171] ⟨2594636774347, 2, [(2, 1), (3, 1), (139, 1), (409, 1), (1471, 1), (5171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_409
    · exact prime_1471
    · exact prime_5171
  · decide +kernel

theorem prime_2597123699743 : Nat.Prime 2597123699743 := by
  apply nodeValid_prime [2, 3, 11, 13, 3026950699] ⟨2597123699743, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (3026950699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_3026950699
  · decide +kernel

theorem prime_2597123699987 : Nat.Prime 2597123699987 := by
  apply nodeValid_prime [2, 53, 2789, 8784929] ⟨2597123699987, 2, [(2, 1), (53, 1), (2789, 1), (8784929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_2789
    · exact prime_8784929
  · decide +kernel

theorem prime_2597123801189 : Nat.Prime 2597123801189 := by
  apply nodeValid_prime [2, 7, 92754421471] ⟨2597123801189, 2, [(2, 2), (7, 1), (92754421471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_92754421471
  · decide +kernel

theorem prime_2599612479631 : Nat.Prime 2599612479631 := by
  apply nodeValid_prime [2, 3, 5, 41, 3931, 19913] ⟨2599612479631, 3, [(2, 1), (3, 4), (5, 1), (41, 1), (3931, 1), (19913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_3931
    · exact prime_19913
  · decide +kernel

theorem prime_2599612619633 : Nat.Prime 2599612619633 := by
  apply nodeValid_prime [2, 7, 1559, 2126897] ⟨2599612619633, 3, [(2, 4), (7, 2), (1559, 1), (2126897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1559
    · exact prime_2126897
  · decide +kernel

theorem prime_2599612620151 : Nat.Prime 2599612620151 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 19, 59, 169891] ⟨2599612620151, 12, [(2, 1), (3, 1), (5, 2), (7, 1), (13, 1), (19, 1), (59, 1), (169891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_59
    · exact prime_169891
  · decide +kernel

end Sude.Lucas.Generated
