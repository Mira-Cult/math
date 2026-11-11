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

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_919 : Nat.Prime 919 := by
  apply nodeValid_prime [2, 3, 17] ⟨919, 7, [(2, 1), (3, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_1297 : Nat.Prime 1297 := by
  apply nodeValid_prime [2, 3] ⟨1297, 10, [(2, 4), (3, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_1571 : Nat.Prime 1571 := by
  apply nodeValid_prime [2, 5, 157] ⟨1571, 2, [(2, 1), (5, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
  · decide +kernel

theorem prime_1619 : Nat.Prime 1619 := by
  apply nodeValid_prime [2, 809] ⟨1619, 2, [(2, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_809
  · decide +kernel

theorem prime_1637 : Nat.Prime 1637 := by
  apply nodeValid_prime [2, 409] ⟨1637, 2, [(2, 2), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_409
  · decide +kernel

theorem prime_2333 : Nat.Prime 2333 := by
  apply nodeValid_prime [2, 11, 53] ⟨2333, 2, [(2, 2), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_2753 : Nat.Prime 2753 := by
  apply nodeValid_prime [2, 43] ⟨2753, 3, [(2, 6), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43
  · decide +kernel

theorem prime_3109 : Nat.Prime 3109 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨3109, 6, [(2, 2), (3, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_3463 : Nat.Prime 3463 := by
  apply nodeValid_prime [2, 3, 577] ⟨3463, 3, [(2, 1), (3, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
  · decide +kernel

theorem prime_3923 : Nat.Prime 3923 := by
  apply nodeValid_prime [2, 37, 53] ⟨3923, 2, [(2, 1), (37, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_53
  · decide +kernel

theorem prime_4327 : Nat.Prime 4327 := by
  apply nodeValid_prime [2, 3, 7, 103] ⟨4327, 3, [(2, 1), (3, 1), (7, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_4507 : Nat.Prime 4507 := by
  apply nodeValid_prime [2, 3, 751] ⟨4507, 2, [(2, 1), (3, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_751
  · decide +kernel

theorem prime_6679 : Nat.Prime 6679 := by
  apply nodeValid_prime [2, 3, 7, 53] ⟨6679, 7, [(2, 1), (3, 2), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_7417 : Nat.Prime 7417 := by
  apply nodeValid_prime [2, 3, 103] ⟨7417, 5, [(2, 3), (3, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_7901 : Nat.Prime 7901 := by
  apply nodeValid_prime [2, 5, 79] ⟨7901, 2, [(2, 2), (5, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_8461 : Nat.Prime 8461 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨8461, 6, [(2, 2), (3, 2), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_8599 : Nat.Prime 8599 := by
  apply nodeValid_prime [2, 3, 1433] ⟨8599, 3, [(2, 1), (3, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1433
  · decide +kernel

theorem prime_8929 : Nat.Prime 8929 := by
  apply nodeValid_prime [2, 3, 31] ⟨8929, 11, [(2, 5), (3, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_9011 : Nat.Prime 9011 := by
  apply nodeValid_prime [2, 5, 17, 53] ⟨9011, 2, [(2, 1), (5, 1), (17, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_53
  · decide +kernel

theorem prime_10273 : Nat.Prime 10273 := by
  apply nodeValid_prime [2, 3, 107] ⟨10273, 10, [(2, 5), (3, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
  · decide +kernel

theorem prime_11243 : Nat.Prime 11243 := by
  apply nodeValid_prime [2, 7, 11, 73] ⟨11243, 5, [(2, 1), (7, 1), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_11471 : Nat.Prime 11471 := by
  apply nodeValid_prime [2, 5, 31, 37] ⟨11471, 11, [(2, 1), (5, 1), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_12917 : Nat.Prime 12917 := by
  apply nodeValid_prime [2, 3229] ⟨12917, 2, [(2, 2), (3229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3229
  · decide +kernel

theorem prime_13463 : Nat.Prime 13463 := by
  apply nodeValid_prime [2, 53, 127] ⟨13463, 5, [(2, 1), (53, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_127
  · decide +kernel

theorem prime_15259 : Nat.Prime 15259 := by
  apply nodeValid_prime [2, 3, 2543] ⟨15259, 2, [(2, 1), (3, 1), (2543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2543
  · decide +kernel

theorem prime_15803 : Nat.Prime 15803 := by
  apply nodeValid_prime [2, 7901] ⟨15803, 2, [(2, 1), (7901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7901
  · decide +kernel

theorem prime_16033 : Nat.Prime 16033 := by
  apply nodeValid_prime [2, 3, 167] ⟨16033, 5, [(2, 5), (3, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
  · decide +kernel

theorem prime_17377 : Nat.Prime 17377 := by
  apply nodeValid_prime [2, 3, 181] ⟨17377, 7, [(2, 5), (3, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel

theorem prime_17569 : Nat.Prime 17569 := by
  apply nodeValid_prime [2, 3, 61] ⟨17569, 11, [(2, 5), (3, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel

theorem prime_18041 : Nat.Prime 18041 := by
  apply nodeValid_prime [2, 5, 11, 41] ⟨18041, 3, [(2, 3), (5, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_18787 : Nat.Prime 18787 := by
  apply nodeValid_prime [2, 3, 31, 101] ⟨18787, 2, [(2, 1), (3, 1), (31, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_101
  · decide +kernel

theorem prime_20681 : Nat.Prime 20681 := by
  apply nodeValid_prime [2, 5, 11, 47] ⟨20681, 3, [(2, 3), (5, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_29311 : Nat.Prime 29311 := by
  apply nodeValid_prime [2, 3, 5, 977] ⟨29311, 3, [(2, 1), (3, 1), (5, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_977
  · decide +kernel

theorem prime_30071 : Nat.Prime 30071 := by
  apply nodeValid_prime [2, 5, 31, 97] ⟨30071, 13, [(2, 1), (5, 1), (31, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_97
  · decide +kernel

theorem prime_33427 : Nat.Prime 33427 := by
  apply nodeValid_prime [2, 3, 619] ⟨33427, 2, [(2, 1), (3, 3), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
  · decide +kernel

theorem prime_33629 : Nat.Prime 33629 := by
  apply nodeValid_prime [2, 7, 1201] ⟨33629, 2, [(2, 2), (7, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1201
  · decide +kernel

theorem prime_34217 : Nat.Prime 34217 := by
  apply nodeValid_prime [2, 7, 13, 47] ⟨34217, 3, [(2, 3), (7, 1), (13, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_34651 : Nat.Prime 34651 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨34651, 2, [(2, 1), (3, 2), (5, 2), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_36809 : Nat.Prime 36809 := by
  apply nodeValid_prime [2, 43, 107] ⟨36809, 3, [(2, 3), (43, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_107
  · decide +kernel

theorem prime_39227 : Nat.Prime 39227 := by
  apply nodeValid_prime [2, 11, 1783] ⟨39227, 2, [(2, 1), (11, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1783
  · decide +kernel

theorem prime_40813 : Nat.Prime 40813 := by
  apply nodeValid_prime [2, 3, 19, 179] ⟨40813, 2, [(2, 2), (3, 1), (19, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_179
  · decide +kernel

theorem prime_43271 : Nat.Prime 43271 := by
  apply nodeValid_prime [2, 5, 4327] ⟨43271, 13, [(2, 1), (5, 1), (4327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4327
  · decide +kernel

theorem prime_43963 : Nat.Prime 43963 := by
  apply nodeValid_prime [2, 3, 17, 431] ⟨43963, 12, [(2, 1), (3, 1), (17, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_431
  · decide +kernel

theorem prime_64439 : Nat.Prime 64439 := by
  apply nodeValid_prime [2, 11, 29, 101] ⟨64439, 7, [(2, 1), (11, 1), (29, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_101
  · decide +kernel

theorem prime_66791 : Nat.Prime 66791 := by
  apply nodeValid_prime [2, 5, 6679] ⟨66791, 7, [(2, 1), (5, 1), (6679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6679
  · decide +kernel

theorem prime_68687 : Nat.Prime 68687 := by
  apply nodeValid_prime [2, 61, 563] ⟨68687, 5, [(2, 1), (61, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_563
  · decide +kernel

theorem prime_88003 : Nat.Prime 88003 := by
  apply nodeValid_prime [2, 3, 4889] ⟨88003, 2, [(2, 1), (3, 2), (4889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4889
  · decide +kernel

theorem prime_89821 : Nat.Prime 89821 := by
  apply nodeValid_prime [2, 3, 5, 499] ⟨89821, 2, [(2, 2), (3, 2), (5, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_499
  · decide +kernel

theorem prime_90017 : Nat.Prime 90017 := by
  apply nodeValid_prime [2, 29, 97] ⟨90017, 3, [(2, 5), (29, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_97
  · decide +kernel

theorem prime_91631 : Nat.Prime 91631 := by
  apply nodeValid_prime [2, 5, 7, 11, 17] ⟨91631, 7, [(2, 1), (5, 1), (7, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_94999 : Nat.Prime 94999 := by
  apply nodeValid_prime [2, 3, 71, 223] ⟨94999, 3, [(2, 1), (3, 1), (71, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_223
  · decide +kernel

theorem prime_95917 : Nat.Prime 95917 := by
  apply nodeValid_prime [2, 3, 7993] ⟨95917, 2, [(2, 2), (3, 1), (7993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7993
  · decide +kernel

theorem prime_99181 : Nat.Prime 99181 := by
  apply nodeValid_prime [2, 3, 5, 19, 29] ⟨99181, 7, [(2, 2), (3, 2), (5, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_101341 : Nat.Prime 101341 := by
  apply nodeValid_prime [2, 3, 5, 563] ⟨101341, 2, [(2, 2), (3, 2), (5, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_563
  · decide +kernel

theorem prime_105367 : Nat.Prime 105367 := by
  apply nodeValid_prime [2, 3, 17, 1033] ⟨105367, 3, [(2, 1), (3, 1), (17, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1033
  · decide +kernel

theorem prime_108247 : Nat.Prime 108247 := by
  apply nodeValid_prime [2, 3, 18041] ⟨108247, 3, [(2, 1), (3, 1), (18041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18041
  · decide +kernel

theorem prime_119849 : Nat.Prime 119849 := by
  apply nodeValid_prime [2, 71, 211] ⟨119849, 3, [(2, 3), (71, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_211
  · decide +kernel

theorem prime_123007 : Nat.Prime 123007 := by
  apply nodeValid_prime [2, 3, 13, 19, 83] ⟨123007, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_128879 : Nat.Prime 128879 := by
  apply nodeValid_prime [2, 64439] ⟨128879, 7, [(2, 1), (64439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_64439
  · decide +kernel

theorem prime_133709 : Nat.Prime 133709 := by
  apply nodeValid_prime [2, 33427] ⟨133709, 2, [(2, 2), (33427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33427
  · decide +kernel

theorem prime_135743 : Nat.Prime 135743 := by
  apply nodeValid_prime [2, 67, 1013] ⟨135743, 5, [(2, 1), (67, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_1013
  · decide +kernel

theorem prime_165449 : Nat.Prime 165449 := by
  apply nodeValid_prime [2, 20681] ⟨165449, 3, [(2, 3), (20681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20681
  · decide +kernel

theorem prime_167191 : Nat.Prime 167191 := by
  apply nodeValid_prime [2, 3, 5, 5573] ⟨167191, 3, [(2, 1), (3, 1), (5, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5573
  · decide +kernel

theorem prime_190357 : Nat.Prime 190357 := by
  apply nodeValid_prime [2, 3, 29, 547] ⟨190357, 6, [(2, 2), (3, 1), (29, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_547
  · decide +kernel

theorem prime_197597 : Nat.Prime 197597 := by
  apply nodeValid_prime [2, 7, 7057] ⟨197597, 2, [(2, 2), (7, 1), (7057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7057
  · decide +kernel

theorem prime_206623 : Nat.Prime 206623 := by
  apply nodeValid_prime [2, 3, 13, 883] ⟨206623, 5, [(2, 1), (3, 2), (13, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_883
  · decide +kernel

theorem prime_217667 : Nat.Prime 217667 := by
  apply nodeValid_prime [2, 43, 2531] ⟨217667, 2, [(2, 1), (43, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2531
  · decide +kernel

theorem prime_236209 : Nat.Prime 236209 := by
  apply nodeValid_prime [2, 3, 7, 19, 37] ⟨236209, 22, [(2, 4), (3, 1), (7, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_239699 : Nat.Prime 239699 := by
  apply nodeValid_prime [2, 119849] ⟨239699, 2, [(2, 1), (119849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_119849
  · decide +kernel

theorem prime_267419 : Nat.Prime 267419 := by
  apply nodeValid_prime [2, 133709] ⟨267419, 2, [(2, 1), (133709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_133709
  · decide +kernel

theorem prime_272287 : Nat.Prime 272287 := by
  apply nodeValid_prime [2, 3, 7, 2161] ⟨272287, 7, [(2, 1), (3, 2), (7, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2161
  · decide +kernel

theorem prime_299521 : Nat.Prime 299521 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨299521, 22, [(2, 9), (3, 2), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_322351 : Nat.Prime 322351 := by
  apply nodeValid_prime [2, 3, 5, 7, 307] ⟨322351, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_307
  · decide +kernel

theorem prime_421469 : Nat.Prime 421469 := by
  apply nodeValid_prime [2, 105367] ⟨421469, 2, [(2, 2), (105367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_105367
  · decide +kernel

theorem prime_494693 : Nat.Prime 494693 := by
  apply nodeValid_prime [2, 11, 11243] ⟨494693, 2, [(2, 2), (11, 1), (11243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11243
  · decide +kernel

theorem prime_527071 : Nat.Prime 527071 := by
  apply nodeValid_prime [2, 3, 5, 17569] ⟨527071, 3, [(2, 1), (3, 1), (5, 1), (17569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17569
  · decide +kernel

theorem prime_534839 : Nat.Prime 534839 := by
  apply nodeValid_prime [2, 267419] ⟨534839, 7, [(2, 1), (267419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_267419
  · decide +kernel

theorem prime_542891 : Nat.Prime 542891 := by
  apply nodeValid_prime [2, 5, 233] ⟨542891, 2, [(2, 1), (5, 1), (233, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
  · decide +kernel

theorem prime_741877 : Nat.Prime 741877 := by
  apply nodeValid_prime [2, 3, 211, 293] ⟨741877, 2, [(2, 2), (3, 1), (211, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_293
  · decide +kernel

theorem prime_826493 : Nat.Prime 826493 := by
  apply nodeValid_prime [2, 206623] ⟨826493, 2, [(2, 2), (206623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_206623
  · decide +kernel

theorem prime_867743 : Nat.Prime 867743 := by
  apply nodeValid_prime [2, 271, 1601] ⟨867743, 5, [(2, 1), (271, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_1601
  · decide +kernel

theorem prime_898211 : Nat.Prime 898211 := by
  apply nodeValid_prime [2, 5, 89821] ⟨898211, 6, [(2, 1), (5, 1), (89821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89821
  · decide +kernel

theorem prime_1019903 : Nat.Prime 1019903 := by
  apply nodeValid_prime [2, 13, 39227] ⟨1019903, 5, [(2, 1), (13, 1), (39227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_39227
  · decide +kernel

theorem prime_1021417 : Nat.Prime 1021417 := by
  apply nodeValid_prime [2, 3, 11, 53, 73] ⟨1021417, 5, [(2, 3), (3, 1), (11, 1), (53, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_73
  · decide +kernel

theorem prime_1098649 : Nat.Prime 1098649 := by
  apply nodeValid_prime [2, 3, 15259] ⟨1098649, 11, [(2, 3), (3, 2), (15259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15259
  · decide +kernel

theorem prime_1143953 : Nat.Prime 1143953 := by
  apply nodeValid_prime [2, 19, 53, 71] ⟨1143953, 3, [(2, 4), (19, 1), (53, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_53
    · exact prime_71
  · decide +kernel

theorem prime_1192673 : Nat.Prime 1192673 := by
  apply nodeValid_prime [2, 13, 47, 61] ⟨1192673, 3, [(2, 5), (13, 1), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_1246057 : Nat.Prime 1246057 := by
  apply nodeValid_prime [2, 3, 7, 7417] ⟨1246057, 5, [(2, 3), (3, 1), (7, 1), (7417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7417
  · decide +kernel

theorem prime_1714411 : Nat.Prime 1714411 := by
  apply nodeValid_prime [2, 3, 5, 43, 443] ⟨1714411, 12, [(2, 1), (3, 2), (5, 1), (43, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_443
  · decide +kernel

theorem prime_1789367 : Nat.Prime 1789367 := by
  apply nodeValid_prime [2, 181, 4943] ⟨1789367, 5, [(2, 1), (181, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_4943
  · decide +kernel

theorem prime_1800341 : Nat.Prime 1800341 := by
  apply nodeValid_prime [2, 5, 90017] ⟨1800341, 2, [(2, 2), (5, 1), (90017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_90017
  · decide +kernel

theorem prime_2996681 : Nat.Prime 2996681 := by
  apply nodeValid_prime [2, 5, 19, 3943] ⟨2996681, 3, [(2, 3), (5, 1), (19, 1), (3943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3943
  · decide +kernel

theorem prime_3257347 : Nat.Prime 3257347 := by
  apply nodeValid_prime [2, 3, 542891] ⟨3257347, 2, [(2, 1), (3, 1), (542891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_542891
  · decide +kernel

theorem prime_3557621 : Nat.Prime 3557621 := by
  apply nodeValid_prime [2, 5, 11, 103, 157] ⟨3557621, 2, [(2, 2), (5, 1), (11, 1), (103, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_103
    · exact prime_157
  · decide +kernel

theorem prime_3600683 : Nat.Prime 3600683 := by
  apply nodeValid_prime [2, 1800341] ⟨3600683, 2, [(2, 1), (1800341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1800341
  · decide +kernel

theorem prime_4712537 : Nat.Prime 4712537 := by
  apply nodeValid_prime [2, 17, 34651] ⟨4712537, 3, [(2, 3), (17, 1), (34651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_34651
  · decide +kernel

theorem prime_4793429 : Nat.Prime 4793429 := by
  apply nodeValid_prime [2, 229, 5233] ⟨4793429, 2, [(2, 2), (229, 1), (5233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_5233
  · decide +kernel

theorem prime_6992261 : Nat.Prime 6992261 := by
  apply nodeValid_prime [2, 5, 11, 37, 859] ⟨6992261, 2, [(2, 2), (5, 1), (11, 1), (37, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_859
  · decide +kernel

theorem prime_9586859 : Nat.Prime 9586859 := by
  apply nodeValid_prime [2, 4793429] ⟨9586859, 2, [(2, 1), (4793429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4793429
  · decide +kernel

theorem prime_11271571 : Nat.Prime 11271571 := by
  apply nodeValid_prime [2, 3, 5, 241, 1559] ⟨11271571, 2, [(2, 1), (3, 1), (5, 1), (241, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
    · exact prime_1559
  · decide +kernel

theorem prime_15246613 : Nat.Prime 15246613 := by
  apply nodeValid_prime [2, 3, 47, 9011] ⟨15246613, 2, [(2, 2), (3, 2), (47, 1), (9011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_9011
  · decide +kernel

theorem prime_16500541 : Nat.Prime 16500541 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 2311] ⟨16500541, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_2311
  · decide +kernel

theorem prime_35258453 : Nat.Prime 35258453 := by
  apply nodeValid_prime [2, 19, 43, 10789] ⟨35258453, 2, [(2, 2), (19, 1), (43, 1), (10789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_10789
  · decide +kernel

theorem prime_39578087 : Nat.Prime 39578087 := by
  apply nodeValid_prime [2, 37, 534839] ⟨39578087, 10, [(2, 1), (37, 1), (534839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_534839
  · decide +kernel

theorem prime_69488873 : Nat.Prime 69488873 := by
  apply nodeValid_prime [2, 29, 299521] ⟨69488873, 3, [(2, 3), (29, 1), (299521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_299521
  · decide +kernel

theorem prime_91067729 : Nat.Prime 91067729 := by
  apply nodeValid_prime [2, 1571, 3623] ⟨91067729, 3, [(2, 4), (1571, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1571
    · exact prime_3623
  · decide +kernel

theorem prime_91479679 : Nat.Prime 91479679 := by
  apply nodeValid_prime [2, 3, 15246613] ⟨91479679, 6, [(2, 1), (3, 1), (15246613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15246613
  · decide +kernel

theorem prime_95868587 : Nat.Prime 95868587 := by
  apply nodeValid_prime [2, 11, 43, 101341] ⟨95868587, 2, [(2, 1), (11, 1), (43, 1), (101341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_101341
  · decide +kernel

theorem prime_172563463 : Nat.Prime 172563463 := by
  apply nodeValid_prime [2, 3, 9586859] ⟨172563463, 3, [(2, 1), (3, 2), (9586859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9586859
  · decide +kernel

theorem prime_185446361 : Nat.Prime 185446361 := by
  apply nodeValid_prime [2, 5, 11, 421469] ⟨185446361, 3, [(2, 3), (5, 1), (11, 1), (421469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_421469
  · decide +kernel

theorem prime_197777351 : Nat.Prime 197777351 := by
  apply nodeValid_prime [2, 5, 443, 8929] ⟨197777351, 7, [(2, 1), (5, 2), (443, 1), (8929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_443
    · exact prime_8929
  · decide +kernel

theorem prime_224716379 : Nat.Prime 224716379 := by
  apply nodeValid_prime [2, 2753, 40813] ⟨224716379, 2, [(2, 1), (2753, 1), (40813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2753
    · exact prime_40813
  · decide +kernel

theorem prime_265705919 : Nat.Prime 265705919 := by
  apply nodeValid_prime [2, 19, 6992261] ⟨265705919, 13, [(2, 1), (19, 1), (6992261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_6992261
  · decide +kernel

theorem prime_337919369 : Nat.Prime 337919369 := by
  apply nodeValid_prime [2, 29, 383, 3803] ⟨337919369, 3, [(2, 3), (29, 1), (383, 1), (3803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_383
    · exact prime_3803
  · decide +kernel

theorem prime_390881641 : Nat.Prime 390881641 := by
  apply nodeValid_prime [2, 3, 5, 3257347] ⟨390881641, 7, [(2, 3), (3, 1), (5, 1), (3257347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3257347
  · decide +kernel

theorem prime_514187411 : Nat.Prime 514187411 := by
  apply nodeValid_prime [2, 5, 11, 139, 33629] ⟨514187411, 2, [(2, 1), (5, 1), (11, 1), (139, 1), (33629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_139
    · exact prime_33629
  · decide +kernel

theorem prime_715909211 : Nat.Prime 715909211 := by
  apply nodeValid_prime [2, 5, 101, 433, 1637] ⟨715909211, 2, [(2, 1), (5, 1), (101, 1), (433, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_433
    · exact prime_1637
  · decide +kernel

theorem prime_849172481 : Nat.Prime 849172481 := by
  apply nodeValid_prime [2, 5, 13, 6379] ⟨849172481, 6, [(2, 11), (5, 1), (13, 1), (6379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_6379
  · decide +kernel

theorem prime_1042827043 : Nat.Prime 1042827043 := by
  apply nodeValid_prime [2, 3, 31, 1619, 3463] ⟨1042827043, 2, [(2, 1), (3, 1), (31, 1), (1619, 1), (3463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1619
    · exact prime_3463
  · decide +kernel

theorem prime_2070761557 : Nat.Prime 2070761557 := by
  apply nodeValid_prime [2, 3, 172563463] ⟨2070761557, 6, [(2, 2), (3, 1), (172563463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_172563463
  · decide +kernel

theorem prime_3188471029 : Nat.Prime 3188471029 := by
  apply nodeValid_prime [2, 3, 265705919] ⟨3188471029, 2, [(2, 2), (3, 1), (265705919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_265705919
  · decide +kernel

theorem prime_4524937861 : Nat.Prime 4524937861 := by
  apply nodeValid_prime [2, 3, 5, 29, 577, 4507] ⟨4524937861, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (577, 1), (4507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_577
    · exact prime_4507
  · decide +kernel

theorem prime_10055417131 : Nat.Prime 10055417131 := by
  apply nodeValid_prime [2, 3, 5, 11, 43, 236209] ⟨10055417131, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (43, 1), (236209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_236209
  · decide +kernel

theorem prime_10353807419 : Nat.Prime 10353807419 := by
  apply nodeValid_prime [2, 29, 10273, 17377] ⟨10353807419, 2, [(2, 1), (29, 1), (10273, 1), (17377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_10273
    · exact prime_17377
  · decide +kernel

theorem prime_12840936023 : Nat.Prime 12840936023 := by
  apply nodeValid_prime [2, 19, 337919369] ⟨12840936023, 5, [(2, 1), (19, 1), (337919369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_337919369
  · decide +kernel

theorem prime_15495964853 : Nat.Prime 15495964853 := by
  apply nodeValid_prime [2, 3109, 1246057] ⟨15495964853, 2, [(2, 2), (3109, 1), (1246057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3109
    · exact prime_1246057
  · decide +kernel

theorem prime_15495964909 : Nat.Prime 15495964909 := by
  apply nodeValid_prime [2, 3, 523, 4721] ⟨15495964909, 7, [(2, 2), (3, 1), (523, 2), (4721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_4721
  · decide +kernel

theorem prime_15495966853 : Nat.Prime 15495966853 := by
  apply nodeValid_prime [2, 3, 13463, 95917] ⟨15495966853, 5, [(2, 2), (3, 1), (13463, 1), (95917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13463
    · exact prime_95917
  · decide +kernel

theorem prime_15600361013 : Nat.Prime 15600361013 := by
  apply nodeValid_prime [2, 31, 1373, 91631] ⟨15600361013, 2, [(2, 2), (31, 1), (1373, 1), (91631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1373
    · exact prime_91631
  · decide +kernel

theorem prime_22881335621 : Nat.Prime 22881335621 := by
  apply nodeValid_prime [2, 5, 11, 13, 499, 16033] ⟨22881335621, 3, [(2, 2), (5, 1), (11, 1), (13, 1), (499, 1), (16033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_499
    · exact prime_16033
  · decide +kernel

theorem prime_30853266757 : Nat.Prime 30853266757 := by
  apply nodeValid_prime [2, 3, 13, 197777351] ⟨30853266757, 2, [(2, 2), (3, 1), (13, 1), (197777351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_197777351
  · decide +kernel

theorem prime_45147187369 : Nat.Prime 45147187369 := by
  apply nodeValid_prime [2, 3, 17, 839, 43963] ⟨45147187369, 23, [(2, 3), (3, 2), (17, 1), (839, 1), (43963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_839
    · exact prime_43963
  · decide +kernel

theorem prime_47010670417 : Nat.Prime 47010670417 := by
  apply nodeValid_prime [2, 3, 23, 59, 113, 2129] ⟨47010670417, 5, [(2, 4), (3, 2), (23, 1), (59, 1), (113, 1), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_59
    · exact prime_113
    · exact prime_2129
  · decide +kernel

theorem prime_89277188813 : Nat.Prime 89277188813 := by
  apply nodeValid_prime [2, 7, 3188471029] ⟨89277188813, 2, [(2, 2), (7, 1), (3188471029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3188471029
  · decide +kernel

theorem prime_90908444531 : Nat.Prime 90908444531 := by
  apply nodeValid_prime [2, 5, 193, 347, 135743] ⟨90908444531, 2, [(2, 1), (5, 1), (193, 1), (347, 1), (135743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
    · exact prime_347
    · exact prime_135743
  · decide +kernel

theorem prime_91938173081 : Nat.Prime 91938173081 := by
  apply nodeValid_prime [2, 5, 13, 59, 2996681] ⟨91938173081, 6, [(2, 3), (5, 1), (13, 1), (59, 1), (2996681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_59
    · exact prime_2996681
  · decide +kernel

theorem prime_178149373319 : Nat.Prime 178149373319 := by
  apply nodeValid_prime [2, 7, 31, 457, 898211] ⟨178149373319, 7, [(2, 1), (7, 1), (31, 1), (457, 1), (898211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_457
    · exact prime_898211
  · decide +kernel

theorem prime_178149373387 : Nat.Prime 178149373387 := by
  apply nodeValid_prime [2, 3, 34217, 867743] ⟨178149373387, 3, [(2, 1), (3, 1), (34217, 1), (867743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34217
    · exact prime_867743
  · decide +kernel

theorem prime_178149378521 : Nat.Prime 178149378521 := by
  apply nodeValid_prime [2, 5, 19, 131, 1789367] ⟨178149378521, 6, [(2, 3), (5, 1), (19, 1), (131, 1), (1789367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_131
    · exact prime_1789367
  · decide +kernel

theorem prime_178554377627 : Nat.Prime 178554377627 := by
  apply nodeValid_prime [2, 89277188813] ⟨178554377627, 2, [(2, 1), (89277188813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_89277188813
  · decide +kernel

theorem prime_178554378547 : Nat.Prime 178554378547 := by
  apply nodeValid_prime [2, 3, 17, 2143, 272287] ⟨178554378547, 2, [(2, 1), (3, 2), (17, 1), (2143, 1), (272287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2143
    · exact prime_272287
  · decide +kernel

theorem prime_178554379519 : Nat.Prime 178554379519 := by
  apply nodeValid_prime [2, 3, 19, 4051, 128879] ⟨178554379519, 6, [(2, 1), (3, 2), (19, 1), (4051, 1), (128879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_4051
    · exact prime_128879
  · decide +kernel

theorem prime_178960002233 : Nat.Prime 178960002233 := by
  apply nodeValid_prime [2, 11, 18787, 108247] ⟨178960002233, 5, [(2, 3), (11, 1), (18787, 1), (108247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_18787
    · exact prime_108247
  · decide +kernel

theorem prime_178960007321 : Nat.Prime 178960007321 := by
  apply nodeValid_prime [2, 5, 3911, 1143953] ⟨178960007321, 3, [(2, 3), (5, 1), (3911, 1), (1143953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3911
    · exact prime_1143953
  · decide +kernel

theorem prime_179366251159 : Nat.Prime 179366251159 := by
  apply nodeValid_prime [2, 3, 577, 1571, 10993] ⟨179366251159, 6, [(2, 1), (3, 2), (577, 1), (1571, 1), (10993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
    · exact prime_1571
    · exact prime_10993
  · decide +kernel

theorem prime_179366251397 : Nat.Prime 179366251397 := by
  apply nodeValid_prime [2, 43, 1042827043] ⟨179366251397, 2, [(2, 2), (43, 1), (1042827043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1042827043
  · decide +kernel

theorem prime_179366260999 : Nat.Prime 179366260999 := by
  apply nodeValid_prime [2, 3, 29311, 1019903] ⟨179366260999, 3, [(2, 1), (3, 1), (29311, 1), (1019903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29311
    · exact prime_1019903
  · decide +kernel

theorem prime_179773103201 : Nat.Prime 179773103201 := by
  apply nodeValid_prime [2, 5, 224716379] ⟨179773103201, 6, [(2, 5), (5, 2), (224716379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_224716379
  · decide +kernel

theorem prime_179773104323 : Nat.Prime 179773104323 := by
  apply nodeValid_prime [2, 7, 12840936023] ⟨179773104323, 5, [(2, 1), (7, 1), (12840936023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12840936023
  · decide +kernel

theorem prime_179773137461 : Nat.Prime 179773137461 := by
  apply nodeValid_prime [2, 5, 7, 107, 1714411] ⟨179773137461, 2, [(2, 2), (5, 1), (7, 2), (107, 1), (1714411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_107
    · exact prime_1714411
  · decide +kernel

theorem prime_180180631721 : Nat.Prime 180180631721 := by
  apply nodeValid_prime [2, 5, 67, 89, 317, 2383] ⟨180180631721, 7, [(2, 3), (5, 1), (67, 1), (89, 1), (317, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_89
    · exact prime_317
    · exact prime_2383
  · decide +kernel

theorem prime_180180633299 : Nat.Prime 180180633299 := by
  apply nodeValid_prime [2, 43, 1907, 1098649] ⟨180180633299, 2, [(2, 1), (43, 1), (1907, 1), (1098649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1907
    · exact prime_1098649
  · decide +kernel

theorem prime_180180636899 : Nat.Prime 180180636899 := by
  apply nodeValid_prime [2, 17, 1361, 1669, 2333] ⟨180180636899, 2, [(2, 1), (17, 1), (1361, 1), (1669, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1361
    · exact prime_1669
    · exact prime_2333
  · decide +kernel

theorem prime_180588748801 : Nat.Prime 180588748801 := by
  apply nodeValid_prime [2, 3, 5, 173, 1699] ⟨180588748801, 7, [(2, 13), (3, 1), (5, 2), (173, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_1699
  · decide +kernel

theorem prime_180588749477 : Nat.Prime 180588749477 := by
  apply nodeValid_prime [2, 45147187369] ⟨180588749477, 2, [(2, 2), (45147187369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45147187369
  · decide +kernel

theorem prime_180588764801 : Nat.Prime 180588764801 := by
  apply nodeValid_prime [2, 5, 569, 99181] ⟨180588764801, 3, [(2, 7), (5, 2), (569, 1), (99181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_569
    · exact prime_99181
  · decide +kernel

theorem prime_180997507693 : Nat.Prime 180997507693 := by
  apply nodeValid_prime [2, 3, 1733, 322351] ⟨180997507693, 2, [(2, 2), (3, 4), (1733, 1), (322351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1733
    · exact prime_322351
  · decide +kernel

theorem prime_180997508359 : Nat.Prime 180997508359 := by
  apply nodeValid_prime [2, 3, 10055417131] ⟨180997508359, 3, [(2, 1), (3, 2), (10055417131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10055417131
  · decide +kernel

theorem prime_180997514441 : Nat.Prime 180997514441 := by
  apply nodeValid_prime [2, 5, 4524937861] ⟨180997514441, 6, [(2, 3), (5, 1), (4524937861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4524937861
  · decide +kernel

theorem prime_181406886949 : Nat.Prime 181406886949 := by
  apply nodeValid_prime [2, 3, 7, 19, 229, 165449] ⟨181406886949, 14, [(2, 2), (3, 2), (7, 1), (19, 1), (229, 1), (165449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_229
    · exact prime_165449
  · decide +kernel

theorem prime_181406916169 : Nat.Prime 181406916169 := by
  apply nodeValid_prime [2, 3, 83, 91067729] ⟨181406916169, 7, [(2, 3), (3, 1), (83, 1), (91067729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_91067729
  · decide +kernel

theorem prime_181406916349 : Nat.Prime 181406916349 := by
  apply nodeValid_prime [2, 3, 7, 12917, 167191] ⟨181406916349, 2, [(2, 2), (3, 1), (7, 1), (12917, 1), (167191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12917
    · exact prime_167191
  · decide +kernel

theorem prime_181816888063 : Nat.Prime 181816888063 := by
  apply nodeValid_prime [2, 3, 19, 643, 919, 2699] ⟨181816888063, 6, [(2, 1), (3, 1), (19, 1), (643, 1), (919, 1), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_643
    · exact prime_919
    · exact prime_2699
  · decide +kernel

theorem prime_181816889063 : Nat.Prime 181816889063 := by
  apply nodeValid_prime [2, 90908444531] ⟨181816889063, 5, [(2, 1), (90908444531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90908444531
  · decide +kernel

theorem prime_181816889099 : Nat.Prime 181816889099 := by
  apply nodeValid_prime [2, 13, 8461, 826493] ⟨181816889099, 2, [(2, 1), (13, 1), (8461, 1), (826493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8461
    · exact prime_826493
  · decide +kernel

theorem prime_182227510009 : Nat.Prime 182227510009 := by
  apply nodeValid_prime [2, 3, 47, 71, 593, 1279] ⟨182227510009, 7, [(2, 3), (3, 2), (47, 1), (71, 1), (593, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_71
    · exact prime_593
    · exact prime_1279
  · decide +kernel

theorem prime_182227510147 : Nat.Prime 182227510147 := by
  apply nodeValid_prime [2, 3, 11, 89, 157, 197597] ⟨182227510147, 3, [(2, 1), (3, 1), (11, 1), (89, 1), (157, 1), (197597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89
    · exact prime_157
    · exact prime_197597
  · decide +kernel

theorem prime_182227520569 : Nat.Prime 182227520569 := by
  apply nodeValid_prime [2, 3, 83, 91479679] ⟨182227520569, 7, [(2, 3), (3, 1), (83, 1), (91479679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_91479679
  · decide +kernel

theorem prime_182638786541 : Nat.Prime 182638786541 := by
  apply nodeValid_prime [2, 5, 7, 37, 35258453] ⟨182638786541, 2, [(2, 2), (5, 1), (7, 1), (37, 1), (35258453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_35258453
  · decide +kernel

theorem prime_182638787183 : Nat.Prime 182638787183 := by
  apply nodeValid_prime [2, 23, 3329, 1192673] ⟨182638787183, 5, [(2, 1), (23, 1), (3329, 1), (1192673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3329
    · exact prime_1192673
  · decide +kernel

theorem prime_182638787263 : Nat.Prime 182638787263 := by
  apply nodeValid_prime [2, 3, 53, 8599, 66791] ⟨182638787263, 3, [(2, 1), (3, 1), (53, 1), (8599, 1), (66791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_8599
    · exact prime_66791
  · decide +kernel

theorem prime_183050684969 : Nat.Prime 183050684969 := by
  apply nodeValid_prime [2, 22881335621] ⟨183050684969, 3, [(2, 3), (22881335621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22881335621
  · decide +kernel

theorem prime_183050717627 : Nat.Prime 183050717627 := by
  apply nodeValid_prime [2, 7, 68687, 190357] ⟨183050717627, 5, [(2, 1), (7, 1), (68687, 1), (190357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_68687
    · exact prime_190357
  · decide +kernel

theorem prime_183050718317 : Nat.Prime 183050718317 := by
  apply nodeValid_prime [2, 89, 514187411] ⟨183050718317, 2, [(2, 2), (89, 1), (514187411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_514187411
  · decide +kernel

theorem prime_183463214593 : Nat.Prime 183463214593 := by
  apply nodeValid_prime [2, 3, 7, 23, 741877] ⟨183463214593, 10, [(2, 9), (3, 1), (7, 1), (23, 1), (741877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_741877
  · decide +kernel

theorem prime_183463217611 : Nat.Prime 183463217611 := by
  apply nodeValid_prime [2, 3, 5, 31, 823, 239699] ⟨183463217611, 2, [(2, 1), (3, 1), (5, 1), (31, 1), (823, 1), (239699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_823
    · exact prime_239699
  · decide +kernel

theorem prime_183463218403 : Nat.Prime 183463218403 := by
  apply nodeValid_prime [2, 3, 331, 751, 123007] ⟨183463218403, 5, [(2, 1), (3, 1), (331, 1), (751, 1), (123007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
    · exact prime_751
    · exact prime_123007
  · decide +kernel

theorem prime_183876345281 : Nat.Prime 183876345281 := by
  apply nodeValid_prime [2, 5, 71, 2063, 3923] ⟨183876345281, 7, [(2, 6), (5, 1), (71, 1), (2063, 1), (3923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_2063
    · exact prime_3923
  · decide +kernel

theorem prime_183876346163 : Nat.Prime 183876346163 := by
  apply nodeValid_prime [2, 91938173081] ⟨183876346163, 2, [(2, 1), (91938173081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_91938173081
  · decide +kernel

theorem prime_183876374921 : Nat.Prime 183876374921 := by
  apply nodeValid_prime [2, 5, 7, 431, 217667] ⟨183876374921, 6, [(2, 3), (5, 1), (7, 2), (431, 1), (217667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_431
    · exact prime_217667
  · decide +kernel

theorem prime_184290157307 : Nat.Prime 184290157307 := by
  apply nodeValid_prime [2, 157, 163, 3600683] ⟨184290157307, 2, [(2, 1), (157, 1), (163, 1), (3600683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_163
    · exact prime_3600683
  · decide +kernel

theorem prime_184290183643 : Nat.Prime 184290183643 := by
  apply nodeValid_prime [2, 3, 30071, 1021417] ⟨184290183643, 2, [(2, 1), (3, 1), (30071, 1), (1021417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30071
    · exact prime_1021417
  · decide +kernel

theorem prime_184290185851 : Nat.Prime 184290185851 := by
  apply nodeValid_prime [2, 3, 5, 109, 11271571] ⟨184290185851, 10, [(2, 1), (3, 1), (5, 2), (109, 1), (11271571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_11271571
  · decide +kernel

theorem prime_184704567079 : Nat.Prime 184704567079 := by
  apply nodeValid_prime [2, 3, 17, 509, 3557621] ⟨184704567079, 3, [(2, 1), (3, 1), (17, 1), (509, 1), (3557621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_509
    · exact prime_3557621
  · decide +kernel

theorem prime_184704575557 : Nat.Prime 184704575557 := by
  apply nodeValid_prime [2, 3, 83, 185446361] ⟨184704575557, 2, [(2, 2), (3, 1), (83, 1), (185446361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_185446361
  · decide +kernel

theorem prime_184704576439 : Nat.Prime 184704576439 := by
  apply nodeValid_prime [2, 3, 43, 715909211] ⟨184704576439, 3, [(2, 1), (3, 1), (43, 1), (715909211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_715909211
  · decide +kernel

theorem prime_185119600543 : Nat.Prime 185119600543 := by
  apply nodeValid_prime [2, 3, 30853266757] ⟨185119600543, 5, [(2, 1), (3, 1), (30853266757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30853266757
  · decide +kernel

theorem prime_185119600859 : Nat.Prime 185119600859 := by
  apply nodeValid_prime [2, 109, 849172481] ⟨185119600859, 2, [(2, 1), (109, 1), (849172481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_849172481
  · decide +kernel

theorem prime_185119611353 : Nat.Prime 185119611353 := by
  apply nodeValid_prime [2, 13, 41, 457, 94999] ⟨185119611353, 3, [(2, 3), (13, 1), (41, 1), (457, 1), (94999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_457
    · exact prime_94999
  · decide +kernel

theorem prime_185535290911 : Nat.Prime 185535290911 := by
  apply nodeValid_prime [2, 3, 5, 89, 69488873] ⟨185535290911, 15, [(2, 1), (3, 1), (5, 1), (89, 1), (69488873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_69488873
  · decide +kernel

theorem prime_185535316793 : Nat.Prime 185535316793 := by
  apply nodeValid_prime [2, 7, 23, 3329, 43271] ⟨185535316793, 3, [(2, 3), (7, 1), (23, 1), (3329, 1), (43271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_3329
    · exact prime_43271
  · decide +kernel

theorem prime_185535316853 : Nat.Prime 185535316853 := by
  apply nodeValid_prime [2, 88003, 527071] ⟨185535316853, 2, [(2, 2), (88003, 1), (527071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_88003
    · exact prime_527071
  · decide +kernel

theorem prime_185951578237 : Nat.Prime 185951578237 := by
  apply nodeValid_prime [2, 3, 15495964853] ⟨185951578237, 2, [(2, 2), (3, 1), (15495964853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15495964853
  · decide +kernel

theorem prime_185951578909 : Nat.Prime 185951578909 := by
  apply nodeValid_prime [2, 3, 15495964909] ⟨185951578909, 6, [(2, 2), (3, 1), (15495964909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15495964909
  · decide +kernel

theorem prime_185951602237 : Nat.Prime 185951602237 := by
  apply nodeValid_prime [2, 3, 15495966853] ⟨185951602237, 2, [(2, 2), (3, 1), (15495966853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15495966853
  · decide +kernel

theorem prime_186368533129 : Nat.Prime 186368533129 := by
  apply nodeValid_prime [2, 3, 95868587] ⟨186368533129, 19, [(2, 3), (3, 5), (95868587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_95868587
  · decide +kernel

theorem prime_186368533543 : Nat.Prime 186368533543 := by
  apply nodeValid_prime [2, 3, 10353807419] ⟨186368533543, 3, [(2, 1), (3, 2), (10353807419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10353807419
  · decide +kernel

theorem prime_186368540131 : Nat.Prime 186368540131 := by
  apply nodeValid_prime [2, 3, 5, 2070761557] ⟨186368540131, 2, [(2, 1), (3, 2), (5, 1), (2070761557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2070761557
  · decide +kernel

theorem prime_186786116533 : Nat.Prime 186786116533 := by
  apply nodeValid_prime [2, 3, 367, 4712537] ⟨186786116533, 2, [(2, 2), (3, 3), (367, 1), (4712537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_4712537
  · decide +kernel

theorem prime_186786124121 : Nat.Prime 186786124121 := by
  apply nodeValid_prime [2, 5, 283, 16500541] ⟨186786124121, 3, [(2, 3), (5, 1), (283, 1), (16500541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_283
    · exact prime_16500541
  · decide +kernel

theorem prime_186786126809 : Nat.Prime 186786126809 := by
  apply nodeValid_prime [2, 17, 79, 127, 367, 373] ⟨186786126809, 3, [(2, 3), (17, 1), (79, 1), (127, 1), (367, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_79
    · exact prime_127
    · exact prime_367
    · exact prime_373
  · decide +kernel

theorem prime_187204332157 : Nat.Prime 187204332157 := by
  apply nodeValid_prime [2, 3, 15600361013] ⟨187204332157, 2, [(2, 2), (3, 1), (15600361013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15600361013
  · decide +kernel

theorem prime_187204351177 : Nat.Prime 187204351177 := by
  apply nodeValid_prime [2, 3, 163, 1901, 2797] ⟨187204351177, 5, [(2, 3), (3, 3), (163, 1), (1901, 1), (2797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_1901
    · exact prime_2797
  · decide +kernel

theorem prime_187204351511 : Nat.Prime 187204351511 := by
  apply nodeValid_prime [2, 5, 11, 43, 39578087] ⟨187204351511, 7, [(2, 1), (5, 1), (11, 1), (43, 1), (39578087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_39578087
  · decide +kernel

theorem prime_187623187681 : Nat.Prime 187623187681 := by
  apply nodeValid_prime [2, 3, 5, 390881641] ⟨187623187681, 7, [(2, 5), (3, 1), (5, 1), (390881641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_390881641
  · decide +kernel

theorem prime_187623202891 : Nat.Prime 187623202891 := by
  apply nodeValid_prime [2, 3, 5, 131, 1297, 36809] ⟨187623202891, 10, [(2, 1), (3, 1), (5, 1), (131, 1), (1297, 1), (36809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_1297
    · exact prime_36809
  · decide +kernel

theorem prime_187623203497 : Nat.Prime 187623203497 := by
  apply nodeValid_prime [2, 3, 15803, 494693] ⟨187623203497, 13, [(2, 3), (3, 1), (15803, 1), (494693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15803
    · exact prime_494693
  · decide +kernel

theorem prime_188042678407 : Nat.Prime 188042678407 := by
  apply nodeValid_prime [2, 3, 11, 19, 761, 3457] ⟨188042678407, 6, [(2, 1), (3, 2), (11, 1), (19, 2), (761, 1), (3457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_761
    · exact prime_3457
  · decide +kernel

theorem prime_188042680597 : Nat.Prime 188042680597 := by
  apply nodeValid_prime [2, 3, 601, 2273, 11471] ⟨188042680597, 2, [(2, 2), (3, 1), (601, 1), (2273, 1), (11471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
    · exact prime_2273
    · exact prime_11471
  · decide +kernel

theorem prime_188042681669 : Nat.Prime 188042681669 := by
  apply nodeValid_prime [2, 47010670417] ⟨188042681669, 2, [(2, 2), (47010670417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_47010670417
  · decide +kernel

end Sude.Lucas.Generated
