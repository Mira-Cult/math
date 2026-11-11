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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0055

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7703 : Nat.Prime 7703 := by
  apply nodeValid_prime [2, 3851] ⟨7703, 5, [(2, 1), (3851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3851
  · decide +kernel

theorem prime_9967 : Nat.Prime 9967 := by
  apply nodeValid_prime [2, 3, 11, 151] ⟨9967, 3, [(2, 1), (3, 1), (11, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_151
  · decide +kernel

theorem prime_10831 : Nat.Prime 10831 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨10831, 7, [(2, 1), (3, 1), (5, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_11119 : Nat.Prime 11119 := by
  apply nodeValid_prime [2, 3, 17, 109] ⟨11119, 3, [(2, 1), (3, 1), (17, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_109
  · decide +kernel

theorem prime_11839 : Nat.Prime 11839 := by
  apply nodeValid_prime [2, 3, 1973] ⟨11839, 3, [(2, 1), (3, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1973
  · decide +kernel

theorem prime_11863 : Nat.Prime 11863 := by
  apply nodeValid_prime [2, 3, 659] ⟨11863, 3, [(2, 1), (3, 2), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_659
  · decide +kernel

theorem prime_11981 : Nat.Prime 11981 := by
  apply nodeValid_prime [2, 5, 599] ⟨11981, 2, [(2, 2), (5, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_599
  · decide +kernel

theorem prime_14957 : Nat.Prime 14957 := by
  apply nodeValid_prime [2, 3739] ⟨14957, 2, [(2, 2), (3739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3739
  · decide +kernel

theorem prime_15277 : Nat.Prime 15277 := by
  apply nodeValid_prime [2, 3, 19, 67] ⟨15277, 6, [(2, 2), (3, 1), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_15359 : Nat.Prime 15359 := by
  apply nodeValid_prime [2, 7, 1097] ⟨15359, 11, [(2, 1), (7, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1097
  · decide +kernel

theorem prime_16411 : Nat.Prime 16411 := by
  apply nodeValid_prime [2, 3, 5, 547] ⟨16411, 3, [(2, 1), (3, 1), (5, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_547
  · decide +kernel

theorem prime_18493 : Nat.Prime 18493 := by
  apply nodeValid_prime [2, 3, 23, 67] ⟨18493, 2, [(2, 2), (3, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_21701 : Nat.Prime 21701 := by
  apply nodeValid_prime [2, 5, 7, 31] ⟨21701, 2, [(2, 2), (5, 2), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_22051 : Nat.Prime 22051 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨22051, 3, [(2, 1), (3, 2), (5, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_22133 : Nat.Prime 22133 := by
  apply nodeValid_prime [2, 11, 503] ⟨22133, 2, [(2, 2), (11, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_503
  · decide +kernel

theorem prime_22993 : Nat.Prime 22993 := by
  apply nodeValid_prime [2, 3, 479] ⟨22993, 5, [(2, 4), (3, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
  · decide +kernel

theorem prime_23143 : Nat.Prime 23143 := by
  apply nodeValid_prime [2, 3, 7, 19, 29] ⟨23143, 5, [(2, 1), (3, 1), (7, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_23971 : Nat.Prime 23971 := by
  apply nodeValid_prime [2, 3, 5, 17, 47] ⟨23971, 10, [(2, 1), (3, 1), (5, 1), (17, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_26171 : Nat.Prime 26171 := by
  apply nodeValid_prime [2, 5, 2617] ⟨26171, 2, [(2, 1), (5, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2617
  · decide +kernel

theorem prime_26699 : Nat.Prime 26699 := by
  apply nodeValid_prime [2, 7, 1907] ⟨26699, 2, [(2, 1), (7, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1907
  · decide +kernel

theorem prime_34253 : Nat.Prime 34253 := by
  apply nodeValid_prime [2, 8563] ⟨34253, 2, [(2, 2), (8563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8563
  · decide +kernel

theorem prime_37139 : Nat.Prime 37139 := by
  apply nodeValid_prime [2, 31, 599] ⟨37139, 2, [(2, 1), (31, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_599
  · decide +kernel

theorem prime_39869 : Nat.Prime 39869 := by
  apply nodeValid_prime [2, 9967] ⟨39869, 2, [(2, 2), (9967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9967
  · decide +kernel

theorem prime_43403 : Nat.Prime 43403 := by
  apply nodeValid_prime [2, 21701] ⟨43403, 2, [(2, 1), (21701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21701
  · decide +kernel

theorem prime_43793 : Nat.Prime 43793 := by
  apply nodeValid_prime [2, 7, 17, 23] ⟨43793, 3, [(2, 4), (7, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_52579 : Nat.Prime 52579 := by
  apply nodeValid_prime [2, 3, 23, 127] ⟨52579, 2, [(2, 1), (3, 2), (23, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_127
  · decide +kernel

theorem prime_52667 : Nat.Prime 52667 := by
  apply nodeValid_prime [2, 17, 1549] ⟨52667, 2, [(2, 1), (17, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1549
  · decide +kernel

theorem prime_55823 : Nat.Prime 55823 := by
  apply nodeValid_prime [2, 13, 19, 113] ⟨55823, 5, [(2, 1), (13, 1), (19, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_113
  · decide +kernel

theorem prime_59957 : Nat.Prime 59957 := by
  apply nodeValid_prime [2, 13, 1153] ⟨59957, 2, [(2, 2), (13, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1153
  · decide +kernel

theorem prime_61949 : Nat.Prime 61949 := by
  apply nodeValid_prime [2, 17, 911] ⟨61949, 2, [(2, 2), (17, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_911
  · decide +kernel

theorem prime_66701 : Nat.Prime 66701 := by
  apply nodeValid_prime [2, 5, 23, 29] ⟨66701, 3, [(2, 2), (5, 2), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_71359 : Nat.Prime 71359 := by
  apply nodeValid_prime [2, 3, 7, 1699] ⟨71359, 6, [(2, 1), (3, 1), (7, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1699
  · decide +kernel

theorem prime_72089 : Nat.Prime 72089 := by
  apply nodeValid_prime [2, 9011] ⟨72089, 3, [(2, 3), (9011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9011
  · decide +kernel

theorem prime_75527 : Nat.Prime 75527 := by
  apply nodeValid_prime [2, 11, 3433] ⟨75527, 5, [(2, 1), (11, 1), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3433
  · decide +kernel

theorem prime_81077 : Nat.Prime 81077 := by
  apply nodeValid_prime [2, 20269] ⟨81077, 2, [(2, 2), (20269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20269
  · decide +kernel

theorem prime_90019 : Nat.Prime 90019 := by
  apply nodeValid_prime [2, 3, 1667] ⟨90019, 14, [(2, 1), (3, 3), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1667
  · decide +kernel

theorem prime_106397 : Nat.Prime 106397 := by
  apply nodeValid_prime [2, 67, 397] ⟨106397, 2, [(2, 2), (67, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_397
  · decide +kernel

theorem prime_112913 : Nat.Prime 112913 := by
  apply nodeValid_prime [2, 7057] ⟨112913, 3, [(2, 4), (7057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7057
  · decide +kernel

theorem prime_128563 : Nat.Prime 128563 := by
  apply nodeValid_prime [2, 3, 7, 3061] ⟨128563, 5, [(2, 1), (3, 1), (7, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3061
  · decide +kernel

theorem prime_157177 : Nat.Prime 157177 := by
  apply nodeValid_prime [2, 3, 37, 59] ⟨157177, 13, [(2, 3), (3, 2), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_159013 : Nat.Prime 159013 := by
  apply nodeValid_prime [2, 3, 7, 631] ⟨159013, 6, [(2, 2), (3, 2), (7, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_631
  · decide +kernel

theorem prime_176017 : Nat.Prime 176017 := by
  apply nodeValid_prime [2, 3, 19, 193] ⟨176017, 5, [(2, 4), (3, 1), (19, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_193
  · decide +kernel

theorem prime_199211 : Nat.Prime 199211 := by
  apply nodeValid_prime [2, 5, 11, 1811] ⟨199211, 2, [(2, 1), (5, 1), (11, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1811
  · decide +kernel

theorem prime_199453 : Nat.Prime 199453 := by
  apply nodeValid_prime [2, 3, 11, 1511] ⟨199453, 2, [(2, 2), (3, 1), (11, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1511
  · decide +kernel

theorem prime_201829 : Nat.Prime 201829 := by
  apply nodeValid_prime [2, 3, 11, 139] ⟨201829, 6, [(2, 2), (3, 1), (11, 2), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
  · decide +kernel

theorem prime_205519 : Nat.Prime 205519 := by
  apply nodeValid_prime [2, 3, 34253] ⟨205519, 13, [(2, 1), (3, 1), (34253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34253
  · decide +kernel

theorem prime_210317 : Nat.Prime 210317 := by
  apply nodeValid_prime [2, 52579] ⟨210317, 2, [(2, 2), (52579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_52579
  · decide +kernel

theorem prime_260419 : Nat.Prime 260419 := by
  apply nodeValid_prime [2, 3, 43403] ⟨260419, 10, [(2, 1), (3, 1), (43403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43403
  · decide +kernel

theorem prime_380231 : Nat.Prime 380231 := by
  apply nodeValid_prime [2, 5, 47, 809] ⟨380231, 11, [(2, 1), (5, 1), (47, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_809
  · decide +kernel

theorem prime_389437 : Nat.Prime 389437 := by
  apply nodeValid_prime [2, 3, 17, 23, 83] ⟨389437, 5, [(2, 2), (3, 1), (17, 1), (23, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_83
  · decide +kernel

theorem prime_398423 : Nat.Prime 398423 := by
  apply nodeValid_prime [2, 199211] ⟨398423, 5, [(2, 1), (199211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_199211
  · decide +kernel

theorem prime_404221 : Nat.Prime 404221 := by
  apply nodeValid_prime [2, 3, 5, 6737] ⟨404221, 6, [(2, 2), (3, 1), (5, 1), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6737
  · decide +kernel

theorem prime_480583 : Nat.Prime 480583 := by
  apply nodeValid_prime [2, 3, 26699] ⟨480583, 5, [(2, 1), (3, 2), (26699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26699
  · decide +kernel

theorem prime_519947 : Nat.Prime 519947 := by
  apply nodeValid_prime [2, 7, 37139] ⟨519947, 2, [(2, 1), (7, 1), (37139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37139
  · decide +kernel

theorem prime_540301 : Nat.Prime 540301 := by
  apply nodeValid_prime [2, 3, 5, 1801] ⟨540301, 2, [(2, 2), (3, 1), (5, 2), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1801
  · decide +kernel

theorem prime_558167 : Nat.Prime 558167 := by
  apply nodeValid_prime [2, 7, 39869] ⟨558167, 5, [(2, 1), (7, 1), (39869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_39869
  · decide +kernel

theorem prime_651649 : Nat.Prime 651649 := by
  apply nodeValid_prime [2, 3, 1697] ⟨651649, 14, [(2, 7), (3, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1697
  · decide +kernel

theorem prime_710341 : Nat.Prime 710341 := by
  apply nodeValid_prime [2, 3, 5, 11839] ⟨710341, 2, [(2, 2), (3, 1), (5, 1), (11839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11839
  · decide +kernel

theorem prime_750313 : Nat.Prime 750313 := by
  apply nodeValid_prime [2, 3, 17, 613] ⟨750313, 10, [(2, 3), (3, 2), (17, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_613
  · decide +kernel

theorem prime_796361 : Nat.Prime 796361 := by
  apply nodeValid_prime [2, 5, 43, 463] ⟨796361, 3, [(2, 3), (5, 1), (43, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_463
  · decide +kernel

theorem prime_796847 : Nat.Prime 796847 := by
  apply nodeValid_prime [2, 398423] ⟨796847, 5, [(2, 1), (398423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_398423
  · decide +kernel

theorem prime_817237 : Nat.Prime 817237 := by
  apply nodeValid_prime [2, 3, 7, 23, 47] ⟨817237, 2, [(2, 2), (3, 3), (7, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_923869 : Nat.Prime 923869 := by
  apply nodeValid_prime [2, 3, 11, 2333] ⟨923869, 10, [(2, 2), (3, 2), (11, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2333
  · decide +kernel

theorem prime_1009369 : Nat.Prime 1009369 := by
  apply nodeValid_prime [2, 3, 4673] ⟨1009369, 17, [(2, 3), (3, 3), (4673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4673
  · decide +kernel

theorem prime_1536781 : Nat.Prime 1536781 := by
  apply nodeValid_prime [2, 3, 5, 7, 3659] ⟨1536781, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (3659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3659
  · decide +kernel

theorem prime_1587673 : Nat.Prime 1587673 := by
  apply nodeValid_prime [2, 3, 22051] ⟨1587673, 10, [(2, 3), (3, 2), (22051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22051
  · decide +kernel

theorem prime_1640833 : Nat.Prime 1640833 := by
  apply nodeValid_prime [2, 3, 4273] ⟨1640833, 5, [(2, 7), (3, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4273
  · decide +kernel

theorem prime_1713511 : Nat.Prime 1713511 := by
  apply nodeValid_prime [2, 3, 5, 79, 241] ⟨1713511, 3, [(2, 1), (3, 2), (5, 1), (79, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_241
  · decide +kernel

theorem prime_2529689 : Nat.Prime 2529689 := by
  apply nodeValid_prime [2, 7, 199, 227] ⟨2529689, 3, [(2, 3), (7, 1), (199, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_199
    · exact prime_227
  · decide +kernel

theorem prime_2707321 : Nat.Prime 2707321 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 293] ⟨2707321, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_293
  · decide +kernel

theorem prime_3070831 : Nat.Prime 3070831 := by
  apply nodeValid_prime [2, 3, 5, 7, 2089] ⟨3070831, 3, [(2, 1), (3, 1), (5, 1), (7, 2), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2089
  · decide +kernel

theorem prime_3102773 : Nat.Prime 3102773 := by
  apply nodeValid_prime [2, 17, 103, 443] ⟨3102773, 3, [(2, 2), (17, 1), (103, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
    · exact prime_443
  · decide +kernel

theorem prime_3995713 : Nat.Prime 3995713 := by
  apply nodeValid_prime [2, 3, 7, 991] ⟨3995713, 5, [(2, 6), (3, 2), (7, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_991
  · decide +kernel

theorem prime_4201217 : Nat.Prime 4201217 := by
  apply nodeValid_prime [2, 16411] ⟨4201217, 3, [(2, 8), (16411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16411
  · decide +kernel

theorem prime_4590689 : Nat.Prime 4590689 := by
  apply nodeValid_prime [2, 41, 3499] ⟨4590689, 3, [(2, 5), (41, 1), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_3499
  · decide +kernel

theorem prime_4805831 : Nat.Prime 4805831 := by
  apply nodeValid_prime [2, 5, 480583] ⟨4805831, 7, [(2, 1), (5, 1), (480583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_480583
  · decide +kernel

theorem prime_5356913 : Nat.Prime 5356913 := by
  apply nodeValid_prime [2, 11, 2767] ⟨5356913, 3, [(2, 4), (11, 2), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2767
  · decide +kernel

theorem prime_5750881 : Nat.Prime 5750881 := by
  apply nodeValid_prime [2, 3, 5, 11981] ⟨5750881, 19, [(2, 5), (3, 1), (5, 1), (11981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11981
  · decide +kernel

theorem prime_5896259 : Nat.Prime 5896259 := by
  apply nodeValid_prime [2, 997, 2957] ⟨5896259, 2, [(2, 1), (997, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_997
    · exact prime_2957
  · decide +kernel

theorem prime_5984579 : Nat.Prime 5984579 := by
  apply nodeValid_prime [2, 17, 176017] ⟨5984579, 2, [(2, 1), (17, 1), (176017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_176017
  · decide +kernel

theorem prime_6105089 : Nat.Prime 6105089 := by
  apply nodeValid_prime [2, 11, 271] ⟨6105089, 3, [(2, 11), (11, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_271
  · decide +kernel

theorem prime_6205547 : Nat.Prime 6205547 := by
  apply nodeValid_prime [2, 3102773] ⟨6205547, 2, [(2, 1), (3102773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3102773
  · decide +kernel

theorem prime_6972961 : Nat.Prime 6972961 := by
  apply nodeValid_prime [2, 3, 5, 73, 199] ⟨6972961, 11, [(2, 5), (3, 1), (5, 1), (73, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_199
  · decide +kernel

theorem prime_7033031 : Nat.Prime 7033031 := by
  apply nodeValid_prime [2, 5, 277, 2539] ⟨7033031, 11, [(2, 1), (5, 1), (277, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_277
    · exact prime_2539
  · decide +kernel

theorem prime_9181379 : Nat.Prime 9181379 := by
  apply nodeValid_prime [2, 4590689] ⟨9181379, 2, [(2, 1), (4590689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4590689
  · decide +kernel

theorem prime_9256537 : Nat.Prime 9256537 := by
  apply nodeValid_prime [2, 3, 128563] ⟨9256537, 5, [(2, 3), (3, 2), (128563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_128563
  · decide +kernel

theorem prime_11056471 : Nat.Prime 11056471 := by
  apply nodeValid_prime [2, 3, 5, 41, 89, 101] ⟨11056471, 12, [(2, 1), (3, 1), (5, 1), (41, 1), (89, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_89
    · exact prime_101
  · decide +kernel

theorem prime_11792519 : Nat.Prime 11792519 := by
  apply nodeValid_prime [2, 5896259] ⟨11792519, 7, [(2, 1), (5896259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5896259
  · decide +kernel

theorem prime_12437213 : Nat.Prime 12437213 := by
  apply nodeValid_prime [2, 71, 43793] ⟨12437213, 2, [(2, 2), (71, 1), (43793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_43793
  · decide +kernel

theorem prime_14535007 : Nat.Prime 14535007 := by
  apply nodeValid_prime [2, 3, 37, 233, 281] ⟨14535007, 3, [(2, 1), (3, 1), (37, 1), (233, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_233
    · exact prime_281
  · decide +kernel

theorem prime_17914103 : Nat.Prime 17914103 := by
  apply nodeValid_prime [2, 23, 389437] ⟨17914103, 5, [(2, 1), (23, 1), (389437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_389437
  · decide +kernel

theorem prime_19498537 : Nat.Prime 19498537 := by
  apply nodeValid_prime [2, 3, 90271] ⟨19498537, 5, [(2, 3), (3, 3), (90271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_90271
  · decide +kernel

theorem prime_32619467 : Nat.Prime 32619467 := by
  apply nodeValid_prime [2, 11, 19, 73, 1069] ⟨32619467, 2, [(2, 1), (11, 1), (19, 1), (73, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_73
    · exact prime_1069
  · decide +kernel

theorem prime_36849973 : Nat.Prime 36849973 := by
  apply nodeValid_prime [2, 3, 3070831] ⟨36849973, 5, [(2, 2), (3, 1), (3070831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3070831
  · decide +kernel

theorem prime_62471809 : Nat.Prime 62471809 := by
  apply nodeValid_prime [2, 3, 7, 61, 127] ⟨62471809, 34, [(2, 7), (3, 2), (7, 1), (61, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_127
  · decide +kernel

theorem prime_69143783 : Nat.Prime 69143783 := by
  apply nodeValid_prime [2, 1321, 26171] ⟨69143783, 5, [(2, 1), (1321, 1), (26171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1321
    · exact prime_26171
  · decide +kernel

theorem prime_92140031 : Nat.Prime 92140031 := by
  apply nodeValid_prime [2, 5, 613, 15031] ⟨92140031, 7, [(2, 1), (5, 1), (613, 1), (15031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_613
    · exact prime_15031
  · decide +kernel

theorem prime_128981717 : Nat.Prime 128981717 := by
  apply nodeValid_prime [2, 3313, 9733] ⟨128981717, 2, [(2, 2), (3313, 1), (9733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3313
    · exact prime_9733
  · decide +kernel

theorem prime_142894933 : Nat.Prime 142894933 := by
  apply nodeValid_prime [2, 3, 59, 201829] ⟨142894933, 6, [(2, 2), (3, 1), (59, 1), (201829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_201829
  · decide +kernel

theorem prime_176903537 : Nat.Prime 176903537 := by
  apply nodeValid_prime [2, 11056471] ⟨176903537, 3, [(2, 4), (11056471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11056471
  · decide +kernel

theorem prime_513360671 : Nat.Prime 513360671 := by
  apply nodeValid_prime [2, 5, 127, 404221] ⟨513360671, 13, [(2, 1), (5, 1), (127, 1), (404221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_404221
  · decide +kernel

theorem prime_533858951 : Nat.Prime 533858951 := by
  apply nodeValid_prime [2, 5, 41, 260419] ⟨533858951, 13, [(2, 1), (5, 2), (41, 1), (260419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_260419
  · decide +kernel

theorem prime_778187659 : Nat.Prime 778187659 := by
  apply nodeValid_prime [2, 3, 23, 53, 106397] ⟨778187659, 2, [(2, 1), (3, 1), (23, 1), (53, 1), (106397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53
    · exact prime_106397
  · decide +kernel

theorem prime_793161869 : Nat.Prime 793161869 := by
  apply nodeValid_prime [2, 367, 540301] ⟨793161869, 2, [(2, 2), (367, 1), (540301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_540301
  · decide +kernel

theorem prime_898000669 : Nat.Prime 898000669 := by
  apply nodeValid_prime [2, 3, 923869] ⟨898000669, 2, [(2, 2), (3, 5), (923869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_923869
  · decide +kernel

theorem prime_1026721343 : Nat.Prime 1026721343 := by
  apply nodeValid_prime [2, 513360671] ⟨1026721343, 5, [(2, 1), (513360671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_513360671
  · decide +kernel

theorem prime_1386964939 : Nat.Prime 1386964939 := by
  apply nodeValid_prime [2, 3, 113, 509, 4019] ⟨1386964939, 2, [(2, 1), (3, 1), (113, 1), (509, 1), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_509
    · exact prime_4019
  · decide +kernel

theorem prime_1512245071 : Nat.Prime 1512245071 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 55823] ⟨1512245071, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (43, 1), (55823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_55823
  · decide +kernel

theorem prime_1721635099 : Nat.Prime 1721635099 := by
  apply nodeValid_prime [2, 3, 47, 6105089] ⟨1721635099, 2, [(2, 1), (3, 1), (47, 1), (6105089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_6105089
  · decide +kernel

theorem prime_1723758133 : Nat.Prime 1723758133 := by
  apply nodeValid_prime [2, 3, 683, 210317] ⟨1723758133, 2, [(2, 2), (3, 1), (683, 1), (210317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_210317
  · decide +kernel

theorem prime_1900184171 : Nat.Prime 1900184171 := by
  apply nodeValid_prime [2, 5, 103, 1291, 1429] ⟨1900184171, 2, [(2, 1), (5, 1), (103, 1), (1291, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_1291
    · exact prime_1429
  · decide +kernel

theorem prime_1952051641 : Nat.Prime 1952051641 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 19, 11119] ⟨1952051641, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1), (11119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_11119
  · decide +kernel

theorem prime_2103569191 : Nat.Prime 2103569191 := by
  apply nodeValid_prime [2, 3, 5, 23, 112913] ⟨2103569191, 3, [(2, 1), (3, 4), (5, 1), (23, 1), (112913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_112913
  · decide +kernel

theorem prime_6073049533 : Nat.Prime 6073049533 := by
  apply nodeValid_prime [2, 3, 11, 380231] ⟨6073049533, 5, [(2, 2), (3, 1), (11, 3), (380231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_380231
  · decide +kernel

theorem prime_7768019569 : Nat.Prime 7768019569 := by
  apply nodeValid_prime [2, 3, 113, 751, 1907] ⟨7768019569, 13, [(2, 4), (3, 1), (113, 1), (751, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_751
    · exact prime_1907
  · decide +kernel

theorem prime_8393508103 : Nat.Prime 8393508103 := by
  apply nodeValid_prime [2, 3, 7, 79, 2529689] ⟨8393508103, 3, [(2, 1), (3, 1), (7, 1), (79, 1), (2529689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_2529689
  · decide +kernel

theorem prime_13452444527 : Nat.Prime 13452444527 := by
  apply nodeValid_prime [2, 73, 92140031] ⟨13452444527, 5, [(2, 1), (73, 1), (92140031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_92140031
  · decide +kernel

theorem prime_15493566463 : Nat.Prime 15493566463 := by
  apply nodeValid_prime [2, 3, 11, 137, 1713511] ⟨15493566463, 3, [(2, 1), (3, 1), (11, 1), (137, 1), (1713511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
    · exact prime_1713511
  · decide +kernel

theorem prime_20685097597 : Nat.Prime 20685097597 := by
  apply nodeValid_prime [2, 3, 1723758133] ⟨20685097597, 2, [(2, 2), (3, 1), (1723758133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1723758133
  · decide +kernel

theorem prime_21065731831 : Nat.Prime 21065731831 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 337, 1619] ⟨21065731831, 3, [(2, 1), (3, 3), (5, 1), (11, 1), (13, 1), (337, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_337
    · exact prime_1619
  · decide +kernel

theorem prime_23424619693 : Nat.Prime 23424619693 := by
  apply nodeValid_prime [2, 3, 1952051641] ⟨23424619693, 2, [(2, 2), (3, 1), (1952051641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1952051641
  · decide +kernel

theorem prime_24499305841 : Nat.Prime 24499305841 := by
  apply nodeValid_prime [2, 3, 5, 127, 6329] ⟨24499305841, 17, [(2, 4), (3, 1), (5, 1), (127, 2), (6329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
    · exact prime_6329
  · decide +kernel

theorem prime_33312798499 : Nat.Prime 33312798499 := by
  apply nodeValid_prime [2, 3, 7, 793161869] ⟨33312798499, 3, [(2, 1), (3, 1), (7, 1), (793161869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_793161869
  · decide +kernel

theorem prime_41316174929 : Nat.Prime 41316174929 := by
  apply nodeValid_prime [2, 7, 2347, 157177] ⟨41316174929, 3, [(2, 4), (7, 1), (2347, 1), (157177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2347
    · exact prime_157177
  · decide +kernel

theorem prime_54585865151 : Nat.Prime 54585865151 := by
  apply nodeValid_prime [2, 5, 5659, 192917] ⟨54585865151, 11, [(2, 1), (5, 2), (5659, 1), (192917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5659
    · exact prime_192917
  · decide +kernel

theorem prime_56029511449 : Nat.Prime 56029511449 := by
  apply nodeValid_prime [2, 3, 778187659] ⟨56029511449, 17, [(2, 3), (3, 2), (778187659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_778187659
  · decide +kernel

theorem prime_61974262411 : Nat.Prime 61974262411 := by
  apply nodeValid_prime [2, 3, 5, 1259, 1640833] ⟨61974262411, 3, [(2, 1), (3, 1), (5, 1), (1259, 1), (1640833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1259
    · exact prime_1640833
  · decide +kernel

theorem prime_82632349859 : Nat.Prime 82632349859 := by
  apply nodeValid_prime [2, 41316174929] ⟨82632349859, 2, [(2, 1), (41316174929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41316174929
  · decide +kernel

theorem prime_163328706131 : Nat.Prime 163328706131 := by
  apply nodeValid_prime [2, 5, 22993, 710341] ⟨163328706131, 2, [(2, 1), (5, 1), (22993, 1), (710341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22993
    · exact prime_710341
  · decide +kernel

theorem prime_163972322623 : Nat.Prime 163972322623 := by
  apply nodeValid_prime [2, 3, 31, 41, 796361] ⟨163972322623, 3, [(2, 1), (3, 4), (31, 1), (41, 1), (796361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_41
    · exact prime_796361
  · decide +kernel

theorem prime_493207056323 : Nat.Prime 493207056323 := by
  apply nodeValid_prime [2, 137, 313, 5750881] ⟨493207056323, 2, [(2, 1), (137, 1), (313, 1), (5750881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_313
    · exact prime_5750881
  · decide +kernel

theorem prime_979972233641 : Nat.Prime 979972233641 := by
  apply nodeValid_prime [2, 5, 24499305841] ⟨979972233641, 3, [(2, 3), (5, 1), (24499305841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_24499305841
  · decide +kernel

theorem prime_979972236569 : Nat.Prime 979972236569 := by
  apply nodeValid_prime [2, 13, 1759, 5356913] ⟨979972236569, 3, [(2, 3), (13, 1), (1759, 1), (5356913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1759
    · exact prime_5356913
  · decide +kernel

theorem prime_979972236787 : Nat.Prime 979972236787 := by
  apply nodeValid_prime [2, 3, 163328706131] ⟨979972236787, 11, [(2, 1), (3, 1), (163328706131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163328706131
  · decide +kernel

theorem prime_981258322571 : Nat.Prime 981258322571 := by
  apply nodeValid_prime [2, 5, 43, 157, 14535007] ⟨981258322571, 2, [(2, 1), (5, 1), (43, 1), (157, 1), (14535007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_157
    · exact prime_14535007
  · decide +kernel

theorem prime_981258322591 : Nat.Prime 981258322591 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 23, 73, 71359] ⟨981258322591, 14, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (23, 1), (73, 1), (71359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_73
    · exact prime_71359
  · decide +kernel

theorem prime_981258324923 : Nat.Prime 981258324923 := by
  apply nodeValid_prime [2, 79063, 6205547] ⟨981258324923, 2, [(2, 1), (79063, 1), (6205547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79063
    · exact prime_6205547
  · decide +kernel

theorem prime_982545559309 : Nat.Prime 982545559309 := by
  apply nodeValid_prime [2, 3, 191, 142894933] ⟨982545559309, 2, [(2, 2), (3, 2), (191, 1), (142894933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_142894933
  · decide +kernel

theorem prime_982545572719 : Nat.Prime 982545572719 := by
  apply nodeValid_prime [2, 3, 54585865151] ⟨982545572719, 3, [(2, 1), (3, 2), (54585865151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54585865151
  · decide +kernel

theorem prime_983833935739 : Nat.Prime 983833935739 := by
  apply nodeValid_prime [2, 3, 163972322623] ⟨983833935739, 2, [(2, 1), (3, 1), (163972322623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163972322623
  · decide +kernel

theorem prime_983834024347 : Nat.Prime 983834024347 := by
  apply nodeValid_prime [2, 3, 6073049533] ⟨983834024347, 3, [(2, 1), (3, 4), (6073049533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6073049533
  · decide +kernel

theorem prime_983834027107 : Nat.Prime 983834027107 := by
  apply nodeValid_prime [2, 3, 7, 23424619693] ⟨983834027107, 5, [(2, 1), (3, 1), (7, 1), (23424619693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23424619693
  · decide +kernel

theorem prime_985123450643 : Nat.Prime 985123450643 := by
  apply nodeValid_prime [2, 59, 14957, 558167] ⟨985123450643, 2, [(2, 1), (59, 1), (14957, 1), (558167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_14957
    · exact prime_558167
  · decide +kernel

theorem prime_985123452223 : Nat.Prime 985123452223 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 11792519] ⟨985123452223, 7, [(2, 1), (3, 3), (7, 1), (13, 1), (17, 1), (11792519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_11792519
  · decide +kernel

theorem prime_985123453351 : Nat.Prime 985123453351 := by
  apply nodeValid_prime [2, 3, 5, 8753, 750313] ⟨985123453351, 7, [(2, 1), (3, 1), (5, 2), (8753, 1), (750313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8753
    · exact prime_750313
  · decide +kernel

theorem prime_986414112647 : Nat.Prime 986414112647 := by
  apply nodeValid_prime [2, 493207056323] ⟨986414112647, 5, [(2, 1), (493207056323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_493207056323
  · decide +kernel

theorem prime_986414122313 : Nat.Prime 986414122313 := by
  apply nodeValid_prime [2, 17, 41, 176903537] ⟨986414122313, 3, [(2, 3), (17, 1), (41, 1), (176903537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_176903537
  · decide +kernel

theorem prime_986414124281 : Nat.Prime 986414124281 := by
  apply nodeValid_prime [2, 5, 13, 41, 71, 651649] ⟨986414124281, 3, [(2, 3), (5, 1), (13, 1), (41, 1), (71, 1), (651649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_71
    · exact prime_651649
  · decide +kernel

theorem prime_987705922523 : Nat.Prime 987705922523 := by
  apply nodeValid_prime [2, 11, 19, 2341, 1009369] ⟨987705922523, 5, [(2, 1), (11, 1), (19, 1), (2341, 1), (1009369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_2341
    · exact prime_1009369
  · decide +kernel

theorem prime_987705931687 : Nat.Prime 987705931687 := by
  apply nodeValid_prime [2, 3, 1097, 1667, 90019] ⟨987705931687, 3, [(2, 1), (3, 1), (1097, 1), (1667, 1), (90019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1097
    · exact prime_1667
    · exact prime_90019
  · decide +kernel

theorem prime_987705931967 : Nat.Prime 987705931967 := by
  apply nodeValid_prime [2, 13, 37, 1026721343] ⟨987705931967, 5, [(2, 1), (13, 1), (37, 1), (1026721343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_1026721343
  · decide +kernel

theorem prime_988998869153 : Nat.Prime 988998869153 := by
  apply nodeValid_prime [2, 7, 211, 349, 59957] ⟨988998869153, 3, [(2, 5), (7, 1), (211, 1), (349, 1), (59957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
    · exact prime_349
    · exact prime_59957
  · decide +kernel

theorem prime_988998869869 : Nat.Prime 988998869869 := by
  apply nodeValid_prime [2, 3, 193, 2141, 199453] ⟨988998869869, 7, [(2, 2), (3, 1), (193, 1), (2141, 1), (199453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_2141
    · exact prime_199453
  · decide +kernel

theorem prime_988998885283 : Nat.Prime 988998885283 := by
  apply nodeValid_prime [2, 3, 23, 1019, 7033031] ⟨988998885283, 2, [(2, 1), (3, 1), (23, 1), (1019, 1), (7033031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1019
    · exact prime_7033031
  · decide +kernel

theorem prime_990292965853 : Nat.Prime 990292965853 := by
  apply nodeValid_prime [2, 3, 41, 359, 367, 15277] ⟨990292965853, 2, [(2, 2), (3, 1), (41, 1), (359, 1), (367, 1), (15277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_359
    · exact prime_367
    · exact prime_15277
  · decide +kernel

theorem prime_990292966447 : Nat.Prime 990292966447 := by
  apply nodeValid_prime [2, 3, 7, 17, 1386964939] ⟨990292966447, 5, [(2, 1), (3, 1), (7, 1), (17, 1), (1386964939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_1386964939
  · decide +kernel

theorem prime_990292996883 : Nat.Prime 990292996883 := by
  apply nodeValid_prime [2, 7, 199, 15359, 23143] ⟨990292996883, 2, [(2, 1), (7, 1), (199, 1), (15359, 1), (23143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_199
    · exact prime_15359
    · exact prime_23143
  · decide +kernel

theorem prime_991588198309 : Nat.Prime 991588198309 := by
  apply nodeValid_prime [2, 3, 82632349859] ⟨991588198309, 2, [(2, 2), (3, 1), (82632349859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_82632349859
  · decide +kernel

theorem prime_991588198577 : Nat.Prime 991588198577 := by
  apply nodeValid_prime [2, 61974262411] ⟨991588198577, 3, [(2, 4), (61974262411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61974262411
  · decide +kernel

theorem prime_991588253633 : Nat.Prime 991588253633 := by
  apply nodeValid_prime [2, 15493566463] ⟨991588253633, 3, [(2, 6), (15493566463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15493566463
  · decide +kernel

theorem prime_992884658153 : Nat.Prime 992884658153 := by
  apply nodeValid_prime [2, 59, 2103569191] ⟨992884658153, 3, [(2, 3), (59, 1), (2103569191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2103569191
  · decide +kernel

theorem prime_992884684601 : Nat.Prime 992884684601 := by
  apply nodeValid_prime [2, 5, 1033, 4805831] ⟨992884684601, 3, [(2, 3), (5, 2), (1033, 1), (4805831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1033
    · exact prime_4805831
  · decide +kernel

theorem prime_992884684657 : Nat.Prime 992884684657 := by
  apply nodeValid_prime [2, 3, 20685097597] ⟨992884684657, 7, [(2, 4), (3, 1), (20685097597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20685097597
  · decide +kernel

theorem prime_994182201797 : Nat.Prime 994182201797 := by
  apply nodeValid_prime [2, 7, 17, 349, 5984579] ⟨994182201797, 2, [(2, 2), (7, 1), (17, 1), (349, 1), (5984579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_349
    · exact prime_5984579
  · decide +kernel

theorem prime_994182267097 : Nat.Prime 994182267097 := by
  apply nodeValid_prime [2, 3, 157, 1223, 23971] ⟨994182267097, 10, [(2, 3), (3, 3), (157, 1), (1223, 1), (23971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_1223
    · exact prime_23971
  · decide +kernel

theorem prime_994182267151 : Nat.Prime 994182267151 := by
  apply nodeValid_prime [2, 3, 5, 3697, 22133] ⟨994182267151, 3, [(2, 1), (3, 5), (5, 2), (3697, 1), (22133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3697
    · exact prime_22133
  · decide +kernel

theorem prime_995480891807 : Nat.Prime 995480891807 := by
  apply nodeValid_prime [2, 17, 227, 128981717] ⟨995480891807, 5, [(2, 1), (17, 1), (227, 1), (128981717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_227
    · exact prime_128981717
  · decide +kernel

theorem prime_995480893907 : Nat.Prime 995480893907 := by
  apply nodeValid_prime [2, 15259, 32619467] ⟨995480893907, 2, [(2, 1), (15259, 1), (32619467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15259
    · exact prime_32619467
  · decide +kernel

theorem prime_995480894999 : Nat.Prime 995480894999 := by
  apply nodeValid_prime [2, 37, 13452444527] ⟨995480894999, 13, [(2, 1), (37, 1), (13452444527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_13452444527
  · decide +kernel

theorem prime_996780742591 : Nat.Prime 996780742591 := by
  apply nodeValid_prime [2, 3, 5, 37, 898000669] ⟨996780742591, 3, [(2, 1), (3, 1), (5, 1), (37, 1), (898000669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_898000669
  · decide +kernel

theorem prime_996780745097 : Nat.Prime 996780745097 := by
  apply nodeValid_prime [2, 81077, 1536781] ⟨996780745097, 3, [(2, 3), (81077, 1), (1536781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_81077
    · exact prime_1536781
  · decide +kernel

theorem prime_996780745421 : Nat.Prime 996780745421 := by
  apply nodeValid_prime [2, 5, 11863, 4201217] ⟨996780745421, 2, [(2, 2), (5, 1), (11863, 1), (4201217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11863
    · exact prime_4201217
  · decide +kernel

theorem prime_998081741257 : Nat.Prime 998081741257 := by
  apply nodeValid_prime [2, 3, 151, 337, 817237] ⟨998081741257, 15, [(2, 3), (3, 1), (151, 1), (337, 1), (817237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_337
    · exact prime_817237
  · decide +kernel

theorem prime_998081745697 : Nat.Prime 998081745697 := by
  apply nodeValid_prime [2, 3, 7, 71, 6972961] ⟨998081745697, 5, [(2, 5), (3, 2), (7, 1), (71, 1), (6972961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_6972961
  · decide +kernel

theorem prime_998081746861 : Nat.Prime 998081746861 := by
  apply nodeValid_prime [2, 3, 5, 11, 1512245071] ⟨998081746861, 17, [(2, 2), (3, 1), (5, 1), (11, 1), (1512245071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1512245071
  · decide +kernel

theorem prime_999383889337 : Nat.Prime 999383889337 := by
  apply nodeValid_prime [2, 3, 7, 17, 673, 519947] ⟨999383889337, 10, [(2, 3), (3, 1), (7, 1), (17, 1), (673, 1), (519947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_673
    · exact prime_519947
  · decide +kernel

theorem prime_999383954971 : Nat.Prime 999383954971 := by
  apply nodeValid_prime [2, 3, 5, 33312798499] ⟨999383954971, 12, [(2, 1), (3, 1), (5, 1), (33312798499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_33312798499
  · decide +kernel

theorem prime_999383956273 : Nat.Prime 999383956273 := by
  apply nodeValid_prime [2, 3, 13, 533858951] ⟨999383956273, 7, [(2, 4), (3, 2), (13, 1), (533858951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_533858951
  · decide +kernel

theorem prime_1000687188923 : Nat.Prime 1000687188923 := by
  apply nodeValid_prime [2, 191, 283, 9256537] ⟨1000687188923, 2, [(2, 1), (191, 1), (283, 1), (9256537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_283
    · exact prime_9256537
  · decide +kernel

theorem prime_1000687224269 : Nat.Prime 1000687224269 := by
  apply nodeValid_prime [2, 1249, 10831, 18493] ⟨1000687224269, 2, [(2, 2), (1249, 1), (10831, 1), (18493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1249
    · exact prime_10831
    · exact prime_18493
  · decide +kernel

theorem prime_1000687224499 : Nat.Prime 1000687224499 := by
  apply nodeValid_prime [2, 3, 13, 1151, 1447, 7703] ⟨1000687224499, 2, [(2, 1), (3, 1), (13, 1), (1151, 1), (1447, 1), (7703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1151
    · exact prime_1447
    · exact prime_7703
  · decide +kernel

theorem prime_1001991627619 : Nat.Prime 1001991627619 := by
  apply nodeValid_prime [2, 3, 97, 1721635099] ⟨1001991627619, 2, [(2, 1), (3, 1), (97, 1), (1721635099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1721635099
  · decide +kernel

theorem prime_1001991628133 : Nat.Prime 1001991628133 := by
  apply nodeValid_prime [2, 11, 1831, 12437213] ⟨1001991628133, 2, [(2, 2), (11, 1), (1831, 1), (12437213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1831
    · exact prime_12437213
  · decide +kernel

theorem prime_1001991642697 : Nat.Prime 1001991642697 := by
  apply nodeValid_prime [2, 3, 11, 37, 89, 163, 2357] ⟨1001991642697, 7, [(2, 3), (3, 2), (11, 1), (37, 1), (89, 1), (163, 1), (2357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_89
    · exact prime_163
    · exact prime_2357
  · decide +kernel

theorem prime_1003297242289 : Nat.Prime 1003297242289 := by
  apply nodeValid_prime [2, 3, 11, 1900184171] ⟨1003297242289, 7, [(2, 4), (3, 1), (11, 1), (1900184171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1900184171
  · decide +kernel

theorem prime_1003297252541 : Nat.Prime 1003297252541 := by
  apply nodeValid_prime [2, 5, 11, 73, 62471809] ⟨1003297252541, 7, [(2, 2), (5, 1), (11, 1), (73, 1), (62471809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_73
    · exact prime_62471809
  · decide +kernel

theorem prime_1003297252619 : Nat.Prime 1003297252619 := by
  apply nodeValid_prime [2, 41, 683, 17914103] ⟨1003297252619, 2, [(2, 1), (41, 1), (683, 1), (17914103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_683
    · exact prime_17914103
  · decide +kernel

theorem prime_1004603963927 : Nat.Prime 1004603963927 := by
  apply nodeValid_prime [2, 43, 317, 36849973] ⟨1004603963927, 5, [(2, 1), (43, 1), (317, 1), (36849973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_317
    · exact prime_36849973
  · decide +kernel

theorem prime_1004604000509 : Nat.Prime 1004604000509 := by
  apply nodeValid_prime [2, 179, 6827, 205519] ⟨1004604000509, 2, [(2, 2), (179, 1), (6827, 1), (205519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_6827
    · exact prime_205519
  · decide +kernel

theorem prime_1005911883241 : Nat.Prime 1005911883241 := by
  apply nodeValid_prime [2, 3, 5, 11, 83, 9181379] ⟨1005911883241, 7, [(2, 3), (3, 1), (5, 1), (11, 1), (83, 1), (9181379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_83
    · exact prime_9181379
  · decide +kernel

theorem prime_1005911883751 : Nat.Prime 1005911883751 := by
  apply nodeValid_prime [2, 3, 5, 61, 72089] ⟨1005911883751, 3, [(2, 1), (3, 1), (5, 4), (61, 2), (72089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_72089
  · decide +kernel

theorem prime_1005911911313 : Nat.Prime 1005911911313 := by
  apply nodeValid_prime [2, 7, 11, 12241, 66701] ⟨1005911911313, 3, [(2, 4), (7, 1), (11, 1), (12241, 1), (66701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_12241
    · exact prime_66701
  · decide +kernel

theorem prime_1007220972361 : Nat.Prime 1007220972361 := by
  apply nodeValid_prime [2, 3, 5, 8393508103] ⟨1007220972361, 13, [(2, 3), (3, 1), (5, 1), (8393508103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8393508103
  · decide +kernel

theorem prime_1007220972463 : Nat.Prime 1007220972463 := by
  apply nodeValid_prime [2, 3, 23, 41, 2357, 75527] ⟨1007220972463, 5, [(2, 1), (3, 1), (23, 1), (41, 1), (2357, 1), (75527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_2357
    · exact prime_75527
  · decide +kernel

theorem prime_1007220982777 : Nat.Prime 1007220982777 := by
  apply nodeValid_prime [2, 3, 52667, 796847] ⟨1007220982777, 5, [(2, 3), (3, 1), (52667, 1), (796847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52667
    · exact prime_796847
  · decide +kernel

theorem prime_1008531206083 : Nat.Prime 1008531206083 := by
  apply nodeValid_prime [2, 3, 56029511449] ⟨1008531206083, 5, [(2, 1), (3, 2), (56029511449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56029511449
  · decide +kernel

theorem prime_1008531218839 : Nat.Prime 1008531218839 := by
  apply nodeValid_prime [2, 3, 11, 13, 17, 69143783] ⟨1008531218839, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (17, 1), (69143783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_69143783
  · decide +kernel

theorem prime_1008531218921 : Nat.Prime 1008531218921 := by
  apply nodeValid_prime [2, 5, 67, 139, 2707321] ⟨1008531218921, 3, [(2, 3), (5, 1), (67, 1), (139, 1), (2707321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_139
    · exact prime_2707321
  · decide +kernel

theorem prime_1009842543209 : Nat.Prime 1009842543209 := by
  apply nodeValid_prime [2, 73, 103, 271, 61949] ⟨1009842543209, 3, [(2, 3), (73, 1), (103, 1), (271, 1), (61949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_103
    · exact prime_271
    · exact prime_61949
  · decide +kernel

theorem prime_1009842543971 : Nat.Prime 1009842543971 := by
  apply nodeValid_prime [2, 5, 13, 7768019569] ⟨1009842543971, 2, [(2, 1), (5, 1), (13, 1), (7768019569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_7768019569
  · decide +kernel

theorem prime_1009842586997 : Nat.Prime 1009842586997 := by
  apply nodeValid_prime [2, 159013, 1587673] ⟨1009842586997, 2, [(2, 2), (159013, 1), (1587673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_159013
    · exact prime_1587673
  · decide +kernel

theorem prime_1011155127889 : Nat.Prime 1011155127889 := by
  apply nodeValid_prime [2, 3, 21065731831] ⟨1011155127889, 19, [(2, 4), (3, 1), (21065731831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21065731831
  · decide +kernel

theorem prime_1011155131747 : Nat.Prime 1011155131747 := by
  apply nodeValid_prime [2, 3, 43, 67, 19498537] ⟨1011155131747, 2, [(2, 1), (3, 2), (43, 1), (67, 1), (19498537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_67
    · exact prime_19498537
  · decide +kernel

theorem prime_1011155131781 : Nat.Prime 1011155131781 := by
  apply nodeValid_prime [2, 5, 12653, 3995713] ⟨1011155131781, 2, [(2, 2), (5, 1), (12653, 1), (3995713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12653
    · exact prime_3995713
  · decide +kernel

end Sude.Lucas.Generated
