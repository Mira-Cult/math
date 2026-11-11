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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0114

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_8867 : Nat.Prime 8867 := by
  apply nodeValid_prime [2, 11, 13, 31] ⟨8867, 2, [(2, 1), (11, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_13441 : Nat.Prime 13441 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨13441, 11, [(2, 7), (3, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_14887 : Nat.Prime 14887 := by
  apply nodeValid_prime [2, 3, 827] ⟨14887, 3, [(2, 1), (3, 2), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_827
  · decide +kernel

theorem prime_15413 : Nat.Prime 15413 := by
  apply nodeValid_prime [2, 3853] ⟨15413, 2, [(2, 2), (3853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3853
  · decide +kernel

theorem prime_17749 : Nat.Prime 17749 := by
  apply nodeValid_prime [2, 3, 17, 29] ⟨17749, 2, [(2, 2), (3, 2), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_24229 : Nat.Prime 24229 := by
  apply nodeValid_prime [2, 3, 673] ⟨24229, 2, [(2, 2), (3, 2), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_673
  · decide +kernel

theorem prime_30553 : Nat.Prime 30553 := by
  apply nodeValid_prime [2, 3, 19, 67] ⟨30553, 5, [(2, 3), (3, 1), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_37423 : Nat.Prime 37423 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨37423, 6, [(2, 1), (3, 5), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_38977 : Nat.Prime 38977 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨38977, 5, [(2, 6), (3, 1), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_44293 : Nat.Prime 44293 := by
  apply nodeValid_prime [2, 3, 3691] ⟨44293, 2, [(2, 2), (3, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3691
  · decide +kernel

theorem prime_46061 : Nat.Prime 46061 := by
  apply nodeValid_prime [2, 5, 7, 47] ⟨46061, 2, [(2, 2), (5, 1), (7, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_48847 : Nat.Prime 48847 := by
  apply nodeValid_prime [2, 3, 7, 1163] ⟨48847, 3, [(2, 1), (3, 1), (7, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1163
  · decide +kernel

theorem prime_49069 : Nat.Prime 49069 := by
  apply nodeValid_prime [2, 3, 29, 47] ⟨49069, 2, [(2, 2), (3, 2), (29, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_47
  · decide +kernel

theorem prime_57041 : Nat.Prime 57041 := by
  apply nodeValid_prime [2, 5, 23, 31] ⟨57041, 11, [(2, 4), (5, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_59141 : Nat.Prime 59141 := by
  apply nodeValid_prime [2, 5, 2957] ⟨59141, 3, [(2, 2), (5, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2957
  · decide +kernel

theorem prime_70001 : Nat.Prime 70001 := by
  apply nodeValid_prime [2, 5, 7] ⟨70001, 3, [(2, 4), (5, 4), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_91249 : Nat.Prime 91249 := by
  apply nodeValid_prime [2, 3, 1901] ⟨91249, 17, [(2, 4), (3, 1), (1901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1901
  · decide +kernel

theorem prime_96851 : Nat.Prime 96851 := by
  apply nodeValid_prime [2, 5, 13, 149] ⟨96851, 2, [(2, 1), (5, 2), (13, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_149
  · decide +kernel

theorem prime_100549 : Nat.Prime 100549 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨100549, 2, [(2, 2), (3, 3), (7, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_103643 : Nat.Prime 103643 := by
  apply nodeValid_prime [2, 7, 11, 673] ⟨103643, 2, [(2, 1), (7, 1), (11, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_673
  · decide +kernel

theorem prime_107903 : Nat.Prime 107903 := by
  apply nodeValid_prime [2, 53951] ⟨107903, 5, [(2, 1), (53951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53951
  · decide +kernel

theorem prime_114083 : Nat.Prime 114083 := by
  apply nodeValid_prime [2, 57041] ⟨114083, 2, [(2, 1), (57041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57041
  · decide +kernel

theorem prime_124543 : Nat.Prime 124543 := by
  apply nodeValid_prime [2, 3, 11, 17, 37] ⟨124543, 5, [(2, 1), (3, 2), (11, 1), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_135469 : Nat.Prime 135469 := by
  apply nodeValid_prime [2, 3, 53, 71] ⟨135469, 2, [(2, 2), (3, 2), (53, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_71
  · decide +kernel

theorem prime_149803 : Nat.Prime 149803 := by
  apply nodeValid_prime [2, 3, 24967] ⟨149803, 2, [(2, 1), (3, 1), (24967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24967
  · decide +kernel

theorem prime_153001 : Nat.Prime 153001 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨153001, 11, [(2, 3), (3, 2), (5, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_164267 : Nat.Prime 164267 := by
  apply nodeValid_prime [2, 23, 3571] ⟨164267, 2, [(2, 1), (23, 1), (3571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3571
  · decide +kernel

theorem prime_177173 : Nat.Prime 177173 := by
  apply nodeValid_prime [2, 44293] ⟨177173, 2, [(2, 2), (44293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44293
  · decide +kernel

theorem prime_192583 : Nat.Prime 192583 := by
  apply nodeValid_prime [2, 3, 13, 823] ⟨192583, 3, [(2, 1), (3, 2), (13, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_823
  · decide +kernel

theorem prime_193703 : Nat.Prime 193703 := by
  apply nodeValid_prime [2, 96851] ⟨193703, 5, [(2, 1), (96851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_96851
  · decide +kernel

theorem prime_195389 : Nat.Prime 195389 := by
  apply nodeValid_prime [2, 48847] ⟨195389, 2, [(2, 2), (48847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48847
  · decide +kernel

theorem prime_199487 : Nat.Prime 199487 := by
  apply nodeValid_prime [2, 7, 14249] ⟨199487, 5, [(2, 1), (7, 1), (14249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_14249
  · decide +kernel

theorem prime_202949 : Nat.Prime 202949 := by
  apply nodeValid_prime [2, 113, 449] ⟨202949, 2, [(2, 2), (113, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_449
  · decide +kernel

theorem prime_203857 : Nat.Prime 203857 := by
  apply nodeValid_prime [2, 3, 31, 137] ⟨203857, 5, [(2, 4), (3, 1), (31, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_137
  · decide +kernel

theorem prime_207199 : Nat.Prime 207199 := by
  apply nodeValid_prime [2, 3, 1279] ⟨207199, 3, [(2, 1), (3, 4), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
  · decide +kernel

theorem prime_230471 : Nat.Prime 230471 := by
  apply nodeValid_prime [2, 5, 19, 1213] ⟨230471, 19, [(2, 1), (5, 1), (19, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1213
  · decide +kernel

theorem prime_231223 : Nat.Prime 231223 := by
  apply nodeValid_prime [2, 3, 89, 433] ⟨231223, 3, [(2, 1), (3, 1), (89, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_433
  · decide +kernel

theorem prime_232567 : Nat.Prime 232567 := by
  apply nodeValid_prime [2, 3, 83, 467] ⟨232567, 5, [(2, 1), (3, 1), (83, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_467
  · decide +kernel

theorem prime_261619 : Nat.Prime 261619 := by
  apply nodeValid_prime [2, 3, 7, 6229] ⟨261619, 3, [(2, 1), (3, 1), (7, 1), (6229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6229
  · decide +kernel

theorem prime_271177 : Nat.Prime 271177 := by
  apply nodeValid_prime [2, 3, 11299] ⟨271177, 5, [(2, 3), (3, 1), (11299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11299
  · decide +kernel

theorem prime_297233 : Nat.Prime 297233 := by
  apply nodeValid_prime [2, 13, 1429] ⟨297233, 3, [(2, 4), (13, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1429
  · decide +kernel

theorem prime_314159 : Nat.Prime 314159 := by
  apply nodeValid_prime [2, 13, 43, 281] ⟨314159, 23, [(2, 1), (13, 1), (43, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_281
  · decide +kernel

theorem prime_314453 : Nat.Prime 314453 := by
  apply nodeValid_prime [2, 127, 619] ⟨314453, 2, [(2, 2), (127, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_619
  · decide +kernel

theorem prime_364997 : Nat.Prime 364997 := by
  apply nodeValid_prime [2, 91249] ⟨364997, 2, [(2, 2), (91249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_91249
  · decide +kernel

theorem prime_402197 : Nat.Prime 402197 := by
  apply nodeValid_prime [2, 100549] ⟨402197, 2, [(2, 2), (100549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_100549
  · decide +kernel

theorem prime_416501 : Nat.Prime 416501 := by
  apply nodeValid_prime [2, 5, 7, 17] ⟨416501, 2, [(2, 2), (5, 3), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_430453 : Nat.Prime 430453 := by
  apply nodeValid_prime [2, 3, 11, 1087] ⟨430453, 5, [(2, 2), (3, 2), (11, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1087
  · decide +kernel

theorem prime_465433 : Nat.Prime 465433 := by
  apply nodeValid_prime [2, 3, 11, 41, 43] ⟨465433, 7, [(2, 3), (3, 1), (11, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_491171 : Nat.Prime 491171 := by
  apply nodeValid_prime [2, 5, 49117] ⟨491171, 2, [(2, 1), (5, 1), (49117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49117
  · decide +kernel

theorem prime_500567 : Nat.Prime 500567 := by
  apply nodeValid_prime [2, 11, 61, 373] ⟨500567, 5, [(2, 1), (11, 1), (61, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_373
  · decide +kernel

theorem prime_514093 : Nat.Prime 514093 := by
  apply nodeValid_prime [2, 3, 42841] ⟨514093, 6, [(2, 2), (3, 1), (42841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42841
  · decide +kernel

theorem prime_657841 : Nat.Prime 657841 := by
  apply nodeValid_prime [2, 3, 5, 2741] ⟨657841, 11, [(2, 4), (3, 1), (5, 1), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2741
  · decide +kernel

theorem prime_709693 : Nat.Prime 709693 := by
  apply nodeValid_prime [2, 3, 59141] ⟨709693, 5, [(2, 2), (3, 1), (59141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59141
  · decide +kernel

theorem prime_733273 : Nat.Prime 733273 := by
  apply nodeValid_prime [2, 3, 30553] ⟨733273, 5, [(2, 3), (3, 1), (30553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30553
  · decide +kernel

theorem prime_777677 : Nat.Prime 777677 := by
  apply nodeValid_prime [2, 23, 79, 107] ⟨777677, 2, [(2, 2), (23, 1), (79, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_79
    · exact prime_107
  · decide +kernel

theorem prime_982343 : Nat.Prime 982343 := by
  apply nodeValid_prime [2, 491171] ⟨982343, 5, [(2, 1), (491171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_491171
  · decide +kernel

theorem prime_1181963 : Nat.Prime 1181963 := by
  apply nodeValid_prime [2, 293, 2017] ⟨1181963, 2, [(2, 1), (293, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_2017
  · decide +kernel

theorem prime_1286819 : Nat.Prime 1286819 := by
  apply nodeValid_prime [2, 13, 43, 1151] ⟨1286819, 2, [(2, 1), (13, 1), (43, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_1151
  · decide +kernel

theorem prime_1752013 : Nat.Prime 1752013 := by
  apply nodeValid_prime [2, 3, 41, 1187] ⟨1752013, 2, [(2, 2), (3, 2), (41, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1187
  · decide +kernel

theorem prime_1765579 : Nat.Prime 1765579 := by
  apply nodeValid_prime [2, 3, 29, 73, 139] ⟨1765579, 3, [(2, 1), (3, 1), (29, 1), (73, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_73
    · exact prime_139
  · decide +kernel

theorem prime_1821377 : Nat.Prime 1821377 := by
  apply nodeValid_prime [2, 149, 191] ⟨1821377, 3, [(2, 6), (149, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_191
  · decide +kernel

theorem prime_1886347 : Nat.Prime 1886347 := by
  apply nodeValid_prime [2, 3, 7, 11, 1361] ⟨1886347, 3, [(2, 1), (3, 2), (7, 1), (11, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1361
  · decide +kernel

theorem prime_2154413 : Nat.Prime 2154413 := by
  apply nodeValid_prime [2, 13, 3187] ⟨2154413, 2, [(2, 2), (13, 2), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3187
  · decide +kernel

theorem prime_2283013 : Nat.Prime 2283013 := by
  apply nodeValid_prime [2, 3, 21139] ⟨2283013, 2, [(2, 2), (3, 3), (21139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21139
  · decide +kernel

theorem prime_2363927 : Nat.Prime 2363927 := by
  apply nodeValid_prime [2, 1181963] ⟨2363927, 5, [(2, 1), (1181963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1181963
  · decide +kernel

theorem prime_2372467 : Nat.Prime 2372467 := by
  apply nodeValid_prime [2, 3, 47, 179] ⟨2372467, 2, [(2, 1), (3, 1), (47, 2), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_179
  · decide +kernel

theorem prime_2414177 : Nat.Prime 2414177 := by
  apply nodeValid_prime [2, 37, 2039] ⟨2414177, 3, [(2, 5), (37, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2039
  · decide +kernel

theorem prime_2763661 : Nat.Prime 2763661 := by
  apply nodeValid_prime [2, 3, 5, 46061] ⟨2763661, 6, [(2, 2), (3, 1), (5, 1), (46061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46061
  · decide +kernel

theorem prime_3822017 : Nat.Prime 3822017 := by
  apply nodeValid_prime [2, 11, 61, 89] ⟨3822017, 3, [(2, 6), (11, 1), (61, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_89
  · decide +kernel

theorem prime_4161263 : Nat.Prime 4161263 := by
  apply nodeValid_prime [2, 7, 297233] ⟨4161263, 5, [(2, 1), (7, 1), (297233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_297233
  · decide +kernel

theorem prime_4287457 : Nat.Prime 4287457 := by
  apply nodeValid_prime [2, 3, 14887] ⟨4287457, 5, [(2, 5), (3, 2), (14887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14887
  · decide +kernel

theorem prime_6709253 : Nat.Prime 6709253 := by
  apply nodeValid_prime [2, 11, 139, 1097] ⟨6709253, 2, [(2, 2), (11, 1), (139, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_139
    · exact prime_1097
  · decide +kernel

theorem prime_7894093 : Nat.Prime 7894093 := by
  apply nodeValid_prime [2, 3, 657841] ⟨7894093, 2, [(2, 2), (3, 1), (657841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_657841
  · decide +kernel

theorem prime_8451089 : Nat.Prime 8451089 := by
  apply nodeValid_prime [2, 127, 4159] ⟨8451089, 3, [(2, 4), (127, 1), (4159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_4159
  · decide +kernel

theorem prime_15540223 : Nat.Prime 15540223 := by
  apply nodeValid_prime [2, 3, 37, 70001] ⟨15540223, 3, [(2, 1), (3, 1), (37, 1), (70001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_70001
  · decide +kernel

theorem prime_17520131 : Nat.Prime 17520131 := by
  apply nodeValid_prime [2, 5, 1752013] ⟨17520131, 6, [(2, 1), (5, 1), (1752013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1752013
  · decide +kernel

theorem prime_21675041 : Nat.Prime 21675041 := by
  apply nodeValid_prime [2, 5, 135469] ⟨21675041, 3, [(2, 5), (5, 1), (135469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_135469
  · decide +kernel

theorem prime_25476391 : Nat.Prime 25476391 := by
  apply nodeValid_prime [2, 3, 5, 157, 601] ⟨25476391, 15, [(2, 1), (3, 3), (5, 1), (157, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
    · exact prime_601
  · decide +kernel

theorem prime_27195167 : Nat.Prime 27195167 := by
  apply nodeValid_prime [2, 67, 202949] ⟨27195167, 5, [(2, 1), (67, 1), (202949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_202949
  · decide +kernel

theorem prime_28387721 : Nat.Prime 28387721 := by
  apply nodeValid_prime [2, 5, 709693] ⟨28387721, 3, [(2, 3), (5, 1), (709693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_709693
  · decide +kernel

theorem prime_31499731 : Nat.Prime 31499731 := by
  apply nodeValid_prime [2, 3, 5, 107, 3271] ⟨31499731, 2, [(2, 1), (3, 2), (5, 1), (107, 1), (3271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
    · exact prime_3271
  · decide +kernel

theorem prime_31576373 : Nat.Prime 31576373 := by
  apply nodeValid_prime [2, 7894093] ⟨31576373, 2, [(2, 2), (7894093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7894093
  · decide +kernel

theorem prime_31623199 : Nat.Prime 31623199 := by
  apply nodeValid_prime [2, 3, 47, 112139] ⟨31623199, 3, [(2, 1), (3, 1), (47, 1), (112139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_112139
  · decide +kernel

theorem prime_31804999 : Nat.Prime 31804999 := by
  apply nodeValid_prime [2, 3, 23, 230471] ⟨31804999, 6, [(2, 1), (3, 1), (23, 1), (230471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_230471
  · decide +kernel

theorem prime_32320021 : Nat.Prime 32320021 := by
  apply nodeValid_prime [2, 3, 5, 47, 73, 157] ⟨32320021, 6, [(2, 2), (3, 1), (5, 1), (47, 1), (73, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_73
    · exact prime_157
  · decide +kernel

theorem prime_41723819 : Nat.Prime 41723819 := by
  apply nodeValid_prime [2, 127, 164267] ⟨41723819, 2, [(2, 1), (127, 1), (164267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_164267
  · decide +kernel

theorem prime_41854199 : Nat.Prime 41854199 := by
  apply nodeValid_prime [2, 101, 207199] ⟨41854199, 7, [(2, 1), (101, 1), (207199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_207199
  · decide +kernel

theorem prime_42550687 : Nat.Prime 42550687 := by
  apply nodeValid_prime [2, 3, 2363927] ⟨42550687, 3, [(2, 1), (3, 2), (2363927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2363927
  · decide +kernel

theorem prime_48081521 : Nat.Prime 48081521 := by
  apply nodeValid_prime [2, 5, 41, 107, 137] ⟨48081521, 3, [(2, 4), (5, 1), (41, 1), (107, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_107
    · exact prime_137
  · decide +kernel

theorem prime_56775443 : Nat.Prime 56775443 := by
  apply nodeValid_prime [2, 28387721] ⟨56775443, 2, [(2, 1), (28387721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28387721
  · decide +kernel

theorem prime_94935553 : Nat.Prime 94935553 := by
  apply nodeValid_prime [2, 3, 19, 3253] ⟨94935553, 5, [(2, 9), (3, 1), (19, 1), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3253
  · decide +kernel

theorem prime_117132679 : Nat.Prime 117132679 := by
  apply nodeValid_prime [2, 3, 13, 500567] ⟨117132679, 3, [(2, 1), (3, 2), (13, 1), (500567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_500567
  · decide +kernel

theorem prime_130050247 : Nat.Prime 130050247 := by
  apply nodeValid_prime [2, 3, 21675041] ⟨130050247, 3, [(2, 1), (3, 1), (21675041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21675041
  · decide +kernel

theorem prime_288489127 : Nat.Prime 288489127 := by
  apply nodeValid_prime [2, 3, 48081521] ⟨288489127, 3, [(2, 1), (3, 1), (48081521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48081521
  · decide +kernel

theorem prime_340652659 : Nat.Prime 340652659 := by
  apply nodeValid_prime [2, 3, 56775443] ⟨340652659, 2, [(2, 1), (3, 1), (56775443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56775443
  · decide +kernel

theorem prime_350259121 : Nat.Prime 350259121 := by
  apply nodeValid_prime [2, 3, 5, 167, 971] ⟨350259121, 23, [(2, 4), (3, 3), (5, 1), (167, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_971
  · decide +kernel

theorem prime_350388743 : Nat.Prime 350388743 := by
  apply nodeValid_prime [2, 11, 37, 430453] ⟨350388743, 5, [(2, 1), (11, 1), (37, 1), (430453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_430453
  · decide +kernel

theorem prime_560426833 : Nat.Prime 560426833 := by
  apply nodeValid_prime [2, 3, 7, 23, 1051] ⟨560426833, 5, [(2, 4), (3, 2), (7, 1), (23, 2), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_1051
  · decide +kernel

theorem prime_752491469 : Nat.Prime 752491469 := by
  apply nodeValid_prime [2, 17, 97, 114083] ⟨752491469, 2, [(2, 2), (17, 1), (97, 1), (114083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97
    · exact prime_114083
  · decide +kernel

theorem prime_878844199 : Nat.Prime 878844199 := by
  apply nodeValid_prime [2, 3, 53, 2763661] ⟨878844199, 3, [(2, 1), (3, 1), (53, 1), (2763661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_2763661
  · decide +kernel

theorem prime_972171341 : Nat.Prime 972171341 := by
  apply nodeValid_prime [2, 5, 7, 67, 103643] ⟨972171341, 10, [(2, 2), (5, 1), (7, 1), (67, 1), (103643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_67
    · exact prime_103643
  · decide +kernel

theorem prime_1110795293 : Nat.Prime 1110795293 := by
  apply nodeValid_prime [2, 1201, 231223] ⟨1110795293, 2, [(2, 2), (1201, 1), (231223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1201
    · exact prime_231223
  · decide +kernel

theorem prime_1386462173 : Nat.Prime 1386462173 := by
  apply nodeValid_prime [2, 23, 139, 181, 599] ⟨1386462173, 2, [(2, 2), (23, 1), (139, 1), (181, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_139
    · exact prime_181
    · exact prime_599
  · decide +kernel

theorem prime_1504982939 : Nat.Prime 1504982939 := by
  apply nodeValid_prime [2, 752491469] ⟨1504982939, 2, [(2, 1), (752491469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_752491469
  · decide +kernel

theorem prime_1813236013 : Nat.Prime 1813236013 := by
  apply nodeValid_prime [2, 3, 7, 1823, 3947] ⟨1813236013, 11, [(2, 2), (3, 2), (7, 1), (1823, 1), (3947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1823
    · exact prime_3947
  · decide +kernel

theorem prime_2666643913 : Nat.Prime 2666643913 := by
  apply nodeValid_prime [2, 3, 3319, 11159] ⟨2666643913, 10, [(2, 3), (3, 2), (3319, 1), (11159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3319
    · exact prime_11159
  · decide +kernel

theorem prime_2772924347 : Nat.Prime 2772924347 := by
  apply nodeValid_prime [2, 1386462173] ⟨2772924347, 2, [(2, 1), (1386462173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1386462173
  · decide +kernel

theorem prime_2786833391 : Nat.Prime 2786833391 := by
  apply nodeValid_prime [2, 5, 11, 127, 199487] ⟨2786833391, 11, [(2, 1), (5, 1), (11, 1), (127, 1), (199487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_127
    · exact prime_199487
  · decide +kernel

theorem prime_3233852213 : Nat.Prime 3233852213 := by
  apply nodeValid_prime [2, 19, 42550687] ⟨3233852213, 2, [(2, 2), (19, 1), (42550687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_42550687
  · decide +kernel

theorem prime_3706452419 : Nat.Prime 3706452419 := by
  apply nodeValid_prime [2, 9623, 192583] ⟨3706452419, 2, [(2, 1), (9623, 1), (192583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9623
    · exact prime_192583
  · decide +kernel

theorem prime_4374955913 : Nat.Prime 4374955913 := by
  apply nodeValid_prime [2, 89, 113, 54377] ⟨4374955913, 3, [(2, 3), (89, 1), (113, 1), (54377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_113
    · exact prime_54377
  · decide +kernel

theorem prime_6682295891 : Nat.Prime 6682295891 := by
  apply nodeValid_prime [2, 5, 43, 15540223] ⟨6682295891, 2, [(2, 1), (5, 1), (43, 1), (15540223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_15540223
  · decide +kernel

theorem prime_7412904839 : Nat.Prime 7412904839 := by
  apply nodeValid_prime [2, 3706452419] ⟨7412904839, 7, [(2, 1), (3706452419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3706452419
  · decide +kernel

theorem prime_12642312707 : Nat.Prime 12642312707 := by
  apply nodeValid_prime [2, 53, 3187, 37423] ⟨12642312707, 2, [(2, 1), (53, 1), (3187, 1), (37423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_3187
    · exact prime_37423
  · decide +kernel

theorem prime_15686290723 : Nat.Prime 15686290723 := by
  apply nodeValid_prime [2, 3, 24229, 107903] ⟨15686290723, 2, [(2, 1), (3, 1), (24229, 1), (107903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24229
    · exact prime_107903
  · decide +kernel

theorem prime_17513850437 : Nat.Prime 17513850437 := by
  apply nodeValid_prime [2, 139, 31499731] ⟨17513850437, 2, [(2, 2), (139, 1), (31499731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_31499731
  · decide +kernel

theorem prime_18887787647 : Nat.Prime 18887787647 := by
  apply nodeValid_prime [2, 7, 13, 59, 4259] ⟨18887787647, 7, [(2, 1), (7, 2), (13, 1), (59, 2), (4259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_59
    · exact prime_4259
  · decide +kernel

theorem prime_26630214529 : Nat.Prime 26630214529 := by
  apply nodeValid_prime [2, 3, 149, 465433] ⟨26630214529, 17, [(2, 7), (3, 1), (149, 1), (465433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_465433
  · decide +kernel

theorem prime_27177374803 : Nat.Prime 27177374803 := by
  apply nodeValid_prime [2, 3, 17, 181, 401, 3671] ⟨27177374803, 2, [(2, 1), (3, 1), (17, 1), (181, 1), (401, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_181
    · exact prime_401
    · exact prime_3671
  · decide +kernel

theorem prime_35832972251 : Nat.Prime 35832972251 := by
  apply nodeValid_prime [2, 5, 71, 601, 3359] ⟨35832972251, 2, [(2, 1), (5, 3), (71, 1), (601, 1), (3359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_601
    · exact prime_3359
  · decide +kernel

theorem prime_59932515901 : Nat.Prime 59932515901 := by
  apply nodeValid_prime [2, 3, 5, 859, 232567] ⟨59932515901, 2, [(2, 2), (3, 1), (5, 2), (859, 1), (232567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_859
    · exact prime_232567
  · decide +kernel

theorem prime_62657464981 : Nat.Prime 62657464981 := by
  apply nodeValid_prime [2, 3, 5, 11, 94935553] ⟨62657464981, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (94935553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_94935553
  · decide +kernel

theorem prime_69068360831 : Nat.Prime 69068360831 := by
  apply nodeValid_prime [2, 5, 7, 23, 103, 416501] ⟨69068360831, 13, [(2, 1), (5, 1), (7, 1), (23, 1), (103, 1), (416501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_103
    · exact prime_416501
  · decide +kernel

theorem prime_160861049929 : Nat.Prime 160861049929 := by
  apply nodeValid_prime [2, 3, 37, 6709253] ⟨160861049929, 7, [(2, 3), (3, 4), (37, 1), (6709253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_6709253
  · decide +kernel

theorem prime_205225205503 : Nat.Prime 205225205503 := by
  apply nodeValid_prime [2, 3, 34819, 982343] ⟨205225205503, 5, [(2, 1), (3, 1), (34819, 1), (982343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34819
    · exact prime_982343
  · decide +kernel

theorem prime_206708905483 : Nat.Prime 206708905483 := by
  apply nodeValid_prime [2, 3, 19, 1813236013] ⟨206708905483, 2, [(2, 1), (3, 1), (19, 1), (1813236013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1813236013
  · decide +kernel

theorem prime_286046528371 : Nat.Prime 286046528371 := by
  apply nodeValid_prime [2, 3, 5, 151, 157, 402197] ⟨286046528371, 2, [(2, 1), (3, 1), (5, 1), (151, 1), (157, 1), (402197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_157
    · exact prime_402197
  · decide +kernel

theorem prime_381091165673 : Nat.Prime 381091165673 := by
  apply nodeValid_prime [2, 7, 972171341] ⟨381091165673, 5, [(2, 3), (7, 2), (972171341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_972171341
  · decide +kernel

theorem prime_571180686221 : Nat.Prime 571180686221 := by
  apply nodeValid_prime [2, 5, 19, 59, 25476391] ⟨571180686221, 2, [(2, 2), (5, 1), (19, 1), (59, 1), (25476391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_59
    · exact prime_25476391
  · decide +kernel

theorem prime_573006417749 : Nat.Prime 573006417749 := by
  apply nodeValid_prime [2, 163, 878844199] ⟨573006417749, 2, [(2, 2), (163, 1), (878844199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_878844199
  · decide +kernel

theorem prime_1141449741727 : Nat.Prime 1141449741727 := by
  apply nodeValid_prime [2, 3, 7, 27177374803] ⟨1141449741727, 10, [(2, 1), (3, 1), (7, 1), (27177374803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_27177374803
  · decide +kernel

theorem prime_1146012823573 : Nat.Prime 1146012823573 := by
  apply nodeValid_prime [2, 3, 37, 3319, 777677] ⟨1146012823573, 5, [(2, 2), (3, 1), (37, 1), (3319, 1), (777677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_3319
    · exact prime_777677
  · decide +kernel

theorem prime_2261097199019 : Nat.Prime 2261097199019 := by
  apply nodeValid_prime [2, 7, 314159, 514093] ⟨2261097199019, 6, [(2, 1), (7, 1), (314159, 1), (514093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_314159
    · exact prime_514093
  · decide +kernel

theorem prime_2262908713493 : Nat.Prime 2262908713493 := by
  apply nodeValid_prime [2, 7, 29, 2786833391] ⟨2262908713493, 2, [(2, 2), (7, 1), (29, 1), (2786833391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_2786833391
  · decide +kernel

theorem prime_2270164292801 : Nat.Prime 2270164292801 := by
  apply nodeValid_prime [2, 5, 19, 41, 1821377] ⟨2270164292801, 3, [(2, 6), (5, 2), (19, 1), (41, 1), (1821377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_1821377
  · decide +kernel

theorem prime_2270164293461 : Nat.Prime 2270164293461 := by
  apply nodeValid_prime [2, 5, 7, 11959, 193703] ⟨2270164293461, 2, [(2, 2), (5, 1), (7, 2), (11959, 1), (193703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11959
    · exact prime_193703
  · decide +kernel

theorem prime_4496889021733 : Nat.Prime 4496889021733 := by
  apply nodeValid_prime [2, 3, 83, 1504982939] ⟨4496889021733, 6, [(2, 2), (3, 2), (83, 1), (1504982939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_1504982939
  · decide +kernel

theorem prime_4496889022159 : Nat.Prime 4496889022159 := by
  apply nodeValid_prime [2, 3, 13, 2351, 1886347] ⟨4496889022159, 15, [(2, 1), (3, 1), (13, 2), (2351, 1), (1886347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2351
    · exact prime_1886347
  · decide +kernel

theorem prime_4496889127663 : Nat.Prime 4496889127663 := by
  apply nodeValid_prime [2, 3, 23, 31, 350388743] ⟨4496889127663, 3, [(2, 1), (3, 2), (23, 1), (31, 1), (350388743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_31
    · exact prime_350388743
  · decide +kernel

theorem prime_4500498284209 : Nat.Prime 4500498284209 := by
  apply nodeValid_prime [2, 3, 967, 32320021] ⟨4500498284209, 13, [(2, 4), (3, 2), (967, 1), (32320021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
    · exact prime_32320021
  · decide +kernel

theorem prime_4500498310073 : Nat.Prime 4500498310073 := by
  apply nodeValid_prime [2, 13441, 41854199] ⟨4500498310073, 3, [(2, 3), (13441, 1), (41854199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13441
    · exact prime_41854199
  · decide +kernel

theorem prime_4500498312407 : Nat.Prime 4500498312407 := by
  apply nodeValid_prime [2, 6343, 15413, 23017] ⟨4500498312407, 5, [(2, 1), (6343, 1), (15413, 1), (23017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_6343
    · exact prime_15413
    · exact prime_23017
  · decide +kernel

theorem prime_4504109398013 : Nat.Prime 4504109398013 := by
  apply nodeValid_prime [2, 7, 160861049929] ⟨4504109398013, 2, [(2, 2), (7, 1), (160861049929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_160861049929
  · decide +kernel

theorem prime_4504109457299 : Nat.Prime 4504109457299 := by
  apply nodeValid_prime [2, 11, 601, 340652659] ⟨4504109457299, 6, [(2, 1), (11, 1), (601, 1), (340652659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_601
    · exact prime_340652659
  · decide +kernel

theorem prime_4504109458571 : Nat.Prime 4504109458571 := by
  apply nodeValid_prime [2, 5, 17, 6367, 4161263] ⟨4504109458571, 2, [(2, 1), (5, 1), (17, 1), (6367, 1), (4161263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_6367
    · exact prime_4161263
  · decide +kernel

theorem prime_4507722475313 : Nat.Prime 4507722475313 := by
  apply nodeValid_prime [2, 7, 191, 11239, 18749] ⟨4507722475313, 3, [(2, 4), (7, 1), (191, 1), (11239, 1), (18749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_191
    · exact prime_11239
    · exact prime_18749
  · decide +kernel

theorem prime_4507722508271 : Nat.Prime 4507722508271 := by
  apply nodeValid_prime [2, 5, 14173, 31804999] ⟨4507722508271, 11, [(2, 1), (5, 1), (14173, 1), (31804999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14173
    · exact prime_31804999
  · decide +kernel

theorem prime_4507722510121 : Nat.Prime 4507722510121 := by
  apply nodeValid_prime [2, 3, 5, 167, 2281, 10957] ⟨4507722510121, 7, [(2, 3), (3, 3), (5, 1), (167, 1), (2281, 1), (10957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_2281
    · exact prime_10957
  · decide +kernel

theorem prime_4511337478481 : Nat.Prime 4511337478481 := by
  apply nodeValid_prime [2, 5, 7, 23, 350259121] ⟨4511337478481, 6, [(2, 4), (5, 1), (7, 1), (23, 1), (350259121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_350259121
  · decide +kernel

theorem prime_4511337478633 : Nat.Prime 4511337478633 := by
  apply nodeValid_prime [2, 3, 62657464981] ⟨4511337478633, 5, [(2, 3), (3, 2), (62657464981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62657464981
  · decide +kernel

theorem prime_4511337518713 : Nat.Prime 4511337518713 := by
  apply nodeValid_prime [2, 3, 607, 6311, 49069] ⟨4511337518713, 15, [(2, 3), (3, 1), (607, 1), (6311, 1), (49069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_607
    · exact prime_6311
    · exact prime_49069
  · decide +kernel

theorem prime_4514954502217 : Nat.Prime 4514954502217 := by
  apply nodeValid_prime [2, 3, 43, 4374955913] ⟨4514954502217, 5, [(2, 3), (3, 1), (43, 1), (4374955913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_4374955913
  · decide +kernel

theorem prime_4514954503627 : Nat.Prime 4514954503627 := by
  apply nodeValid_prime [2, 3, 7, 35832972251] ⟨4514954503627, 3, [(2, 1), (3, 2), (7, 1), (35832972251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_35832972251
  · decide +kernel

theorem prime_4514954521067 : Nat.Prime 4514954521067 := by
  apply nodeValid_prime [2, 11, 205225205503] ⟨4514954521067, 2, [(2, 1), (11, 1), (205225205503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_205225205503
  · decide +kernel

theorem prime_4518573411841 : Nat.Prime 4518573411841 := by
  apply nodeValid_prime [2, 3, 5, 31, 71, 8623] ⟨4518573411841, 7, [(2, 9), (3, 1), (5, 1), (31, 2), (71, 1), (8623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_71
    · exact prime_8623
  · decide +kernel

theorem prime_4518573412747 : Nat.Prime 4518573412747 := by
  apply nodeValid_prime [2, 3, 43, 17513850437] ⟨4518573412747, 2, [(2, 1), (3, 1), (43, 1), (17513850437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_17513850437
  · decide +kernel

theorem prime_4518573488021 : Nat.Prime 4518573488021 := by
  apply nodeValid_prime [2, 5, 331, 2609, 261619] ⟨4518573488021, 2, [(2, 2), (5, 1), (331, 1), (2609, 1), (261619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_331
    · exact prime_2609
    · exact prime_261619
  · decide +kernel

theorem prime_4522194398039 : Nat.Prime 4522194398039 := by
  apply nodeValid_prime [2, 2261097199019] ⟨4522194398039, 13, [(2, 1), (2261097199019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2261097199019
  · decide +kernel

theorem prime_4522194398497 : Nat.Prime 4522194398497 := by
  apply nodeValid_prime [2, 3, 1129, 41723819] ⟨4522194398497, 5, [(2, 5), (3, 1), (1129, 1), (41723819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1129
    · exact prime_41723819
  · decide +kernel

theorem prime_4522194419471 : Nat.Prime 4522194419471 := by
  apply nodeValid_prime [2, 5, 7, 13, 479, 211727] ⟨4522194419471, 7, [(2, 1), (5, 1), (7, 3), (13, 1), (479, 1), (211727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_479
    · exact prime_211727
  · decide +kernel

theorem prime_4525817316313 : Nat.Prime 4525817316313 := by
  apply nodeValid_prime [2, 3, 139, 8867, 153001] ⟨4525817316313, 5, [(2, 3), (3, 1), (139, 1), (8867, 1), (153001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_8867
    · exact prime_153001
  · decide +kernel

theorem prime_4525817424377 : Nat.Prime 4525817424377 := by
  apply nodeValid_prime [2, 37, 53, 288489127] ⟨4525817424377, 3, [(2, 3), (37, 1), (53, 1), (288489127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_53
    · exact prime_288489127
  · decide +kernel

theorem prime_4525817426987 : Nat.Prime 4525817426987 := by
  apply nodeValid_prime [2, 2262908713493] ⟨4525817426987, 2, [(2, 1), (2262908713493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2262908713493
  · decide +kernel

theorem prime_4529442175283 : Nat.Prime 4529442175283 := by
  apply nodeValid_prime [2, 2003, 17749, 63703] ⟨4529442175283, 2, [(2, 1), (2003, 1), (17749, 1), (63703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2003
    · exact prime_17749
    · exact prime_63703
  · decide +kernel

theorem prime_4529442200027 : Nat.Prime 4529442200027 := by
  apply nodeValid_prime [2, 137, 7673, 2154413] ⟨4529442200027, 2, [(2, 1), (137, 1), (7673, 1), (2154413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_7673
    · exact prime_2154413
  · decide +kernel

theorem prime_4529442200389 : Nat.Prime 4529442200389 := by
  apply nodeValid_prime [2, 3, 7, 2099, 4603, 5581] ⟨4529442200389, 2, [(2, 2), (3, 1), (7, 1), (2099, 1), (4603, 1), (5581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2099
    · exact prime_4603
    · exact prime_5581
  · decide +kernel

theorem prime_4533068988103 : Nat.Prime 4533068988103 := by
  apply nodeValid_prime [2, 3, 719, 26959, 38977] ⟨4533068988103, 3, [(2, 1), (3, 1), (719, 1), (26959, 1), (38977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
    · exact prime_26959
    · exact prime_38977
  · decide +kernel

theorem prime_4533069034499 : Nat.Prime 4533069034499 := by
  apply nodeValid_prime [2, 41, 203857, 271177] ⟨4533069034499, 2, [(2, 1), (41, 1), (203857, 1), (271177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_203857
    · exact prime_271177
  · decide +kernel

theorem prime_4533069035281 : Nat.Prime 4533069035281 := by
  apply nodeValid_prime [2, 3, 5, 18887787647] ⟨4533069035281, 17, [(2, 4), (3, 1), (5, 1), (18887787647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18887787647
  · decide +kernel

theorem prime_4536697758941 : Nat.Prime 4536697758941 := by
  apply nodeValid_prime [2, 5, 19, 439, 27195167] ⟨4536697758941, 3, [(2, 2), (5, 1), (19, 1), (439, 1), (27195167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_439
    · exact prime_27195167
  · decide +kernel

theorem prime_4536697761403 : Nat.Prime 4536697761403 := by
  apply nodeValid_prime [2, 3, 103, 419, 17520131] ⟨4536697761403, 3, [(2, 1), (3, 1), (103, 1), (419, 1), (17520131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_419
    · exact prime_17520131
  · decide +kernel

theorem prime_4536697761469 : Nat.Prime 4536697761469 := by
  apply nodeValid_prime [2, 3, 17, 7412904839] ⟨4536697761469, 7, [(2, 2), (3, 2), (17, 1), (7412904839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_7412904839
  · decide +kernel

theorem prime_4540328507053 : Nat.Prime 4540328507053 := by
  apply nodeValid_prime [2, 3, 13, 3233852213] ⟨4540328507053, 2, [(2, 2), (3, 3), (13, 1), (3233852213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3233852213
  · decide +kernel

theorem prime_4540328585603 : Nat.Prime 4540328585603 := by
  apply nodeValid_prime [2, 2270164292801] ⟨4540328585603, 2, [(2, 1), (2270164292801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2270164292801
  · decide +kernel

theorem prime_4540328586923 : Nat.Prime 4540328586923 := by
  apply nodeValid_prime [2, 2270164293461] ⟨4540328586923, 2, [(2, 1), (2270164293461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2270164293461
  · decide +kernel

theorem prime_4543961205881 : Nat.Prime 4543961205881 := by
  apply nodeValid_prime [2, 5, 17, 6682295891] ⟨4543961205881, 3, [(2, 3), (5, 1), (17, 1), (6682295891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_6682295891
  · decide +kernel

theorem prime_4543961206403 : Nat.Prime 4543961206403 := by
  apply nodeValid_prime [2, 1286819, 1765579] ⟨4543961206403, 2, [(2, 1), (1286819, 1), (1765579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1286819
    · exact prime_1765579
  · decide +kernel

theorem prime_4543961227753 : Nat.Prime 4543961227753 := by
  apply nodeValid_prime [2, 3, 71, 2666643913] ⟨4543961227753, 5, [(2, 3), (3, 1), (71, 1), (2666643913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_2666643913
  · decide +kernel

theorem prime_4547595920627 : Nat.Prime 4547595920627 := by
  apply nodeValid_prime [2, 11, 206708905483] ⟨4547595920627, 2, [(2, 1), (11, 1), (206708905483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_206708905483
  · decide +kernel

theorem prime_4547595929081 : Nat.Prime 4547595929081 := by
  apply nodeValid_prime [2, 5, 41, 2772924347] ⟨4547595929081, 6, [(2, 3), (5, 1), (41, 1), (2772924347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_2772924347
  · decide +kernel

theorem prime_4547595929543 : Nat.Prime 4547595929543 := by
  apply nodeValid_prime [2, 23, 89, 1110795293] ⟨4547595929543, 5, [(2, 1), (23, 1), (89, 1), (1110795293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_89
    · exact prime_1110795293
  · decide +kernel

theorem prime_4551232567859 : Nat.Prime 4551232567859 := by
  apply nodeValid_prime [2, 3253, 9551, 73243] ⟨4551232567859, 2, [(2, 1), (3253, 1), (9551, 1), (73243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3253
    · exact prime_9551
    · exact prime_73243
  · decide +kernel

theorem prime_4551232567883 : Nat.Prime 4551232567883 := by
  apply nodeValid_prime [2, 7, 11, 13, 269, 8451089] ⟨4551232567883, 2, [(2, 1), (7, 1), (11, 1), (13, 1), (269, 1), (8451089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_269
    · exact prime_8451089
  · decide +kernel

theorem prime_4551232574521 : Nat.Prime 4551232574521 := by
  apply nodeValid_prime [2, 3, 5, 12642312707] ⟨4551232574521, 14, [(2, 3), (3, 2), (5, 1), (12642312707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12642312707
  · decide +kernel

theorem prime_4554871198483 : Nat.Prime 4554871198483 := by
  apply nodeValid_prime [2, 3, 11, 19, 37, 43, 2283013] ⟨4554871198483, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (37, 1), (43, 1), (2283013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_37
    · exact prime_43
    · exact prime_2283013
  · decide +kernel

theorem prime_4554871201087 : Nat.Prime 4554871201087 := by
  apply nodeValid_prime [2, 3, 314453, 2414177] ⟨4554871201087, 3, [(2, 1), (3, 1), (314453, 1), (2414177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_314453
    · exact prime_2414177
  · decide +kernel

theorem prime_4554871208477 : Nat.Prime 4554871208477 := by
  apply nodeValid_prime [2, 19, 59932515901] ⟨4554871208477, 2, [(2, 2), (19, 1), (59932515901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59932515901
  · decide +kernel

theorem prime_4558511814847 : Nat.Prime 4558511814847 := by
  apply nodeValid_prime [2, 3, 11, 69068360831] ⟨4558511814847, 3, [(2, 1), (3, 1), (11, 1), (69068360831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_69068360831
  · decide +kernel

theorem prime_4558511859623 : Nat.Prime 4558511859623 := by
  apply nodeValid_prime [2, 7, 83, 560426833] ⟨4558511859623, 7, [(2, 1), (7, 2), (83, 1), (560426833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
    · exact prime_560426833
  · decide +kernel

theorem prime_4558511861273 : Nat.Prime 4558511861273 := by
  apply nodeValid_prime [2, 853, 911, 733273] ⟨4558511861273, 3, [(2, 3), (853, 1), (911, 1), (733273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_853
    · exact prime_911
    · exact prime_733273
  · decide +kernel

theorem prime_4562154369991 : Nat.Prime 4562154369991 := by
  apply nodeValid_prime [2, 3, 5, 7, 563, 4287457] ⟨4562154369991, 3, [(2, 1), (3, 3), (5, 1), (7, 1), (563, 1), (4287457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_563
    · exact prime_4287457
  · decide +kernel

theorem prime_4562154371041 : Nat.Prime 4562154371041 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 31576373] ⟨4562154371041, 13, [(2, 5), (3, 1), (5, 1), (7, 1), (43, 1), (31576373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_31576373
  · decide +kernel

theorem prime_4562154397387 : Nat.Prime 4562154397387 := by
  apply nodeValid_prime [2, 3, 47, 2273, 2372467] ⟨4562154397387, 3, [(2, 1), (3, 2), (47, 1), (2273, 1), (2372467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_2273
    · exact prime_2372467
  · decide +kernel

theorem prime_4565798960083 : Nat.Prime 4565798960083 := by
  apply nodeValid_prime [2, 3, 31, 73, 1721, 195389] ⟨4565798960083, 2, [(2, 1), (3, 1), (31, 1), (73, 1), (1721, 1), (195389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_73
    · exact prime_1721
    · exact prime_195389
  · decide +kernel

theorem prime_4565798966909 : Nat.Prime 4565798966909 := by
  apply nodeValid_prime [2, 1141449741727] ⟨4565798966909, 2, [(2, 2), (1141449741727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1141449741727
  · decide +kernel

theorem prime_4565798968639 : Nat.Prime 4565798968639 := by
  apply nodeValid_prime [2, 3, 31, 251, 2683, 36451] ⟨4565798968639, 3, [(2, 1), (3, 1), (31, 1), (251, 1), (2683, 1), (36451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_251
    · exact prime_2683
    · exact prime_36451
  · decide +kernel

theorem prime_4569445478593 : Nat.Prime 4569445478593 := by
  apply nodeValid_prime [2, 3, 61, 130050247] ⟨4569445478593, 10, [(2, 6), (3, 2), (61, 1), (130050247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_130050247
  · decide +kernel

theorem prime_4569445480711 : Nat.Prime 4569445480711 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 43, 661, 28657] ⟨4569445480711, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (43, 1), (661, 1), (28657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_43
    · exact prime_661
    · exact prime_28657
  · decide +kernel

theorem prime_4569445489769 : Nat.Prime 4569445489769 := by
  apply nodeValid_prime [2, 571180686221] ⟨4569445489769, 3, [(2, 3), (571180686221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_571180686221
  · decide +kernel

theorem prime_4573093988077 : Nat.Prime 4573093988077 := by
  apply nodeValid_prime [2, 3, 381091165673] ⟨4573093988077, 5, [(2, 2), (3, 1), (381091165673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_381091165673
  · decide +kernel

theorem prime_4573094053519 : Nat.Prime 4573094053519 := by
  apply nodeValid_prime [2, 3, 241, 117132679] ⟨4573094053519, 3, [(2, 1), (3, 4), (241, 1), (117132679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_117132679
  · decide +kernel

theorem prime_4573094053789 : Nat.Prime 4573094053789 := by
  apply nodeValid_prime [2, 3, 13, 103, 31623199] ⟨4573094053789, 6, [(2, 2), (3, 3), (13, 1), (103, 1), (31623199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
    · exact prime_31623199
  · decide +kernel

theorem prime_4576744274159 : Nat.Prime 4576744274159 := by
  apply nodeValid_prime [2, 7, 647, 4057, 124543] ⟨4576744274159, 7, [(2, 1), (7, 1), (647, 1), (4057, 1), (124543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_647
    · exact prime_4057
    · exact prime_124543
  · decide +kernel

theorem prime_4576744275073 : Nat.Prime 4576744275073 := by
  apply nodeValid_prime [2, 3, 67271, 177173] ⟨4576744275073, 5, [(2, 7), (3, 1), (67271, 1), (177173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67271
    · exact prime_177173
  · decide +kernel

theorem prime_4576744453937 : Nat.Prime 4576744453937 := by
  apply nodeValid_prime [2, 286046528371] ⟨4576744453937, 3, [(2, 4), (286046528371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_286046528371
  · decide +kernel

theorem prime_4580396891117 : Nat.Prime 4580396891117 := by
  apply nodeValid_prime [2, 73, 15686290723] ⟨4580396891117, 2, [(2, 2), (73, 1), (15686290723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_15686290723
  · decide +kernel

theorem prime_4580396898989 : Nat.Prime 4580396898989 := by
  apply nodeValid_prime [2, 43, 26630214529] ⟨4580396898989, 2, [(2, 2), (43, 1), (26630214529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_26630214529
  · decide +kernel

theorem prime_4580396901209 : Nat.Prime 4580396901209 := by
  apply nodeValid_prime [2, 149803, 3822017] ⟨4580396901209, 3, [(2, 3), (149803, 1), (3822017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149803
    · exact prime_3822017
  · decide +kernel

theorem prime_4584051294293 : Nat.Prime 4584051294293 := by
  apply nodeValid_prime [2, 1146012823573] ⟨4584051294293, 2, [(2, 2), (1146012823573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1146012823573
  · decide +kernel

theorem prime_4584051341993 : Nat.Prime 4584051341993 := by
  apply nodeValid_prime [2, 573006417749] ⟨4584051341993, 3, [(2, 3), (573006417749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_573006417749
  · decide +kernel

theorem prime_4584051342557 : Nat.Prime 4584051342557 := by
  apply nodeValid_prime [2, 7, 101, 4441, 364997] ⟨4584051342557, 2, [(2, 2), (7, 1), (101, 1), (4441, 1), (364997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_4441
    · exact prime_364997
  · decide +kernel

end Sude.Lucas.Generated
