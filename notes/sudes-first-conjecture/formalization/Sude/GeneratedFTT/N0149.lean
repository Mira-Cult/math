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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0128
import Sude.GeneratedFTT.N0135
import Sude.GeneratedFTT.N0139

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6361 : Nat.Prime 6361 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨6361, 19, [(2, 3), (3, 1), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_7129 : Nat.Prime 7129 := by
  apply nodeValid_prime [2, 3, 11] ⟨7129, 7, [(2, 3), (3, 4), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_18661 : Nat.Prime 18661 := by
  apply nodeValid_prime [2, 3, 5, 311] ⟨18661, 10, [(2, 2), (3, 1), (5, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_311
  · decide +kernel

theorem prime_21563 : Nat.Prime 21563 := by
  apply nodeValid_prime [2, 10781] ⟨21563, 2, [(2, 1), (10781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10781
  · decide +kernel

theorem prime_26881 : Nat.Prime 26881 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨26881, 11, [(2, 8), (3, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_28517 : Nat.Prime 28517 := by
  apply nodeValid_prime [2, 7129] ⟨28517, 2, [(2, 2), (7129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7129
  · decide +kernel

theorem prime_31321 : Nat.Prime 31321 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨31321, 7, [(2, 3), (3, 3), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_36787 : Nat.Prime 36787 := by
  apply nodeValid_prime [2, 3, 6131] ⟨36787, 2, [(2, 1), (3, 1), (6131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6131
  · decide +kernel

theorem prime_41077 : Nat.Prime 41077 := by
  apply nodeValid_prime [2, 3, 7, 163] ⟨41077, 2, [(2, 2), (3, 2), (7, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_163
  · decide +kernel

theorem prime_41593 : Nat.Prime 41593 := by
  apply nodeValid_prime [2, 3, 1733] ⟨41593, 5, [(2, 3), (3, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1733
  · decide +kernel

theorem prime_46327 : Nat.Prime 46327 := by
  apply nodeValid_prime [2, 3, 7, 1103] ⟨46327, 3, [(2, 1), (3, 1), (7, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1103
  · decide +kernel

theorem prime_47251 : Nat.Prime 47251 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨47251, 10, [(2, 1), (3, 3), (5, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_49009 : Nat.Prime 49009 := by
  apply nodeValid_prime [2, 3, 1021] ⟨49009, 19, [(2, 4), (3, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
  · decide +kernel

theorem prime_58193 : Nat.Prime 58193 := by
  apply nodeValid_prime [2, 3637] ⟨58193, 3, [(2, 4), (3637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3637
  · decide +kernel

theorem prime_70423 : Nat.Prime 70423 := by
  apply nodeValid_prime [2, 3, 11, 97] ⟨70423, 5, [(2, 1), (3, 1), (11, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_75337 : Nat.Prime 75337 := by
  apply nodeValid_prime [2, 3, 43, 73] ⟨75337, 5, [(2, 3), (3, 1), (43, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_73
  · decide +kernel

theorem prime_80077 : Nat.Prime 80077 := by
  apply nodeValid_prime [2, 3, 6673] ⟨80077, 2, [(2, 2), (3, 1), (6673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6673
  · decide +kernel

theorem prime_92233 : Nat.Prime 92233 := by
  apply nodeValid_prime [2, 3, 7, 61] ⟨92233, 5, [(2, 3), (3, 3), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_100829 : Nat.Prime 100829 := by
  apply nodeValid_prime [2, 7, 13, 277] ⟨100829, 2, [(2, 2), (7, 1), (13, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_277
  · decide +kernel

theorem prime_101279 : Nat.Prime 101279 := by
  apply nodeValid_prime [2, 79, 641] ⟨101279, 17, [(2, 1), (79, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_641
  · decide +kernel

theorem prime_101741 : Nat.Prime 101741 := by
  apply nodeValid_prime [2, 5, 5087] ⟨101741, 2, [(2, 2), (5, 1), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5087
  · decide +kernel

theorem prime_149159 : Nat.Prime 149159 := by
  apply nodeValid_prime [2, 17, 41, 107] ⟨149159, 19, [(2, 1), (17, 1), (41, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_107
  · decide +kernel

theorem prime_164309 : Nat.Prime 164309 := by
  apply nodeValid_prime [2, 41077] ⟨164309, 2, [(2, 2), (41077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41077
  · decide +kernel

theorem prime_177101 : Nat.Prime 177101 := by
  apply nodeValid_prime [2, 5, 7, 11, 23] ⟨177101, 2, [(2, 2), (5, 2), (7, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_178489 : Nat.Prime 178489 := by
  apply nodeValid_prime [2, 3, 37, 67] ⟨178489, 14, [(2, 3), (3, 2), (37, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_67
  · decide +kernel

theorem prime_178903 : Nat.Prime 178903 := by
  apply nodeValid_prime [2, 3, 3313] ⟨178903, 3, [(2, 1), (3, 3), (3313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3313
  · decide +kernel

theorem prime_179923 : Nat.Prime 179923 := by
  apply nodeValid_prime [2, 3, 157, 191] ⟨179923, 2, [(2, 1), (3, 1), (157, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_191
  · decide +kernel

theorem prime_190837 : Nat.Prime 190837 := by
  apply nodeValid_prime [2, 3, 19, 31] ⟨190837, 5, [(2, 2), (3, 4), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_195259 : Nat.Prime 195259 := by
  apply nodeValid_prime [2, 3, 7, 4649] ⟨195259, 11, [(2, 1), (3, 1), (7, 1), (4649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4649
  · decide +kernel

theorem prime_282577 : Nat.Prime 282577 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨282577, 10, [(2, 4), (3, 1), (7, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_283579 : Nat.Prime 283579 := by
  apply nodeValid_prime [2, 3, 151, 313] ⟨283579, 2, [(2, 1), (3, 1), (151, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_313
  · decide +kernel

theorem prime_316201 : Nat.Prime 316201 := by
  apply nodeValid_prime [2, 3, 5, 17, 31] ⟨316201, 11, [(2, 3), (3, 1), (5, 2), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_332573 : Nat.Prime 332573 := by
  apply nodeValid_prime [2, 29, 47, 61] ⟨332573, 2, [(2, 2), (29, 1), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_337861 : Nat.Prime 337861 := by
  apply nodeValid_prime [2, 3, 5, 1877] ⟨337861, 2, [(2, 2), (3, 2), (5, 1), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1877
  · decide +kernel

theorem prime_358727 : Nat.Prime 358727 := by
  apply nodeValid_prime [2, 83, 2161] ⟨358727, 5, [(2, 1), (83, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_2161
  · decide +kernel

theorem prime_384719 : Nat.Prime 384719 := by
  apply nodeValid_prime [2, 149, 1291] ⟨384719, 11, [(2, 1), (149, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_1291
  · decide +kernel

theorem prime_436741 : Nat.Prime 436741 := by
  apply nodeValid_prime [2, 3, 5, 29, 251] ⟨436741, 10, [(2, 2), (3, 1), (5, 1), (29, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_251
  · decide +kernel

theorem prime_481843 : Nat.Prime 481843 := by
  apply nodeValid_prime [2, 3, 8923] ⟨481843, 3, [(2, 1), (3, 3), (8923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8923
  · decide +kernel

theorem prime_485207 : Nat.Prime 485207 := by
  apply nodeValid_prime [2, 242603] ⟨485207, 5, [(2, 1), (242603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_242603
  · decide +kernel

theorem prime_508213 : Nat.Prime 508213 := by
  apply nodeValid_prime [2, 3, 19, 743] ⟨508213, 6, [(2, 2), (3, 2), (19, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_743
  · decide +kernel

theorem prime_540437 : Nat.Prime 540437 := by
  apply nodeValid_prime [2, 13, 19, 547] ⟨540437, 2, [(2, 2), (13, 1), (19, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_547
  · decide +kernel

theorem prime_567013 : Nat.Prime 567013 := by
  apply nodeValid_prime [2, 3, 47251] ⟨567013, 2, [(2, 2), (3, 1), (47251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47251
  · decide +kernel

theorem prime_570079 : Nat.Prime 570079 := by
  apply nodeValid_prime [2, 3, 17, 23] ⟨570079, 3, [(2, 1), (3, 6), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_714893 : Nat.Prime 714893 := by
  apply nodeValid_prime [2, 313, 571] ⟨714893, 2, [(2, 2), (313, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_571
  · decide +kernel

theorem prime_741233 : Nat.Prime 741233 := by
  apply nodeValid_prime [2, 46327] ⟨741233, 3, [(2, 4), (46327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46327
  · decide +kernel

theorem prime_982973 : Nat.Prime 982973 := by
  apply nodeValid_prime [2, 397, 619] ⟨982973, 2, [(2, 2), (397, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_619
  · decide +kernel

theorem prime_1356067 : Nat.Prime 1356067 := by
  apply nodeValid_prime [2, 3, 75337] ⟨1356067, 2, [(2, 1), (3, 2), (75337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75337
  · decide +kernel

theorem prime_1360409 : Nat.Prime 1360409 := by
  apply nodeValid_prime [2, 7, 17, 1429] ⟨1360409, 6, [(2, 3), (7, 1), (17, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1429
  · decide +kernel

theorem prime_1584389 : Nat.Prime 1584389 := by
  apply nodeValid_prime [2, 13, 30469] ⟨1584389, 2, [(2, 2), (13, 1), (30469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_30469
  · decide +kernel

theorem prime_1627013 : Nat.Prime 1627013 := by
  apply nodeValid_prime [2, 137, 2969] ⟨1627013, 2, [(2, 2), (137, 1), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_2969
  · decide +kernel

theorem prime_2340697 : Nat.Prime 2340697 := by
  apply nodeValid_prime [2, 3, 17, 5737] ⟨2340697, 5, [(2, 3), (3, 1), (17, 1), (5737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_5737
  · decide +kernel

theorem prime_2698573 : Nat.Prime 2698573 := by
  apply nodeValid_prime [2, 3, 224881] ⟨2698573, 5, [(2, 2), (3, 1), (224881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_224881
  · decide +kernel

theorem prime_3162011 : Nat.Prime 3162011 := by
  apply nodeValid_prime [2, 5, 316201] ⟨3162011, 2, [(2, 1), (5, 1), (316201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_316201
  · decide +kernel

theorem prime_3386989 : Nat.Prime 3386989 := by
  apply nodeValid_prime [2, 3, 11, 2851] ⟨3386989, 2, [(2, 2), (3, 3), (11, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2851
  · decide +kernel

theorem prime_3402079 : Nat.Prime 3402079 := by
  apply nodeValid_prime [2, 3, 567013] ⟨3402079, 3, [(2, 1), (3, 1), (567013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_567013
  · decide +kernel

theorem prime_3597511 : Nat.Prime 3597511 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 463] ⟨3597511, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_463
  · decide +kernel

theorem prime_3708863 : Nat.Prime 3708863 := by
  apply nodeValid_prime [2, 151, 12281] ⟨3708863, 5, [(2, 1), (151, 1), (12281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_12281
  · decide +kernel

theorem prime_4320097 : Nat.Prime 4320097 := by
  apply nodeValid_prime [2, 3, 11, 4091] ⟨4320097, 5, [(2, 5), (3, 1), (11, 1), (4091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4091
  · decide +kernel

theorem prime_5897839 : Nat.Prime 5897839 := by
  apply nodeValid_prime [2, 3, 982973] ⟨5897839, 3, [(2, 1), (3, 1), (982973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_982973
  · decide +kernel

theorem prime_6324023 : Nat.Prime 6324023 := by
  apply nodeValid_prime [2, 3162011] ⟨6324023, 5, [(2, 1), (3162011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3162011
  · decide +kernel

theorem prime_6480811 : Nat.Prime 6480811 := by
  apply nodeValid_prime [2, 3, 5, 7, 127] ⟨6480811, 3, [(2, 1), (3, 6), (5, 1), (7, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_8282809 : Nat.Prime 8282809 := by
  apply nodeValid_prime [2, 3, 17, 67, 101] ⟨8282809, 13, [(2, 3), (3, 2), (17, 1), (67, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
    · exact prime_101
  · decide +kernel

theorem prime_11738407 : Nat.Prime 11738407 := by
  apply nodeValid_prime [2, 3, 1321, 1481] ⟨11738407, 3, [(2, 1), (3, 1), (1321, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1321
    · exact prime_1481
  · decide +kernel

theorem prime_12333283 : Nat.Prime 12333283 := by
  apply nodeValid_prime [2, 3, 13, 12163] ⟨12333283, 2, [(2, 1), (3, 1), (13, 2), (12163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_12163
  · decide +kernel

theorem prime_12950519 : Nat.Prime 12950519 := by
  apply nodeValid_prime [2, 7, 23, 37, 1087] ⟨12950519, 7, [(2, 1), (7, 1), (23, 1), (37, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_37
    · exact prime_1087
  · decide +kernel

theorem prime_19778233 : Nat.Prime 19778233 := by
  apply nodeValid_prime [2, 3, 29, 157, 181] ⟨19778233, 5, [(2, 3), (3, 1), (29, 1), (157, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_157
    · exact prime_181
  · decide +kernel

theorem prime_22803161 : Nat.Prime 22803161 := by
  apply nodeValid_prime [2, 5, 570079] ⟨22803161, 3, [(2, 3), (5, 1), (570079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_570079
  · decide +kernel

theorem prime_24508709 : Nat.Prime 24508709 := by
  apply nodeValid_prime [2, 7, 19, 23, 2003] ⟨24508709, 2, [(2, 2), (7, 1), (19, 1), (23, 1), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_2003
  · decide +kernel

theorem prime_26366843 : Nat.Prime 26366843 := by
  apply nodeValid_prime [2, 269, 49009] ⟨26366843, 2, [(2, 1), (269, 1), (49009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_49009
  · decide +kernel

theorem prime_27695471 : Nat.Prime 27695471 := by
  apply nodeValid_prime [2, 5, 11, 73, 3449] ⟨27695471, 11, [(2, 1), (5, 1), (11, 1), (73, 1), (3449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_73
    · exact prime_3449
  · decide +kernel

theorem prime_29931571 : Nat.Prime 29931571 := by
  apply nodeValid_prime [2, 3, 5, 332573] ⟨29931571, 3, [(2, 1), (3, 2), (5, 1), (332573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_332573
  · decide +kernel

theorem prime_34353877 : Nat.Prime 34353877 := by
  apply nodeValid_prime [2, 3, 1451, 1973] ⟨34353877, 2, [(2, 2), (3, 1), (1451, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
    · exact prime_1973
  · decide +kernel

theorem prime_36241351 : Nat.Prime 36241351 := by
  apply nodeValid_prime [2, 3, 5, 307, 787] ⟨36241351, 3, [(2, 1), (3, 1), (5, 2), (307, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_307
    · exact prime_787
  · decide +kernel

theorem prime_40085327 : Nat.Prime 40085327 := by
  apply nodeValid_prime [2, 19, 727, 1451] ⟨40085327, 5, [(2, 1), (19, 1), (727, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_727
    · exact prime_1451
  · decide +kernel

theorem prime_64808111 : Nat.Prime 64808111 := by
  apply nodeValid_prime [2, 5, 6480811] ⟨64808111, 7, [(2, 1), (5, 1), (6480811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6480811
  · decide +kernel

theorem prime_84838679 : Nat.Prime 84838679 := by
  apply nodeValid_prime [2, 61, 739, 941] ⟨84838679, 7, [(2, 1), (61, 1), (739, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_739
    · exact prime_941
  · decide +kernel

theorem prime_85465241 : Nat.Prime 85465241 := by
  apply nodeValid_prime [2, 5, 7, 23, 577] ⟨85465241, 3, [(2, 3), (5, 1), (7, 1), (23, 2), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_577
  · decide +kernel

theorem prime_100331353 : Nat.Prime 100331353 := by
  apply nodeValid_prime [2, 3, 11, 42227] ⟨100331353, 7, [(2, 3), (3, 3), (11, 1), (42227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_42227
  · decide +kernel

theorem prime_106144033 : Nat.Prime 106144033 := by
  apply nodeValid_prime [2, 3, 19, 58193] ⟨106144033, 5, [(2, 5), (3, 1), (19, 1), (58193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_58193
  · decide +kernel

theorem prime_133196461 : Nat.Prime 133196461 := by
  apply nodeValid_prime [2, 3, 5, 19, 31, 3769] ⟨133196461, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (31, 1), (3769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_31
    · exact prime_3769
  · decide +kernel

theorem prime_139221421 : Nat.Prime 139221421 := by
  apply nodeValid_prime [2, 3, 5, 13, 178489] ⟨139221421, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (178489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_178489
  · decide +kernel

theorem prime_149424631 : Nat.Prime 149424631 := by
  apply nodeValid_prime [2, 3, 5, 401, 12421] ⟨149424631, 12, [(2, 1), (3, 1), (5, 1), (401, 1), (12421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_401
    · exact prime_12421
  · decide +kernel

theorem prime_161914381 : Nat.Prime 161914381 := by
  apply nodeValid_prime [2, 3, 5, 2698573] ⟨161914381, 7, [(2, 2), (3, 1), (5, 1), (2698573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2698573
  · decide +kernel

theorem prime_171574321 : Nat.Prime 171574321 := by
  apply nodeValid_prime [2, 3, 5, 714893] ⟨171574321, 11, [(2, 4), (3, 1), (5, 1), (714893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_714893
  · decide +kernel

theorem prime_404834851 : Nat.Prime 404834851 := by
  apply nodeValid_prime [2, 3, 5, 7, 128519] ⟨404834851, 3, [(2, 1), (3, 2), (5, 2), (7, 1), (128519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_128519
  · decide +kernel

theorem prime_408322391 : Nat.Prime 408322391 := by
  apply nodeValid_prime [2, 5, 7, 31, 26881] ⟨408322391, 11, [(2, 1), (5, 1), (7, 2), (31, 1), (26881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_26881
  · decide +kernel

theorem prime_565818257 : Nat.Prime 565818257 := by
  apply nodeValid_prime [2, 251, 140891] ⟨565818257, 3, [(2, 4), (251, 1), (140891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_140891
  · decide +kernel

theorem prime_831991519 : Nat.Prime 831991519 := by
  apply nodeValid_prime [2, 3, 2791, 16561] ⟨831991519, 3, [(2, 1), (3, 2), (2791, 1), (16561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2791
    · exact prime_16561
  · decide +kernel

theorem prime_884613217 : Nat.Prime 884613217 := by
  apply nodeValid_prime [2, 3, 29, 61, 5209] ⟨884613217, 5, [(2, 5), (3, 1), (29, 1), (61, 1), (5209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_61
    · exact prime_5209
  · decide +kernel

theorem prime_906898249 : Nat.Prime 906898249 := by
  apply nodeValid_prime [2, 3, 271, 15493] ⟨906898249, 7, [(2, 3), (3, 3), (271, 1), (15493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_15493
  · decide +kernel

theorem prime_1352459099 : Nat.Prime 1352459099 := by
  apply nodeValid_prime [2, 22133, 30553] ⟨1352459099, 2, [(2, 1), (22133, 1), (30553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_22133
    · exact prime_30553
  · decide +kernel

theorem prime_1356456391 : Nat.Prime 1356456391 := by
  apply nodeValid_prime [2, 3, 5, 61, 741233] ⟨1356456391, 3, [(2, 1), (3, 1), (5, 1), (61, 1), (741233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_741233
  · decide +kernel

theorem prime_2589989431 : Nat.Prime 2589989431 := by
  apply nodeValid_prime [2, 3, 5, 7, 12333283] ⟨2589989431, 15, [(2, 1), (3, 1), (5, 1), (7, 1), (12333283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_12333283
  · decide +kernel

theorem prime_2827726367 : Nat.Prime 2827726367 := by
  apply nodeValid_prime [2, 179, 827, 9551] ⟨2827726367, 5, [(2, 1), (179, 1), (827, 1), (9551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_827
    · exact prime_9551
  · decide +kernel

theorem prime_3046501811 : Nat.Prime 3046501811 := by
  apply nodeValid_prime [2, 5, 11, 27695471] ⟨3046501811, 2, [(2, 1), (5, 1), (11, 1), (27695471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_27695471
  · decide +kernel

theorem prime_3375771067 : Nat.Prime 3375771067 := by
  apply nodeValid_prime [2, 3, 167, 41593] ⟨3375771067, 3, [(2, 1), (3, 5), (167, 1), (41593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_41593
  · decide +kernel

theorem prime_3677567197 : Nat.Prime 3677567197 := by
  apply nodeValid_prime [2, 3, 37, 8282809] ⟨3677567197, 2, [(2, 2), (3, 1), (37, 1), (8282809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_8282809
  · decide +kernel

theorem prime_4156490161 : Nat.Prime 4156490161 := by
  apply nodeValid_prime [2, 3, 5, 19, 101279] ⟨4156490161, 11, [(2, 4), (3, 3), (5, 1), (19, 1), (101279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_101279
  · decide +kernel

theorem prime_4694389729 : Nat.Prime 4694389729 := by
  apply nodeValid_prime [2, 3, 7, 89, 11213] ⟨4694389729, 17, [(2, 5), (3, 1), (7, 2), (89, 1), (11213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_11213
  · decide +kernel

theorem prime_5327858441 : Nat.Prime 5327858441 := by
  apply nodeValid_prime [2, 5, 133196461] ⟨5327858441, 3, [(2, 3), (5, 1), (133196461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_133196461
  · decide +kernel

theorem prime_6427365379 : Nat.Prime 6427365379 := by
  apply nodeValid_prime [2, 3, 7, 653, 33479] ⟨6427365379, 17, [(2, 1), (3, 1), (7, 2), (653, 1), (33479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_653
    · exact prime_33479
  · decide +kernel

theorem prime_6800404003 : Nat.Prime 6800404003 := by
  apply nodeValid_prime [2, 3, 7, 161914381] ⟨6800404003, 2, [(2, 1), (3, 1), (7, 1), (161914381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_161914381
  · decide +kernel

theorem prime_8906366723 : Nat.Prime 8906366723 := by
  apply nodeValid_prime [2, 11, 404834851] ⟨8906366723, 2, [(2, 1), (11, 1), (404834851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_404834851
  · decide +kernel

theorem prime_13503084269 : Nat.Prime 13503084269 := by
  apply nodeValid_prime [2, 3375771067] ⟨13503084269, 2, [(2, 2), (3375771067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3375771067
  · decide +kernel

theorem prime_19028065937 : Nat.Prime 19028065937 := by
  apply nodeValid_prime [2, 11, 53, 401, 5087] ⟨19028065937, 3, [(2, 4), (11, 1), (53, 1), (401, 1), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_401
    · exact prime_5087
  · decide +kernel

theorem prime_40534682761 : Nat.Prime 40534682761 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 251, 3137] ⟨40534682761, 7, [(2, 3), (3, 2), (5, 1), (11, 1), (13, 1), (251, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_251
    · exact prime_3137
  · decide +kernel

theorem prime_146691054791 : Nat.Prime 146691054791 := by
  apply nodeValid_prime [2, 5, 7, 61, 34353877] ⟨146691054791, 7, [(2, 1), (5, 1), (7, 1), (61, 1), (34353877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_34353877
  · decide +kernel

theorem prime_206999492779 : Nat.Prime 206999492779 := by
  apply nodeValid_prime [2, 3, 13, 884613217] ⟨206999492779, 7, [(2, 1), (3, 2), (13, 1), (884613217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_884613217
  · decide +kernel

theorem prime_243208096567 : Nat.Prime 243208096567 := by
  apply nodeValid_prime [2, 3, 40534682761] ⟨243208096567, 3, [(2, 1), (3, 1), (40534682761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40534682761
  · decide +kernel

theorem prime_514097179033 : Nat.Prime 514097179033 := by
  apply nodeValid_prime [2, 3, 1021, 2437, 8609] ⟨514097179033, 10, [(2, 3), (3, 1), (1021, 1), (2437, 1), (8609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
    · exact prime_2437
    · exact prime_8609
  · decide +kernel

theorem prime_1368212463287 : Nat.Prime 1368212463287 := by
  apply nodeValid_prime [2, 199, 6361, 540437] ⟨1368212463287, 5, [(2, 1), (199, 1), (6361, 1), (540437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_6361
    · exact prime_540437
  · decide +kernel

theorem prime_1377271111241 : Nat.Prime 1377271111241 := by
  apply nodeValid_prime [2, 5, 17, 563, 3597511] ⟨1377271111241, 3, [(2, 3), (5, 1), (17, 1), (563, 1), (3597511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_563
    · exact prime_3597511
  · decide +kernel

theorem prime_2060464228717 : Nat.Prime 2060464228717 := by
  apply nodeValid_prime [2, 3, 337861, 508213] ⟨2060464228717, 2, [(2, 2), (3, 1), (337861, 1), (508213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337861
    · exact prime_508213
  · decide +kernel

theorem prime_2072723434909 : Nat.Prime 2072723434909 := by
  apply nodeValid_prime [2, 3, 7, 7253, 3402079] ⟨2072723434909, 2, [(2, 2), (3, 1), (7, 1), (7253, 1), (3402079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7253
    · exact prime_3402079
  · decide +kernel

theorem prime_2080923624919 : Nat.Prime 2080923624919 := by
  apply nodeValid_prime [2, 3, 17, 6800404003] ⟨2080923624919, 12, [(2, 1), (3, 2), (17, 1), (6800404003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_6800404003
  · decide +kernel

theorem prime_4145446854023 : Nat.Prime 4145446854023 := by
  apply nodeValid_prime [2, 733, 2827726367] ⟨4145446854023, 5, [(2, 1), (733, 1), (2827726367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_733
    · exact prime_2827726367
  · decide +kernel

theorem prime_4148177206559 : Nat.Prime 4148177206559 := by
  apply nodeValid_prime [2, 7, 11, 112951, 238477] ⟨4148177206559, 7, [(2, 1), (7, 1), (11, 1), (112951, 1), (238477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_112951
    · exact prime_238477
  · decide +kernel

theorem prime_4156375580429 : Nat.Prime 4156375580429 := by
  apply nodeValid_prime [2, 164309, 6324023] ⟨4156375580429, 2, [(2, 2), (164309, 1), (6324023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_164309
    · exact prime_6324023
  · decide +kernel

theorem prime_8193016331611 : Nat.Prime 8193016331611 := by
  apply nodeValid_prime [2, 3, 5, 11, 1013, 24508709] ⟨8193016331611, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (1013, 1), (24508709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1013
    · exact prime_24508709
  · decide +kernel

theorem prime_8193016340161 : Nat.Prime 8193016340161 := by
  apply nodeValid_prime [2, 3, 5, 659, 12950519] ⟨8193016340161, 37, [(2, 6), (3, 1), (5, 1), (659, 1), (12950519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_659
    · exact prime_12950519
  · decide +kernel

theorem prime_8193016340489 : Nat.Prime 8193016340489 := by
  apply nodeValid_prime [2, 7, 29347, 101741] ⟨8193016340489, 3, [(2, 3), (7, 3), (29347, 1), (101741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29347
    · exact prime_101741
  · decide +kernel

theorem prime_8198433365821 : Nat.Prime 8198433365821 := by
  apply nodeValid_prime [2, 3, 5, 283579, 481843] ⟨8198433365821, 2, [(2, 2), (3, 1), (5, 1), (283579, 1), (481843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_283579
    · exact prime_481843
  · decide +kernel

theorem prime_8198433420761 : Nat.Prime 8198433420761 := by
  apply nodeValid_prime [2, 5, 11, 349, 2861, 18661] ⟨8198433420761, 3, [(2, 3), (5, 1), (11, 1), (349, 1), (2861, 1), (18661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_349
    · exact prime_2861
    · exact prime_18661
  · decide +kernel

theorem prime_8198433421361 : Nat.Prime 8198433421361 := by
  apply nodeValid_prime [2, 5, 7, 13, 251, 787, 5701] ⟨8198433421361, 3, [(2, 4), (5, 1), (7, 1), (13, 1), (251, 1), (787, 1), (5701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_251
    · exact prime_787
    · exact prime_5701
  · decide +kernel

theorem prime_8203852769857 : Nat.Prime 8203852769857 := by
  apply nodeValid_prime [2, 3, 1049, 1889, 21563] ⟨8203852769857, 7, [(2, 6), (3, 1), (1049, 1), (1889, 1), (21563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1049
    · exact prime_1889
    · exact prime_21563
  · decide +kernel

theorem prime_8203852772581 : Nat.Prime 8203852772581 := by
  apply nodeValid_prime [2, 3, 5, 100829, 1356067] ⟨8203852772581, 2, [(2, 2), (3, 1), (5, 1), (100829, 1), (1356067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_100829
    · exact prime_1356067
  · decide +kernel

theorem prime_8203852822537 : Nat.Prime 8203852822537 := by
  apply nodeValid_prime [2, 3, 7, 823, 19778233] ⟨8203852822537, 10, [(2, 3), (3, 2), (7, 1), (823, 1), (19778233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_823
    · exact prime_19778233
  · decide +kernel

theorem prime_8209274705507 : Nat.Prime 8209274705507 := by
  apply nodeValid_prime [2, 7, 37, 131, 277, 436741] ⟨8209274705507, 2, [(2, 1), (7, 1), (37, 1), (131, 1), (277, 1), (436741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_131
    · exact prime_277
    · exact prime_436741
  · decide +kernel

theorem prime_8209274778967 : Nat.Prime 8209274778967 := by
  apply nodeValid_prime [2, 3, 29, 2069, 22803161] ⟨8209274778967, 3, [(2, 1), (3, 1), (29, 1), (2069, 1), (22803161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2069
    · exact prime_22803161
  · decide +kernel

theorem prime_8209274779723 : Nat.Prime 8209274779723 := by
  apply nodeValid_prime [2, 3, 1368212463287] ⟨8209274779723, 22, [(2, 1), (3, 1), (1368212463287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1368212463287
  · decide +kernel

theorem prime_8214699001937 : Nat.Prime 8214699001937 := by
  apply nodeValid_prime [2, 7, 691, 106144033] ⟨8214699001937, 5, [(2, 4), (7, 1), (691, 1), (106144033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_691
    · exact prime_106144033
  · decide +kernel

theorem prime_8214699068297 : Nat.Prime 8214699068297 := by
  apply nodeValid_prime [2, 7, 146691054791] ⟨8214699068297, 3, [(2, 3), (7, 1), (146691054791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_146691054791
  · decide +kernel

theorem prime_8214699069569 : Nat.Prime 8214699069569 := by
  apply nodeValid_prime [2, 178903, 358727] ⟨8214699069569, 3, [(2, 7), (178903, 1), (358727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_178903
    · exact prime_358727
  · decide +kernel

theorem prime_8220125719111 : Nat.Prime 8220125719111 := by
  apply nodeValid_prime [2, 3, 5, 1597, 171574321] ⟨8220125719111, 11, [(2, 1), (3, 1), (5, 1), (1597, 1), (171574321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1597
    · exact prime_171574321
  · decide +kernel

theorem prime_8220125728937 : Nat.Prime 8220125728937 := by
  apply nodeValid_prime [2, 11, 103, 906898249] ⟨8220125728937, 6, [(2, 3), (11, 1), (103, 1), (906898249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_103
    · exact prime_906898249
  · decide +kernel

theorem prime_8220125729461 : Nat.Prime 8220125729461 := by
  apply nodeValid_prime [2, 3, 5, 101, 1356456391] ⟨8220125729461, 6, [(2, 2), (3, 1), (5, 1), (101, 1), (1356456391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_1356456391
  · decide +kernel

theorem prime_8225554864529 : Nat.Prime 8225554864529 := by
  apply nodeValid_prime [2, 514097179033] ⟨8225554864529, 3, [(2, 4), (514097179033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_514097179033
  · decide +kernel

theorem prime_8225554889653 : Nat.Prime 8225554889653 := by
  apply nodeValid_prime [2, 3, 22901, 29931571] ⟨8225554889653, 2, [(2, 2), (3, 1), (22901, 1), (29931571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22901
    · exact prime_29931571
  · decide +kernel

theorem prime_8225554889701 : Nat.Prime 8225554889701 := by
  apply nodeValid_prime [2, 3, 5, 3046501811] ⟨8225554889701, 11, [(2, 2), (3, 3), (5, 2), (3046501811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3046501811
  · decide +kernel

theorem prime_8230986411719 : Nat.Prime 8230986411719 := by
  apply nodeValid_prime [2, 7, 227, 2589989431] ⟨8230986411719, 7, [(2, 1), (7, 1), (227, 1), (2589989431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
    · exact prime_2589989431
  · decide +kernel

theorem prime_8230986412007 : Nat.Prime 8230986412007 := by
  apply nodeValid_prime [2, 307, 8461, 1584389] ⟨8230986412007, 5, [(2, 1), (307, 1), (8461, 1), (1584389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_8461
    · exact prime_1584389
  · decide +kernel

theorem prime_8230986430229 : Nat.Prime 8230986430229 := by
  apply nodeValid_prime [2, 24077, 85465241] ⟨8230986430229, 2, [(2, 2), (24077, 1), (85465241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_24077
    · exact prime_85465241
  · decide +kernel

theorem prime_8236420418621 : Nat.Prime 8236420418621 := by
  apply nodeValid_prime [2, 5, 37, 3001, 3708863] ⟨8236420418621, 2, [(2, 2), (5, 1), (37, 1), (3001, 1), (3708863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_3001
    · exact prime_3708863
  · decide +kernel

theorem prime_8236420453993 : Nat.Prime 8236420453993 := by
  apply nodeValid_prime [2, 3, 19, 37, 113, 4320097] ⟨8236420453993, 10, [(2, 3), (3, 1), (19, 1), (37, 1), (113, 1), (4320097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_113
    · exact prime_4320097
  · decide +kernel

theorem prime_8236420454503 : Nat.Prime 8236420454503 := by
  apply nodeValid_prime [2, 3, 179923, 282577] ⟨8236420454503, 5, [(2, 1), (3, 4), (179923, 1), (282577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179923
    · exact prime_282577
  · decide +kernel

theorem prime_8241856826393 : Nat.Prime 8241856826393 := by
  apply nodeValid_prime [2, 7, 173, 383, 919, 2417] ⟨8241856826393, 3, [(2, 3), (7, 1), (173, 1), (383, 1), (919, 1), (2417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_173
    · exact prime_383
    · exact prime_919
    · exact prime_2417
  · decide +kernel

theorem prime_8241856914409 : Nat.Prime 8241856914409 := by
  apply nodeValid_prime [2, 3, 13, 149159, 177101] ⟨8241856914409, 7, [(2, 3), (3, 1), (13, 1), (149159, 1), (177101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_149159
    · exact prime_177101
  · decide +kernel

theorem prime_8241856914869 : Nat.Prime 8241856914869 := by
  apply nodeValid_prime [2, 2060464228717] ⟨8241856914869, 2, [(2, 2), (2060464228717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2060464228717
  · decide +kernel

theorem prime_8247295585499 : Nat.Prime 8247295585499 := by
  apply nodeValid_prime [2, 463, 8906366723] ⟨8247295585499, 2, [(2, 1), (463, 1), (8906366723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_463
    · exact prime_8906366723
  · decide +kernel

theorem prime_8247295585703 : Nat.Prime 8247295585703 := by
  apply nodeValid_prime [2, 3049, 1352459099] ⟨8247295585703, 5, [(2, 1), (3049, 1), (1352459099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3049
    · exact prime_1352459099
  · decide +kernel

theorem prime_8247295653419 : Nat.Prime 8247295653419 := by
  apply nodeValid_prime [2, 10099, 408322391] ⟨8247295653419, 2, [(2, 1), (10099, 1), (408322391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10099
    · exact prime_408322391
  · decide +kernel

theorem prime_8252736907559 : Nat.Prime 8252736907559 := by
  apply nodeValid_prime [2, 11, 13, 19, 41, 887, 41761] ⟨8252736907559, 7, [(2, 1), (11, 1), (13, 1), (19, 1), (41, 1), (887, 1), (41761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_41
    · exact prime_887
    · exact prime_41761
  · decide +kernel

theorem prime_8252737143583 : Nat.Prime 8252737143583 := by
  apply nodeValid_prime [2, 3, 293, 4694389729] ⟨8252737143583, 3, [(2, 1), (3, 1), (293, 1), (4694389729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_4694389729
  · decide +kernel

theorem prime_8252737146637 : Nat.Prime 8252737146637 := by
  apply nodeValid_prime [2, 3, 107, 6427365379] ⟨8252737146637, 2, [(2, 2), (3, 1), (107, 1), (6427365379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_6427365379
  · decide +kernel

theorem prime_8258180583551 : Nat.Prime 8258180583551 := by
  apply nodeValid_prime [2, 5, 31, 5327858441] ⟨8258180583551, 13, [(2, 1), (5, 2), (31, 1), (5327858441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_5327858441
  · decide +kernel

theorem prime_8258180615827 : Nat.Prime 8258180615827 := by
  apply nodeValid_prime [2, 3, 37, 3169, 11738407] ⟨8258180615827, 3, [(2, 1), (3, 1), (37, 1), (3169, 1), (11738407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_3169
    · exact prime_11738407
  · decide +kernel

theorem prime_8258180616659 : Nat.Prime 8258180616659 := by
  apply nodeValid_prime [2, 7, 31, 19028065937] ⟨8258180616659, 2, [(2, 1), (7, 1), (31, 1), (19028065937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_19028065937
  · decide +kernel

theorem prime_8263626664877 : Nat.Prime 8263626664877 := by
  apply nodeValid_prime [2, 11, 19, 71, 139221421] ⟨8263626664877, 2, [(2, 2), (11, 1), (19, 1), (71, 1), (139221421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_71
    · exact prime_139221421
  · decide +kernel

theorem prime_8263626667447 : Nat.Prime 8263626667447 := by
  apply nodeValid_prime [2, 3, 1377271111241] ⟨8263626667447, 3, [(2, 1), (3, 1), (1377271111241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1377271111241
  · decide +kernel

theorem prime_8263626689317 : Nat.Prime 8263626689317 := by
  apply nodeValid_prime [2, 3, 8117, 84838679] ⟨8263626689317, 5, [(2, 2), (3, 1), (8117, 1), (84838679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8117
    · exact prime_84838679
  · decide +kernel

theorem prime_8269075223743 : Nat.Prime 8269075223743 := by
  apply nodeValid_prime [2, 3, 2083, 3467, 190837] ⟨8269075223743, 3, [(2, 1), (3, 1), (2083, 1), (3467, 1), (190837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2083
    · exact prime_3467
    · exact prime_190837
  · decide +kernel

theorem prime_8269075279763 : Nat.Prime 8269075279763 := by
  apply nodeValid_prime [2, 11, 70423, 485207] ⟨8269075279763, 2, [(2, 1), (11, 2), (70423, 1), (485207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_70423
    · exact prime_485207
  · decide +kernel

theorem prime_8269075283279 : Nat.Prime 8269075283279 := by
  apply nodeValid_prime [2, 17, 243208096567] ⟨8269075283279, 13, [(2, 1), (17, 1), (243208096567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_243208096567
  · decide +kernel

theorem prime_8274526190369 : Nat.Prime 8274526190369 := by
  apply nodeValid_prime [2, 457, 565818257] ⟨8274526190369, 3, [(2, 5), (457, 1), (565818257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_565818257
  · decide +kernel

theorem prime_8274526191401 : Nat.Prime 8274526191401 := by
  apply nodeValid_prime [2, 5, 7, 593, 1013, 9839] ⟨8274526191401, 6, [(2, 3), (5, 2), (7, 1), (593, 1), (1013, 1), (9839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_593
    · exact prime_1013
    · exact prime_9839
  · decide +kernel

theorem prime_8274526193251 : Nat.Prime 8274526193251 := by
  apply nodeValid_prime [2, 3, 5, 3677567197] ⟨8274526193251, 2, [(2, 1), (3, 2), (5, 3), (3677567197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3677567197
  · decide +kernel

theorem prime_8279979597089 : Nat.Prime 8279979597089 := by
  apply nodeValid_prime [2, 311, 831991519] ⟨8279979597089, 3, [(2, 5), (311, 1), (831991519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_831991519
  · decide +kernel

theorem prime_8279979707291 : Nat.Prime 8279979707291 := by
  apply nodeValid_prime [2, 5, 31, 1013, 26366843] ⟨8279979707291, 2, [(2, 1), (5, 1), (31, 1), (1013, 1), (26366843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1013
    · exact prime_26366843
  · decide +kernel

theorem prime_8279979711161 : Nat.Prime 8279979711161 := by
  apply nodeValid_prime [2, 5, 206999492779] ⟨8279979711161, 3, [(2, 3), (5, 1), (206999492779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_206999492779
  · decide +kernel

theorem prime_8285435389207 : Nat.Prime 8285435389207 := by
  apply nodeValid_prime [2, 3, 89, 509, 3386989] ⟨8285435389207, 3, [(2, 1), (3, 3), (89, 1), (509, 1), (3386989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_509
    · exact prime_3386989
  · decide +kernel

theorem prime_8285435391811 : Nat.Prime 8285435391811 := by
  apply nodeValid_prime [2, 3, 5, 117991, 2340697] ⟨8285435391811, 7, [(2, 1), (3, 1), (5, 1), (117991, 1), (2340697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_117991
    · exact prime_2340697
  · decide +kernel

theorem prime_8285435434343 : Nat.Prime 8285435434343 := by
  apply nodeValid_prime [2, 11, 359, 28517, 36787] ⟨8285435434343, 5, [(2, 1), (11, 1), (359, 1), (28517, 1), (36787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_359
    · exact prime_28517
    · exact prime_36787
  · decide +kernel

theorem prime_8290893708047 : Nat.Prime 8290893708047 := by
  apply nodeValid_prime [2, 4145446854023] ⟨8290893708047, 5, [(2, 1), (4145446854023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4145446854023
  · decide +kernel

theorem prime_8290893739637 : Nat.Prime 8290893739637 := by
  apply nodeValid_prime [2, 2072723434909] ⟨8290893739637, 2, [(2, 2), (2072723434909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2072723434909
  · decide +kernel

theorem prime_8290893741167 : Nat.Prime 8290893741167 := by
  apply nodeValid_prime [2, 307, 13503084269] ⟨8290893741167, 5, [(2, 1), (307, 1), (13503084269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_13503084269
  · decide +kernel

theorem prime_8296354361357 : Nat.Prime 8296354361357 := by
  apply nodeValid_prime [2, 499, 4156490161] ⟨8296354361357, 2, [(2, 2), (499, 1), (4156490161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_499
    · exact prime_4156490161
  · decide +kernel

theorem prime_8296354362383 : Nat.Prime 8296354362383 := by
  apply nodeValid_prime [2, 17, 23, 71, 149424631] ⟨8296354362383, 10, [(2, 1), (17, 1), (23, 1), (71, 1), (149424631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_71
    · exact prime_149424631
  · decide +kernel

theorem prime_8296354413119 : Nat.Prime 8296354413119 := by
  apply nodeValid_prime [2, 4148177206559] ⟨8296354413119, 11, [(2, 1), (4148177206559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4148177206559
  · decide +kernel

theorem prime_8301817472593 : Nat.Prime 8301817472593 := by
  apply nodeValid_prime [2, 3, 7, 31, 25447, 31321] ⟨8301817472593, 5, [(2, 4), (3, 1), (7, 1), (31, 1), (25447, 1), (31321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_25447
    · exact prime_31321
  · decide +kernel

theorem prime_8301817472633 : Nat.Prime 8301817472633 := by
  apply nodeValid_prime [2, 10343, 100331353] ⟨8301817472633, 3, [(2, 3), (10343, 1), (100331353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10343
    · exact prime_100331353
  · decide +kernel

theorem prime_8301817562371 : Nat.Prime 8301817562371 := by
  apply nodeValid_prime [2, 3, 5, 283, 601, 1627013] ⟨8301817562371, 7, [(2, 1), (3, 1), (5, 1), (283, 1), (601, 1), (1627013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_283
    · exact prime_601
    · exact prime_1627013
  · decide +kernel

theorem prime_8307283142141 : Nat.Prime 8307283142141 := by
  apply nodeValid_prime [2, 5, 101, 3023, 1360409] ⟨8307283142141, 2, [(2, 2), (5, 1), (101, 1), (3023, 1), (1360409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_3023
    · exact prime_1360409
  · decide +kernel

theorem prime_8307283166671 : Nat.Prime 8307283166671 := by
  apply nodeValid_prime [2, 3, 5, 29, 1619, 5897839] ⟨8307283166671, 11, [(2, 1), (3, 1), (5, 1), (29, 1), (1619, 1), (5897839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1619
    · exact prime_5897839
  · decide +kernel

theorem prime_8307283167481 : Nat.Prime 8307283167481 := by
  apply nodeValid_prime [2, 3, 5, 11, 157, 40085327] ⟨8307283167481, 17, [(2, 3), (3, 1), (5, 1), (11, 1), (157, 1), (40085327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_157
    · exact prime_40085327
  · decide +kernel

theorem prime_8312751159709 : Nat.Prime 8312751159709 := by
  apply nodeValid_prime [2, 3, 19, 97, 977, 384719] ⟨8312751159709, 6, [(2, 2), (3, 1), (19, 1), (97, 1), (977, 1), (384719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_97
    · exact prime_977
    · exact prime_384719
  · decide +kernel

theorem prime_8312751160859 : Nat.Prime 8312751160859 := by
  apply nodeValid_prime [2, 4156375580429] ⟨8312751160859, 2, [(2, 1), (4156375580429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4156375580429
  · decide +kernel

theorem prime_8312751161573 : Nat.Prime 8312751161573 := by
  apply nodeValid_prime [2, 11, 13, 401, 36241351] ⟨8312751161573, 2, [(2, 2), (11, 1), (13, 1), (401, 1), (36241351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_401
    · exact prime_36241351
  · decide +kernel

theorem prime_8318221613071 : Nat.Prime 8318221613071 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 383, 727, 3083] ⟨8318221613071, 6, [(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (383, 1), (727, 1), (3083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_383
    · exact prime_727
    · exact prime_3083
  · decide +kernel

theorem prime_8318221629253 : Nat.Prime 8318221629253 := by
  apply nodeValid_prime [2, 3, 41, 92233, 183307] ⟨8318221629253, 2, [(2, 2), (3, 1), (41, 1), (92233, 1), (183307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_92233
    · exact prime_183307
  · decide +kernel

theorem prime_8318221629677 : Nat.Prime 8318221629677 := by
  apply nodeValid_prime [2, 7, 19, 80077, 195259] ⟨8318221629677, 3, [(2, 2), (7, 1), (19, 1), (80077, 1), (195259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_80077
    · exact prime_195259
  · decide +kernel

theorem prime_8323694499677 : Nat.Prime 8323694499677 := by
  apply nodeValid_prime [2, 2080923624919] ⟨8323694499677, 2, [(2, 2), (2080923624919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2080923624919
  · decide +kernel

theorem prime_8323694544323 : Nat.Prime 8323694544323 := by
  apply nodeValid_prime [2, 773, 58321, 92317] ⟨8323694544323, 2, [(2, 1), (773, 1), (58321, 1), (92317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_773
    · exact prime_58321
    · exact prime_92317
  · decide +kernel

theorem prime_8323694544397 : Nat.Prime 8323694544397 := by
  apply nodeValid_prime [2, 3, 7, 11, 139, 64808111] ⟨8323694544397, 5, [(2, 2), (3, 1), (7, 1), (11, 1), (139, 1), (64808111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_139
    · exact prime_64808111
  · decide +kernel

end Sude.Lucas.Generated
