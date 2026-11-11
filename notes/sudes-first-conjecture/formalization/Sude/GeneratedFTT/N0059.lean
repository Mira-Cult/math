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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0057

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4657 : Nat.Prime 4657 := by
  apply nodeValid_prime [2, 3, 97] ⟨4657, 15, [(2, 4), (3, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
  · decide +kernel

theorem prime_10289 : Nat.Prime 10289 := by
  apply nodeValid_prime [2, 643] ⟨10289, 3, [(2, 4), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_643
  · decide +kernel

theorem prime_11083 : Nat.Prime 11083 := by
  apply nodeValid_prime [2, 3, 1847] ⟨11083, 2, [(2, 1), (3, 1), (1847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1847
  · decide +kernel

theorem prime_11131 : Nat.Prime 11131 := by
  apply nodeValid_prime [2, 3, 5, 7, 53] ⟨11131, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_12979 : Nat.Prime 12979 := by
  apply nodeValid_prime [2, 3, 7, 103] ⟨12979, 2, [(2, 1), (3, 2), (7, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_13367 : Nat.Prime 13367 := by
  apply nodeValid_prime [2, 41, 163] ⟨13367, 5, [(2, 1), (41, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_163
  · decide +kernel

theorem prime_15473 : Nat.Prime 15473 := by
  apply nodeValid_prime [2, 967] ⟨15473, 3, [(2, 4), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_967
  · decide +kernel

theorem prime_15913 : Nat.Prime 15913 := by
  apply nodeValid_prime [2, 3, 13, 17] ⟨15913, 5, [(2, 3), (3, 2), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_16963 : Nat.Prime 16963 := by
  apply nodeValid_prime [2, 3, 11, 257] ⟨16963, 2, [(2, 1), (3, 1), (11, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_257
  · decide +kernel

theorem prime_18131 : Nat.Prime 18131 := by
  apply nodeValid_prime [2, 5, 7, 37] ⟨18131, 7, [(2, 1), (5, 1), (7, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_18253 : Nat.Prime 18253 := by
  apply nodeValid_prime [2, 3, 13] ⟨18253, 5, [(2, 2), (3, 3), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_19889 : Nat.Prime 19889 := by
  apply nodeValid_prime [2, 11, 113] ⟨19889, 3, [(2, 4), (11, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
  · decide +kernel

theorem prime_23539 : Nat.Prime 23539 := by
  apply nodeValid_prime [2, 3, 3923] ⟨23539, 2, [(2, 1), (3, 1), (3923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3923
  · decide +kernel

theorem prime_23909 : Nat.Prime 23909 := by
  apply nodeValid_prime [2, 43, 139] ⟨23909, 2, [(2, 2), (43, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_139
  · decide +kernel

theorem prime_25033 : Nat.Prime 25033 := by
  apply nodeValid_prime [2, 3, 7, 149] ⟨25033, 5, [(2, 3), (3, 1), (7, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_27893 : Nat.Prime 27893 := by
  apply nodeValid_prime [2, 19, 367] ⟨27893, 2, [(2, 2), (19, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_367
  · decide +kernel

theorem prime_37549 : Nat.Prime 37549 := by
  apply nodeValid_prime [2, 3, 7, 149] ⟨37549, 2, [(2, 2), (3, 2), (7, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_39779 : Nat.Prime 39779 := by
  apply nodeValid_prime [2, 19889] ⟨39779, 2, [(2, 1), (19889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19889
  · decide +kernel

theorem prime_41263 : Nat.Prime 41263 := by
  apply nodeValid_prime [2, 3, 13, 23] ⟨41263, 5, [(2, 1), (3, 1), (13, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_44257 : Nat.Prime 44257 := by
  apply nodeValid_prime [2, 3, 461] ⟨44257, 5, [(2, 5), (3, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
  · decide +kernel

theorem prime_46691 : Nat.Prime 46691 := by
  apply nodeValid_prime [2, 5, 7, 23, 29] ⟨46691, 2, [(2, 1), (5, 1), (7, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_55511 : Nat.Prime 55511 := by
  apply nodeValid_prime [2, 5, 7, 13, 61] ⟨55511, 11, [(2, 1), (5, 1), (7, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_63103 : Nat.Prime 63103 := by
  apply nodeValid_prime [2, 3, 13, 809] ⟨63103, 3, [(2, 1), (3, 1), (13, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_809
  · decide +kernel

theorem prime_86011 : Nat.Prime 86011 := by
  apply nodeValid_prime [2, 3, 5, 47, 61] ⟨86011, 7, [(2, 1), (3, 1), (5, 1), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_88771 : Nat.Prime 88771 := by
  apply nodeValid_prime [2, 3, 5, 11, 269] ⟨88771, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_269
  · decide +kernel

theorem prime_89681 : Nat.Prime 89681 := by
  apply nodeValid_prime [2, 5, 19, 59] ⟨89681, 3, [(2, 4), (5, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_90619 : Nat.Prime 90619 := by
  apply nodeValid_prime [2, 3, 11, 1373] ⟨90619, 3, [(2, 1), (3, 1), (11, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1373
  · decide +kernel

theorem prime_93383 : Nat.Prime 93383 := by
  apply nodeValid_prime [2, 46691] ⟨93383, 5, [(2, 1), (46691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46691
  · decide +kernel

theorem prime_102797 : Nat.Prime 102797 := by
  apply nodeValid_prime [2, 31, 829] ⟨102797, 2, [(2, 2), (31, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_829
  · decide +kernel

theorem prime_104659 : Nat.Prime 104659 := by
  apply nodeValid_prime [2, 3, 17443] ⟨104659, 2, [(2, 1), (3, 1), (17443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17443
  · decide +kernel

theorem prime_115873 : Nat.Prime 115873 := by
  apply nodeValid_prime [2, 3, 17, 71] ⟨115873, 5, [(2, 5), (3, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_126097 : Nat.Prime 126097 := by
  apply nodeValid_prime [2, 3, 37, 71] ⟨126097, 5, [(2, 4), (3, 1), (37, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
  · decide +kernel

theorem prime_140761 : Nat.Prime 140761 := by
  apply nodeValid_prime [2, 3, 5, 17, 23] ⟨140761, 7, [(2, 3), (3, 2), (5, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_142789 : Nat.Prime 142789 := by
  apply nodeValid_prime [2, 3, 73, 163] ⟨142789, 2, [(2, 2), (3, 1), (73, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_163
  · decide +kernel

theorem prime_147557 : Nat.Prime 147557 := by
  apply nodeValid_prime [2, 37, 997] ⟨147557, 2, [(2, 2), (37, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_997
  · decide +kernel

theorem prime_150197 : Nat.Prime 150197 := by
  apply nodeValid_prime [2, 37549] ⟨150197, 2, [(2, 2), (37549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37549
  · decide +kernel

theorem prime_157561 : Nat.Prime 157561 := by
  apply nodeValid_prime [2, 3, 5, 13, 101] ⟨157561, 11, [(2, 3), (3, 1), (5, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_168247 : Nat.Prime 168247 := by
  apply nodeValid_prime [2, 3, 13, 719] ⟨168247, 3, [(2, 1), (3, 2), (13, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_719
  · decide +kernel

theorem prime_216259 : Nat.Prime 216259 := by
  apply nodeValid_prime [2, 3, 7, 19, 271] ⟨216259, 12, [(2, 1), (3, 1), (7, 1), (19, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_271
  · decide +kernel

theorem prime_246787 : Nat.Prime 246787 := by
  apply nodeValid_prime [2, 3, 41131] ⟨246787, 2, [(2, 1), (3, 1), (41131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41131
  · decide +kernel

theorem prime_267511 : Nat.Prime 267511 := by
  apply nodeValid_prime [2, 3, 5, 37, 241] ⟨267511, 3, [(2, 1), (3, 1), (5, 1), (37, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_241
  · decide +kernel

theorem prime_277217 : Nat.Prime 277217 := by
  apply nodeValid_prime [2, 8663] ⟨277217, 3, [(2, 5), (8663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8663
  · decide +kernel

theorem prime_288007 : Nat.Prime 288007 := by
  apply nodeValid_prime [2, 3, 23, 2087] ⟨288007, 5, [(2, 1), (3, 1), (23, 1), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2087
  · decide +kernel

theorem prime_305749 : Nat.Prime 305749 := by
  apply nodeValid_prime [2, 3, 19, 149] ⟨305749, 6, [(2, 2), (3, 3), (19, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_149
  · decide +kernel

theorem prime_381371 : Nat.Prime 381371 := by
  apply nodeValid_prime [2, 5, 11, 3467] ⟨381371, 2, [(2, 1), (5, 1), (11, 1), (3467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3467
  · decide +kernel

theorem prime_392351 : Nat.Prime 392351 := by
  apply nodeValid_prime [2, 5, 7, 19, 59] ⟨392351, 7, [(2, 1), (5, 2), (7, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_538051 : Nat.Prime 538051 := by
  apply nodeValid_prime [2, 3, 5, 17, 211] ⟨538051, 3, [(2, 1), (3, 1), (5, 2), (17, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_211
  · decide +kernel

theorem prime_584099 : Nat.Prime 584099 := by
  apply nodeValid_prime [2, 19, 809] ⟨584099, 2, [(2, 1), (19, 2), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_809
  · decide +kernel

theorem prime_595073 : Nat.Prime 595073 := by
  apply nodeValid_prime [2, 4649] ⟨595073, 3, [(2, 7), (4649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4649
  · decide +kernel

theorem prime_874967 : Nat.Prime 874967 := by
  apply nodeValid_prime [2, 23, 827] ⟨874967, 7, [(2, 1), (23, 2), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_827
  · decide +kernel

theorem prime_880951 : Nat.Prime 880951 := by
  apply nodeValid_prime [2, 3, 5, 7, 839] ⟨880951, 7, [(2, 1), (3, 1), (5, 2), (7, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_839
  · decide +kernel

theorem prime_889363 : Nat.Prime 889363 := by
  apply nodeValid_prime [2, 3, 49409] ⟨889363, 5, [(2, 1), (3, 2), (49409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49409
  · decide +kernel

theorem prime_912773 : Nat.Prime 912773 := by
  apply nodeValid_prime [2, 7, 4657] ⟨912773, 2, [(2, 2), (7, 2), (4657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4657
  · decide +kernel

theorem prime_966659 : Nat.Prime 966659 := by
  apply nodeValid_prime [2, 7, 11, 6277] ⟨966659, 2, [(2, 1), (7, 1), (11, 1), (6277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_6277
  · decide +kernel

theorem prime_1009483 : Nat.Prime 1009483 := by
  apply nodeValid_prime [2, 3, 168247] ⟨1009483, 2, [(2, 1), (3, 1), (168247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_168247
  · decide +kernel

theorem prime_1009649 : Nat.Prime 1009649 := by
  apply nodeValid_prime [2, 63103] ⟨1009649, 3, [(2, 4), (63103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63103
  · decide +kernel

theorem prime_1378777 : Nat.Prime 1378777 := by
  apply nodeValid_prime [2, 3, 7, 29, 283] ⟨1378777, 15, [(2, 3), (3, 1), (7, 1), (29, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_283
  · decide +kernel

theorem prime_1491683 : Nat.Prime 1491683 := by
  apply nodeValid_prime [2, 17, 73, 601] ⟨1491683, 2, [(2, 1), (17, 1), (73, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_73
    · exact prime_601
  · decide +kernel

theorem prime_1764733 : Nat.Prime 1764733 := by
  apply nodeValid_prime [2, 3, 199, 739] ⟨1764733, 5, [(2, 2), (3, 1), (199, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_739
  · decide +kernel

theorem prime_1932421 : Nat.Prime 1932421 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 107] ⟨1932421, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_107
  · decide +kernel

theorem prime_2065799 : Nat.Prime 2065799 := by
  apply nodeValid_prime [2, 7, 147557] ⟨2065799, 7, [(2, 1), (7, 1), (147557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_147557
  · decide +kernel

theorem prime_2537869 : Nat.Prime 2537869 := by
  apply nodeValid_prime [2, 3, 19, 11131] ⟨2537869, 7, [(2, 2), (3, 1), (19, 1), (11131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11131
  · decide +kernel

theorem prime_2983367 : Nat.Prime 2983367 := by
  apply nodeValid_prime [2, 1491683] ⟨2983367, 5, [(2, 1), (1491683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1491683
  · decide +kernel

theorem prime_4037933 : Nat.Prime 4037933 := by
  apply nodeValid_prime [2, 1009483] ⟨4037933, 2, [(2, 2), (1009483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1009483
  · decide +kernel

theorem prime_4884059 : Nat.Prime 4884059 := by
  apply nodeValid_prime [2, 193, 12653] ⟨4884059, 2, [(2, 1), (193, 1), (12653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_12653
  · decide +kernel

theorem prime_5856457 : Nat.Prime 5856457 := by
  apply nodeValid_prime [2, 3, 239, 1021] ⟨5856457, 5, [(2, 3), (3, 1), (239, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_1021
  · decide +kernel

theorem prime_6080761 : Nat.Prime 6080761 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 127] ⟨6080761, 34, [(2, 3), (3, 2), (5, 1), (7, 1), (19, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_127
  · decide +kernel

theorem prime_7123099 : Nat.Prime 7123099 := by
  apply nodeValid_prime [2, 3, 97, 12239] ⟨7123099, 2, [(2, 1), (3, 1), (97, 1), (12239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_12239
  · decide +kernel

theorem prime_7202963 : Nat.Prime 7202963 := by
  apply nodeValid_prime [2, 13, 29, 41, 233] ⟨7202963, 2, [(2, 1), (13, 1), (29, 1), (41, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_41
    · exact prime_233
  · decide +kernel

theorem prime_9768119 : Nat.Prime 9768119 := by
  apply nodeValid_prime [2, 4884059] ⟨9768119, 7, [(2, 1), (4884059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4884059
  · decide +kernel

theorem prime_10781497 : Nat.Prime 10781497 := by
  apply nodeValid_prime [2, 3, 11, 13613] ⟨10781497, 5, [(2, 3), (3, 2), (11, 1), (13613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13613
  · decide +kernel

theorem prime_13180339 : Nat.Prime 13180339 := by
  apply nodeValid_prime [2, 3, 17, 19, 2267] ⟨13180339, 7, [(2, 1), (3, 2), (17, 1), (19, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_2267
  · decide +kernel

theorem prime_19008463 : Nat.Prime 19008463 := by
  apply nodeValid_prime [2, 3, 11, 288007] ⟨19008463, 11, [(2, 1), (3, 1), (11, 1), (288007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_288007
  · decide +kernel

theorem prime_25822733 : Nat.Prime 25822733 := by
  apply nodeValid_prime [2, 13, 157, 3163] ⟨25822733, 2, [(2, 2), (13, 1), (157, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_157
    · exact prime_3163
  · decide +kernel

theorem prime_28273013 : Nat.Prime 28273013 := by
  apply nodeValid_prime [2, 61, 115873] ⟨28273013, 2, [(2, 2), (61, 1), (115873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_115873
  · decide +kernel

theorem prime_34138903 : Nat.Prime 34138903 := by
  apply nodeValid_prime [2, 3, 7, 79, 10289] ⟨34138903, 3, [(2, 1), (3, 1), (7, 1), (79, 1), (10289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_10289
  · decide +kernel

theorem prime_35138743 : Nat.Prime 35138743 := by
  apply nodeValid_prime [2, 3, 5856457] ⟨35138743, 3, [(2, 1), (3, 1), (5856457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5856457
  · decide +kernel

theorem prime_38323163 : Nat.Prime 38323163 := by
  apply nodeValid_prime [2, 1609, 11909] ⟨38323163, 2, [(2, 1), (1609, 1), (11909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1609
    · exact prime_11909
  · decide +kernel

theorem prime_39880213 : Nat.Prime 39880213 := by
  apply nodeValid_prime [2, 3, 139, 23909] ⟨39880213, 2, [(2, 2), (3, 1), (139, 1), (23909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_23909
  · decide +kernel

theorem prime_60908857 : Nat.Prime 60908857 := by
  apply nodeValid_prime [2, 3, 2537869] ⟨60908857, 5, [(2, 3), (3, 1), (2537869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2537869
  · decide +kernel

theorem prime_85241573 : Nat.Prime 85241573 := by
  apply nodeValid_prime [2, 13, 126097] ⟨85241573, 2, [(2, 2), (13, 2), (126097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_126097
  · decide +kernel

theorem prime_93209551 : Nat.Prime 93209551 := by
  apply nodeValid_prime [2, 3, 5, 7, 88771] ⟨93209551, 6, [(2, 1), (3, 1), (5, 2), (7, 1), (88771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_88771
  · decide +kernel

theorem prime_97303049 : Nat.Prime 97303049 := by
  apply nodeValid_prime [2, 31, 392351] ⟨97303049, 3, [(2, 3), (31, 1), (392351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_392351
  · decide +kernel

theorem prime_99239431 : Nat.Prime 99239431 := by
  apply nodeValid_prime [2, 3, 5, 1181, 2801] ⟨99239431, 6, [(2, 1), (3, 1), (5, 1), (1181, 1), (2801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1181
    · exact prime_2801
  · decide +kernel

theorem prime_171100219 : Nat.Prime 171100219 := by
  apply nodeValid_prime [2, 3, 53, 538051] ⟨171100219, 10, [(2, 1), (3, 1), (53, 1), (538051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_538051
  · decide +kernel

theorem prime_293086513 : Nat.Prime 293086513 := by
  apply nodeValid_prime [2, 3, 59, 3833] ⟨293086513, 5, [(2, 4), (3, 4), (59, 1), (3833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_3833
  · decide +kernel

theorem prime_293278177 : Nat.Prime 293278177 := by
  apply nodeValid_prime [2, 3, 83, 12269] ⟨293278177, 10, [(2, 5), (3, 2), (83, 1), (12269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_12269
  · decide +kernel

theorem prime_312585547 : Nat.Prime 312585547 := by
  apply nodeValid_prime [2, 3, 7, 13, 37, 15473] ⟨312585547, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (37, 1), (15473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_15473
  · decide +kernel

theorem prime_456203113 : Nat.Prime 456203113 := by
  apply nodeValid_prime [2, 3, 19008463] ⟨456203113, 5, [(2, 3), (3, 1), (19008463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19008463
  · decide +kernel

theorem prime_478191437 : Nat.Prime 478191437 := by
  apply nodeValid_prime [2, 17, 23, 305749] ⟨478191437, 2, [(2, 2), (17, 1), (23, 1), (305749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_305749
  · decide +kernel

theorem prime_481396183 : Nat.Prime 481396183 := by
  apply nodeValid_prime [2, 3, 83, 966659] ⟨481396183, 7, [(2, 1), (3, 1), (83, 1), (966659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_966659
  · decide +kernel

theorem prime_496194947 : Nat.Prime 496194947 := by
  apply nodeValid_prime [2, 13, 17, 941, 1193] ⟨496194947, 2, [(2, 1), (13, 1), (17, 1), (941, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_941
    · exact prime_1193
  · decide +kernel

theorem prime_700860731 : Nat.Prime 700860731 := by
  apply nodeValid_prime [2, 5, 6379, 10987] ⟨700860731, 2, [(2, 1), (5, 1), (6379, 1), (10987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6379
    · exact prime_10987
  · decide +kernel

theorem prime_817324237 : Nat.Prime 817324237 := by
  apply nodeValid_prime [2, 3, 53, 142789] ⟨817324237, 2, [(2, 2), (3, 3), (53, 1), (142789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_142789
  · decide +kernel

theorem prime_829689691 : Nat.Prime 829689691 := by
  apply nodeValid_prime [2, 3, 5, 2069, 13367] ⟨829689691, 2, [(2, 1), (3, 1), (5, 1), (2069, 1), (13367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2069
    · exact prime_13367
  · decide +kernel

theorem prime_1229090659 : Nat.Prime 1229090659 := by
  apply nodeValid_prime [2, 3, 19, 10781497] ⟨1229090659, 11, [(2, 1), (3, 1), (19, 1), (10781497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_10781497
  · decide +kernel

theorem prime_2194312633 : Nat.Prime 2194312633 := by
  apply nodeValid_prime [2, 3, 1063, 86011] ⟨2194312633, 5, [(2, 3), (3, 1), (1063, 1), (86011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1063
    · exact prime_86011
  · decide +kernel

theorem prime_2227131133 : Nat.Prime 2227131133 := by
  apply nodeValid_prime [2, 3, 19, 9768119] ⟨2227131133, 5, [(2, 2), (3, 1), (19, 1), (9768119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_9768119
  · decide +kernel

theorem prime_2670781453 : Nat.Prime 2670781453 := by
  apply nodeValid_prime [2, 3, 211, 409, 2579] ⟨2670781453, 2, [(2, 2), (3, 1), (211, 1), (409, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_409
    · exact prime_2579
  · decide +kernel

theorem prime_3233723869 : Nat.Prime 3233723869 := by
  apply nodeValid_prime [2, 3, 101, 889363] ⟨3233723869, 6, [(2, 2), (3, 2), (101, 1), (889363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_889363
  · decide +kernel

theorem prime_3258361481 : Nat.Prime 3258361481 := by
  apply nodeValid_prime [2, 5, 11, 47, 157561] ⟨3258361481, 3, [(2, 3), (5, 1), (11, 1), (47, 1), (157561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
    · exact prime_157561
  · decide +kernel

theorem prime_3662031713 : Nat.Prime 3662031713 := by
  apply nodeValid_prime [2, 83, 1378777] ⟨3662031713, 3, [(2, 5), (83, 1), (1378777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_1378777
  · decide +kernel

theorem prime_4028499511 : Nat.Prime 4028499511 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 1009649] ⟨4028499511, 12, [(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (1009649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_1009649
  · decide +kernel

theorem prime_4919100371 : Nat.Prime 4919100371 := by
  apply nodeValid_prime [2, 5, 47, 617, 16963] ⟨4919100371, 2, [(2, 1), (5, 1), (47, 1), (617, 1), (16963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_617
    · exact prime_16963
  · decide +kernel

theorem prime_5219980357 : Nat.Prime 5219980357 := by
  apply nodeValid_prime [2, 3, 17, 43, 595073] ⟨5219980357, 6, [(2, 2), (3, 1), (17, 1), (43, 1), (595073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_595073
  · decide +kernel

theorem prime_7670957299 : Nat.Prime 7670957299 := by
  apply nodeValid_prime [2, 3, 97, 13180339] ⟨7670957299, 10, [(2, 1), (3, 1), (97, 1), (13180339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_13180339
  · decide +kernel

theorem prime_15020598623 : Nat.Prime 15020598623 := by
  apply nodeValid_prime [2, 137, 769, 71287] ⟨15020598623, 5, [(2, 1), (137, 1), (769, 1), (71287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_769
    · exact prime_71287
  · decide +kernel

theorem prime_22953188977 : Nat.Prime 22953188977 := by
  apply nodeValid_prime [2, 3, 478191437] ⟨22953188977, 7, [(2, 4), (3, 1), (478191437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_478191437
  · decide +kernel

theorem prime_26398251829 : Nat.Prime 26398251829 := by
  apply nodeValid_prime [2, 3, 13, 1367, 41263] ⟨26398251829, 2, [(2, 2), (3, 2), (13, 1), (1367, 1), (41263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1367
    · exact prime_41263
  · decide +kernel

theorem prime_30759151831 : Nat.Prime 30759151831 := by
  apply nodeValid_prime [2, 3, 5, 11, 93209551] ⟨30759151831, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (93209551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_93209551
  · decide +kernel

theorem prime_41789082407 : Nat.Prime 41789082407 := by
  apply nodeValid_prime [2, 17, 1229090659] ⟨41789082407, 5, [(2, 1), (17, 1), (1229090659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1229090659
  · decide +kernel

theorem prime_185020801087 : Nat.Prime 185020801087 := by
  apply nodeValid_prime [2, 3, 11, 113, 1559, 15913] ⟨185020801087, 11, [(2, 1), (3, 1), (11, 1), (113, 1), (1559, 1), (15913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
    · exact prime_1559
    · exact prime_15913
  · decide +kernel

theorem prime_269909466941 : Nat.Prime 269909466941 := by
  apply nodeValid_prime [2, 5, 401, 2593, 12979] ⟨269909466941, 2, [(2, 2), (5, 1), (401, 1), (2593, 1), (12979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_401
    · exact prime_2593
    · exact prime_12979
  · decide +kernel

theorem prime_539818933883 : Nat.Prime 539818933883 := by
  apply nodeValid_prime [2, 269909466941] ⟨539818933883, 2, [(2, 1), (269909466941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_269909466941
  · decide +kernel

theorem prime_548791611383 : Nat.Prime 548791611383 := by
  apply nodeValid_prime [2, 7, 79, 496194947] ⟨548791611383, 5, [(2, 1), (7, 1), (79, 1), (496194947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_496194947
  · decide +kernel

theorem prime_1079637867767 : Nat.Prime 1079637867767 := by
  apply nodeValid_prime [2, 539818933883] ⟨1079637867767, 5, [(2, 1), (539818933883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_539818933883
  · decide +kernel

theorem prime_1079637868541 : Nat.Prime 1079637868541 := by
  apply nodeValid_prime [2, 5, 7, 11, 41, 2423, 7057] ⟨1079637868541, 3, [(2, 2), (5, 1), (7, 1), (11, 1), (41, 1), (2423, 1), (7057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_41
    · exact prime_2423
    · exact prime_7057
  · decide +kernel

theorem prime_1079637868949 : Nat.Prime 1079637868949 := by
  apply nodeValid_prime [2, 67, 4028499511] ⟨1079637868949, 2, [(2, 2), (67, 1), (4028499511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_4028499511
  · decide +kernel

theorem prime_1081011183643 : Nat.Prime 1081011183643 := by
  apply nodeValid_prime [2, 3, 13, 171100219] ⟨1081011183643, 3, [(2, 1), (3, 5), (13, 1), (171100219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_171100219
  · decide +kernel

theorem prime_1081011195163 : Nat.Prime 1081011195163 := by
  apply nodeValid_prime [2, 3, 107, 139, 4037933] ⟨1081011195163, 3, [(2, 1), (3, 2), (107, 1), (139, 1), (4037933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_139
    · exact prime_4037933
  · decide +kernel

theorem prime_1081011196061 : Nat.Prime 1081011196061 := by
  apply nodeValid_prime [2, 5, 29, 18131, 102797] ⟨1081011196061, 3, [(2, 2), (5, 1), (29, 1), (18131, 1), (102797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_18131
    · exact prime_102797
  · decide +kernel

theorem prime_1082385676429 : Nat.Prime 1082385676429 := by
  apply nodeValid_prime [2, 3, 7, 499, 25822733] ⟨1082385676429, 6, [(2, 2), (3, 1), (7, 1), (499, 1), (25822733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_499
    · exact prime_25822733
  · decide +kernel

theorem prime_1082385730639 : Nat.Prime 1082385730639 := by
  apply nodeValid_prime [2, 3, 2227131133] ⟨1082385730639, 3, [(2, 1), (3, 5), (2227131133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2227131133
  · decide +kernel

theorem prime_1082385731857 : Nat.Prime 1082385731857 := by
  apply nodeValid_prime [2, 3, 11, 13, 179, 880951] ⟨1082385731857, 7, [(2, 4), (3, 1), (11, 1), (13, 1), (179, 1), (880951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_179
    · exact prime_880951
  · decide +kernel

theorem prime_1083761359123 : Nat.Prime 1083761359123 := by
  apply nodeValid_prime [2, 3, 13, 163, 85241573] ⟨1083761359123, 2, [(2, 1), (3, 1), (13, 1), (163, 1), (85241573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_163
    · exact prime_85241573
  · decide +kernel

theorem prime_1083761359427 : Nat.Prime 1083761359427 := by
  apply nodeValid_prime [2, 67, 4583, 1764733] ⟨1083761359427, 2, [(2, 1), (67, 1), (4583, 1), (1764733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_4583
    · exact prime_1764733
  · decide +kernel

theorem prime_1083761359763 : Nat.Prime 1083761359763 := by
  apply nodeValid_prime [2, 5569, 97303049] ⟨1083761359763, 2, [(2, 1), (5569, 1), (97303049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5569
    · exact prime_97303049
  · decide +kernel

theorem prime_1085138224801 : Nat.Prime 1085138224801 := by
  apply nodeValid_prime [2, 3, 5, 7, 233, 277217] ⟨1085138224801, 23, [(2, 5), (3, 1), (5, 2), (7, 1), (233, 1), (277217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_233
    · exact prime_277217
  · decide +kernel

theorem prime_1085138233369 : Nat.Prime 1085138233369 := by
  apply nodeValid_prime [2, 3, 7, 3739, 246787] ⟨1085138233369, 13, [(2, 3), (3, 1), (7, 2), (3739, 1), (246787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3739
    · exact prime_246787
  · decide +kernel

theorem prime_1086516141593 : Nat.Prime 1086516141593 := by
  apply nodeValid_prime [2, 7, 29, 97, 140761] ⟨1086516141593, 3, [(2, 3), (7, 3), (29, 1), (97, 1), (140761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_97
    · exact prime_140761
  · decide +kernel

theorem prime_1086516142583 : Nat.Prime 1086516142583 := by
  apply nodeValid_prime [2, 13, 41789082407] ⟨1086516142583, 5, [(2, 1), (13, 1), (41789082407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41789082407
  · decide +kernel

theorem prime_1086516275759 : Nat.Prime 1086516275759 := by
  apply nodeValid_prime [2, 149, 479, 941, 8089] ⟨1086516275759, 13, [(2, 1), (149, 1), (479, 1), (941, 1), (8089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_479
    · exact prime_941
    · exact prime_8089
  · decide +kernel

theorem prime_1087895483281 : Nat.Prime 1087895483281 := by
  apply nodeValid_prime [2, 3, 5, 43, 35138743] ⟨1087895483281, 7, [(2, 4), (3, 2), (5, 1), (43, 1), (35138743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_35138743
  · decide +kernel

theorem prime_1087895484451 : Nat.Prime 1087895484451 := by
  apply nodeValid_prime [2, 3, 5, 1301, 2549] ⟨1087895484451, 10, [(2, 1), (3, 8), (5, 2), (1301, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1301
    · exact prime_2549
  · decide +kernel

theorem prime_1087895505209 : Nat.Prime 1087895505209 := by
  apply nodeValid_prime [2, 1801, 2707, 27893] ⟨1087895505209, 3, [(2, 3), (1801, 1), (2707, 1), (27893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1801
    · exact prime_2707
    · exact prime_27893
  · decide +kernel

theorem prime_1089275915011 : Nat.Prime 1089275915011 := by
  apply nodeValid_prime [2, 3, 5, 39779, 912773] ⟨1089275915011, 2, [(2, 1), (3, 1), (5, 1), (39779, 1), (912773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_39779
    · exact prime_912773
  · decide +kernel

theorem prime_1089275934431 : Nat.Prime 1089275934431 := by
  apply nodeValid_prime [2, 5, 613, 7549, 23539] ⟨1089275934431, 11, [(2, 1), (5, 1), (613, 1), (7549, 1), (23539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_613
    · exact prime_7549
    · exact prime_23539
  · decide +kernel

theorem prime_1089275936459 : Nat.Prime 1089275936459 := by
  apply nodeValid_prime [2, 71, 7670957299] ⟨1089275936459, 2, [(2, 1), (71, 1), (7670957299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_7670957299
  · decide +kernel

theorem prime_1090657454191 : Nat.Prime 1090657454191 := by
  apply nodeValid_prime [2, 3, 5, 127, 15683, 18253] ⟨1090657454191, 12, [(2, 1), (3, 1), (5, 1), (127, 1), (15683, 1), (18253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
    · exact prime_15683
    · exact prime_18253
  · decide +kernel

theorem prime_1090657454483 : Nat.Prime 1090657454483 := by
  apply nodeValid_prime [2, 89681, 6080761] ⟨1090657454483, 2, [(2, 1), (89681, 1), (6080761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89681
    · exact prime_6080761
  · decide +kernel

theorem prime_1090657511231 : Nat.Prime 1090657511231 := by
  apply nodeValid_prime [2, 5, 7, 17, 577, 797, 1993] ⟨1090657511231, 7, [(2, 1), (5, 1), (7, 1), (17, 1), (577, 1), (797, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_577
    · exact prime_797
    · exact prime_1993
  · decide +kernel

theorem prime_1092040282363 : Nat.Prime 1092040282363 := by
  apply nodeValid_prime [2, 3, 37, 4919100371] ⟨1092040282363, 3, [(2, 1), (3, 1), (37, 1), (4919100371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4919100371
  · decide +kernel

theorem prime_1092040347439 : Nat.Prime 1092040347439 := by
  apply nodeValid_prime [2, 3, 23, 293086513] ⟨1092040347439, 6, [(2, 1), (3, 4), (23, 1), (293086513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_293086513
  · decide +kernel

theorem prime_1093424188897 : Nat.Prime 1093424188897 := by
  apply nodeValid_prime [2, 3, 13, 41, 7123099] ⟨1093424188897, 7, [(2, 5), (3, 2), (13, 1), (41, 1), (7123099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_7123099
  · decide +kernel

theorem prime_1093424189327 : Nat.Prime 1093424189327 := by
  apply nodeValid_prime [2, 7, 1549, 7202963] ⟨1093424189327, 5, [(2, 1), (7, 2), (1549, 1), (7202963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1549
    · exact prime_7202963
  · decide +kernel

theorem prime_1093424243407 : Nat.Prime 1093424243407 := by
  apply nodeValid_prime [2, 3, 11, 53, 312585547] ⟨1093424243407, 5, [(2, 1), (3, 1), (11, 1), (53, 1), (312585547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_312585547
  · decide +kernel

theorem prime_1094809402793 : Nat.Prime 1094809402793 := by
  apply nodeValid_prime [2, 7, 197, 99239431] ⟨1094809402793, 3, [(2, 3), (7, 1), (197, 1), (99239431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_197
    · exact prime_99239431
  · decide +kernel

theorem prime_1094809457617 : Nat.Prime 1094809457617 := by
  apply nodeValid_prime [2, 3, 7, 3258361481] ⟨1094809457617, 10, [(2, 4), (3, 1), (7, 1), (3258361481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3258361481
  · decide +kernel

theorem prime_1094809458487 : Nat.Prime 1094809458487 := by
  apply nodeValid_prime [2, 3, 107, 1949, 874967] ⟨1094809458487, 3, [(2, 1), (3, 1), (107, 1), (1949, 1), (874967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_1949
    · exact prime_874967
  · decide +kernel

theorem prime_1096195754453 : Nat.Prime 1096195754453 := by
  apply nodeValid_prime [2, 7151, 38323163] ⟨1096195754453, 2, [(2, 2), (7151, 1), (38323163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7151
    · exact prime_38323163
  · decide +kernel

theorem prime_1096195874971 : Nat.Prime 1096195874971 := by
  apply nodeValid_prime [2, 3, 5, 7, 5219980357] ⟨1096195874971, 12, [(2, 1), (3, 1), (5, 1), (7, 1), (5219980357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_5219980357
  · decide +kernel

theorem prime_1096195875361 : Nat.Prime 1096195875361 := by
  apply nodeValid_prime [2, 3, 5, 8537, 267511] ⟨1096195875361, 17, [(2, 5), (3, 1), (5, 1), (8537, 1), (267511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8537
    · exact prime_267511
  · decide +kernel

theorem prime_1097583222187 : Nat.Prime 1097583222187 := by
  apply nodeValid_prime [2, 3, 11, 139, 39880213] ⟨1097583222187, 2, [(2, 1), (3, 2), (11, 1), (139, 1), (39880213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
    · exact prime_39880213
  · decide +kernel

theorem prime_1097583222767 : Nat.Prime 1097583222767 := by
  apply nodeValid_prime [2, 548791611383] ⟨1097583222767, 5, [(2, 1), (548791611383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_548791611383
  · decide +kernel

theorem prime_1097583297241 : Nat.Prime 1097583297241 := by
  apply nodeValid_prime [2, 3, 5, 19, 481396183] ⟨1097583297241, 22, [(2, 3), (3, 1), (5, 1), (19, 1), (481396183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_481396183
  · decide +kernel

theorem prime_1098972015217 : Nat.Prime 1098972015217 := by
  apply nodeValid_prime [2, 3, 11083, 2065799] ⟨1098972015217, 7, [(2, 4), (3, 1), (11083, 1), (2065799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11083
    · exact prime_2065799
  · decide +kernel

theorem prime_1098972015311 : Nat.Prime 1098972015311 := by
  apply nodeValid_prime [2, 5, 13, 23, 28273013] ⟨1098972015311, 7, [(2, 1), (5, 1), (13, 2), (23, 1), (28273013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_28273013
  · decide +kernel

theorem prime_1098972032687 : Nat.Prime 1098972032687 := by
  apply nodeValid_prime [2, 11, 29, 38921, 44257] ⟨1098972032687, 5, [(2, 1), (11, 1), (29, 1), (38921, 1), (44257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_38921
    · exact prime_44257
  · decide +kernel

theorem prime_1100361908557 : Nat.Prime 1100361908557 := by
  apply nodeValid_prime [2, 3, 67, 456203113] ⟨1100361908557, 2, [(2, 2), (3, 2), (67, 1), (456203113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_456203113
  · decide +kernel

theorem prime_1100361910339 : Nat.Prime 1100361910339 := by
  apply nodeValid_prime [2, 3, 104659, 584099] ⟨1100361910339, 2, [(2, 1), (3, 2), (104659, 1), (584099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_104659
    · exact prime_584099
  · decide +kernel

theorem prime_1100361958637 : Nat.Prime 1100361958637 := by
  apply nodeValid_prime [2, 103, 2670781453] ⟨1100361958637, 2, [(2, 2), (103, 1), (2670781453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_2670781453
  · decide +kernel

theorem prime_1101753069133 : Nat.Prime 1101753069133 := by
  apply nodeValid_prime [2, 3, 131, 700860731] ⟨1101753069133, 5, [(2, 2), (3, 1), (131, 1), (700860731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_700860731
  · decide +kernel

theorem prime_1101753070897 : Nat.Prime 1101753070897 := by
  apply nodeValid_prime [2, 3, 22953188977] ⟨1101753070897, 5, [(2, 4), (3, 1), (22953188977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22953188977
  · decide +kernel

theorem prime_1101753071477 : Nat.Prime 1101753071477 := by
  apply nodeValid_prime [2, 337, 817324237] ⟨1101753071477, 2, [(2, 2), (337, 1), (817324237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_817324237
  · decide +kernel

theorem prime_1103145365029 : Nat.Prime 1103145365029 := by
  apply nodeValid_prime [2, 3, 7, 967, 1033, 13147] ⟨1103145365029, 2, [(2, 2), (3, 1), (7, 1), (967, 1), (1033, 1), (13147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_967
    · exact prime_1033
    · exact prime_13147
  · decide +kernel

theorem prime_1103145366553 : Nat.Prime 1103145366553 := by
  apply nodeValid_prime [2, 3, 23, 101, 3593, 5507] ⟨1103145366553, 5, [(2, 3), (3, 1), (23, 1), (101, 1), (3593, 1), (5507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_101
    · exact prime_3593
    · exact prime_5507
  · decide +kernel

theorem prime_1103145376843 : Nat.Prime 1103145376843 := by
  apply nodeValid_prime [2, 3, 53, 5347, 216259] ⟨1103145376843, 2, [(2, 1), (3, 2), (53, 1), (5347, 1), (216259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_5347
    · exact prime_216259
  · decide +kernel

theorem prime_1104538880443 : Nat.Prime 1104538880443 := by
  apply nodeValid_prime [2, 3, 227, 367, 661, 3343] ⟨1104538880443, 3, [(2, 1), (3, 1), (227, 1), (367, 1), (661, 1), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_367
    · exact prime_661
    · exact prime_3343
  · decide +kernel

theorem prime_1104538893239 : Nat.Prime 1104538893239 := by
  apply nodeValid_prime [2, 11, 829, 1091, 55511] ⟨1104538893239, 11, [(2, 1), (11, 1), (829, 1), (1091, 1), (55511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_829
    · exact prime_1091
    · exact prime_55511
  · decide +kernel

theorem prime_1104538894073 : Nat.Prime 1104538894073 := by
  apply nodeValid_prime [2, 71, 5099, 381371] ⟨1104538894073, 3, [(2, 3), (71, 1), (5099, 1), (381371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_5099
    · exact prime_381371
  · decide +kernel

theorem prime_1105933563199 : Nat.Prime 1105933563199 := by
  apply nodeValid_prime [2, 3, 19, 3233723869] ⟨1105933563199, 3, [(2, 1), (3, 2), (19, 1), (3233723869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3233723869
  · decide +kernel

theorem prime_1105933567033 : Nat.Prime 1105933567033 := by
  apply nodeValid_prime [2, 3, 7, 2194312633] ⟨1105933567033, 10, [(2, 3), (3, 2), (7, 1), (2194312633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2194312633
  · decide +kernel

theorem prime_1105933577327 : Nat.Prime 1105933577327 := by
  apply nodeValid_prime [2, 151, 3662031713] ⟨1105933577327, 5, [(2, 1), (151, 1), (3662031713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_3662031713
  · decide +kernel

theorem prime_1107329457277 : Nat.Prime 1107329457277 := by
  apply nodeValid_prime [2, 3, 7, 23, 149, 157, 8167] ⟨1107329457277, 6, [(2, 2), (3, 2), (7, 1), (23, 1), (149, 1), (157, 1), (8167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_149
    · exact prime_157
    · exact prime_8167
  · decide +kernel

theorem prime_1107329457709 : Nat.Prime 1107329457709 := by
  apply nodeValid_prime [2, 3, 17, 53, 34138903] ⟨1107329457709, 6, [(2, 2), (3, 2), (17, 1), (53, 1), (34138903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_53
    · exact prime_34138903
  · decide +kernel

theorem prime_1107329465917 : Nat.Prime 1107329465917 := by
  apply nodeValid_prime [2, 3, 30759151831] ⟨1107329465917, 2, [(2, 2), (3, 2), (30759151831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30759151831
  · decide +kernel

theorem prime_1108726548751 : Nat.Prime 1108726548751 := by
  apply nodeValid_prime [2, 3, 5, 17, 1932421] ⟨1108726548751, 3, [(2, 1), (3, 3), (5, 4), (17, 1), (1932421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1932421
  · decide +kernel

theorem prime_1108726576819 : Nat.Prime 1108726576819 := by
  apply nodeValid_prime [2, 3, 7, 26398251829] ⟨1108726576819, 2, [(2, 1), (3, 1), (7, 1), (26398251829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_26398251829
  · decide +kernel

theorem prime_1108726578413 : Nat.Prime 1108726578413 := by
  apply nodeValid_prime [2, 53, 1753, 2983367] ⟨1108726578413, 2, [(2, 2), (53, 1), (1753, 1), (2983367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1753
    · exact prime_2983367
  · decide +kernel

theorem prime_1110124806523 : Nat.Prime 1110124806523 := by
  apply nodeValid_prime [2, 3, 185020801087] ⟨1110124806523, 2, [(2, 1), (3, 1), (185020801087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_185020801087
  · decide +kernel

theorem prime_1110124806559 : Nat.Prime 1110124806559 := by
  apply nodeValid_prime [2, 3, 223, 829689691] ⟨1110124806559, 3, [(2, 1), (3, 1), (223, 1), (829689691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_829689691
  · decide +kernel

theorem prime_1110124827683 : Nat.Prime 1110124827683 := by
  apply nodeValid_prime [2, 13, 701, 60908857] ⟨1110124827683, 2, [(2, 1), (13, 1), (701, 1), (60908857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_701
    · exact prime_60908857
  · decide +kernel

theorem prime_1111524290831 : Nat.Prime 1111524290831 := by
  apply nodeValid_prime [2, 5, 379, 293278177] ⟨1111524290831, 13, [(2, 1), (5, 1), (379, 1), (293278177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_379
    · exact prime_293278177
  · decide +kernel

theorem prime_1111524291959 : Nat.Prime 1111524291959 := by
  apply nodeValid_prime [2, 4523, 7867, 15619] ⟨1111524291959, 7, [(2, 1), (4523, 1), (7867, 1), (15619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_4523
    · exact prime_7867
    · exact prime_15619
  · decide +kernel

theorem prime_1111524298103 : Nat.Prime 1111524298103 := by
  apply nodeValid_prime [2, 37, 15020598623] ⟨1111524298103, 5, [(2, 1), (37, 1), (15020598623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_15020598623
  · decide +kernel

theorem prime_1112924924297 : Nat.Prime 1112924924297 := by
  apply nodeValid_prime [2, 37, 25033, 150197] ⟨1112924924297, 3, [(2, 3), (37, 1), (25033, 1), (150197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_25033
    · exact prime_150197
  · decide +kernel

theorem prime_1112924924317 : Nat.Prime 1112924924317 := by
  apply nodeValid_prime [2, 3, 97, 3517, 90619] ⟨1112924924317, 2, [(2, 2), (3, 2), (97, 1), (3517, 1), (90619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_3517
    · exact prime_90619
  · decide +kernel

theorem prime_1112924960083 : Nat.Prime 1112924960083 := by
  apply nodeValid_prime [2, 3, 13, 5659, 93383] ⟨1112924960083, 3, [(2, 1), (3, 4), (13, 1), (5659, 1), (93383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5659
    · exact prime_93383
  · decide +kernel

end Sude.Lucas.Generated
