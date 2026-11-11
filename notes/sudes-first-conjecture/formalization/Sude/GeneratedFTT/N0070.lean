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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0062

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9043 : Nat.Prime 9043 := by
  apply nodeValid_prime [2, 3, 11, 137] ⟨9043, 3, [(2, 1), (3, 1), (11, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
  · decide +kernel

theorem prime_10181 : Nat.Prime 10181 := by
  apply nodeValid_prime [2, 5, 509] ⟨10181, 2, [(2, 2), (5, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_509
  · decide +kernel

theorem prime_10847 : Nat.Prime 10847 := by
  apply nodeValid_prime [2, 11, 17, 29] ⟨10847, 5, [(2, 1), (11, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_12143 : Nat.Prime 12143 := by
  apply nodeValid_prime [2, 13, 467] ⟨12143, 10, [(2, 1), (13, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_467
  · decide +kernel

theorem prime_13267 : Nat.Prime 13267 := by
  apply nodeValid_prime [2, 3, 11, 67] ⟨13267, 3, [(2, 1), (3, 2), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_15797 : Nat.Prime 15797 := by
  apply nodeValid_prime [2, 11, 359] ⟨15797, 2, [(2, 2), (11, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_359
  · decide +kernel

theorem prime_18097 : Nat.Prime 18097 := by
  apply nodeValid_prime [2, 3, 13, 29] ⟨18097, 5, [(2, 4), (3, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_18793 : Nat.Prime 18793 := by
  apply nodeValid_prime [2, 3, 29] ⟨18793, 5, [(2, 3), (3, 4), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_19309 : Nat.Prime 19309 := by
  apply nodeValid_prime [2, 3, 1609] ⟨19309, 6, [(2, 2), (3, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1609
  · decide +kernel

theorem prime_24889 : Nat.Prime 24889 := by
  apply nodeValid_prime [2, 3, 17, 61] ⟨24889, 11, [(2, 3), (3, 1), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_26189 : Nat.Prime 26189 := by
  apply nodeValid_prime [2, 6547] ⟨26189, 2, [(2, 2), (6547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6547
  · decide +kernel

theorem prime_27091 : Nat.Prime 27091 := by
  apply nodeValid_prime [2, 3, 5, 7, 43] ⟨27091, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_29453 : Nat.Prime 29453 := by
  apply nodeValid_prime [2, 37, 199] ⟨29453, 2, [(2, 2), (37, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_199
  · decide +kernel

theorem prime_31627 : Nat.Prime 31627 := by
  apply nodeValid_prime [2, 3, 7, 251] ⟨31627, 3, [(2, 1), (3, 2), (7, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_251
  · decide +kernel

theorem prime_38047 : Nat.Prime 38047 := by
  apply nodeValid_prime [2, 3, 17, 373] ⟨38047, 3, [(2, 1), (3, 1), (17, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_373
  · decide +kernel

theorem prime_48091 : Nat.Prime 48091 := by
  apply nodeValid_prime [2, 3, 5, 7, 229] ⟨48091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_229
  · decide +kernel

theorem prime_48437 : Nat.Prime 48437 := by
  apply nodeValid_prime [2, 12109] ⟨48437, 2, [(2, 2), (12109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12109
  · decide +kernel

theorem prime_56443 : Nat.Prime 56443 := by
  apply nodeValid_prime [2, 3, 23, 409] ⟨56443, 5, [(2, 1), (3, 1), (23, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_409
  · decide +kernel

theorem prime_58907 : Nat.Prime 58907 := by
  apply nodeValid_prime [2, 29453] ⟨58907, 2, [(2, 1), (29453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29453
  · decide +kernel

theorem prime_63179 : Nat.Prime 63179 := by
  apply nodeValid_prime [2, 31, 1019] ⟨63179, 2, [(2, 1), (31, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1019
  · decide +kernel

theorem prime_68927 : Nat.Prime 68927 := by
  apply nodeValid_prime [2, 11, 13, 241] ⟨68927, 5, [(2, 1), (11, 1), (13, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_241
  · decide +kernel

theorem prime_77699 : Nat.Prime 77699 := by
  apply nodeValid_prime [2, 53, 733] ⟨77699, 2, [(2, 1), (53, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_733
  · decide +kernel

theorem prime_81547 : Nat.Prime 81547 := by
  apply nodeValid_prime [2, 3, 13591] ⟨81547, 3, [(2, 1), (3, 1), (13591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13591
  · decide +kernel

theorem prime_90599 : Nat.Prime 90599 := by
  apply nodeValid_prime [2, 97, 467] ⟨90599, 11, [(2, 1), (97, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_467
  · decide +kernel

theorem prime_92593 : Nat.Prime 92593 := by
  apply nodeValid_prime [2, 3, 643] ⟨92593, 5, [(2, 4), (3, 2), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_643
  · decide +kernel

theorem prime_92801 : Nat.Prime 92801 := by
  apply nodeValid_prime [2, 5, 29] ⟨92801, 3, [(2, 7), (5, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_99109 : Nat.Prime 99109 := by
  apply nodeValid_prime [2, 3, 2753] ⟨99109, 6, [(2, 2), (3, 2), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2753
  · decide +kernel

theorem prime_121931 : Nat.Prime 121931 := by
  apply nodeValid_prime [2, 5, 89, 137] ⟨121931, 2, [(2, 1), (5, 1), (89, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_137
  · decide +kernel

theorem prime_125803 : Nat.Prime 125803 := by
  apply nodeValid_prime [2, 3, 29, 241] ⟨125803, 3, [(2, 1), (3, 2), (29, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_241
  · decide +kernel

theorem prime_145289 : Nat.Prime 145289 := by
  apply nodeValid_prime [2, 11, 13, 127] ⟨145289, 3, [(2, 3), (11, 1), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_149249 : Nat.Prime 149249 := by
  apply nodeValid_prime [2, 11, 53] ⟨149249, 3, [(2, 8), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_155399 : Nat.Prime 155399 := by
  apply nodeValid_prime [2, 77699] ⟨155399, 19, [(2, 1), (77699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_77699
  · decide +kernel

theorem prime_172079 : Nat.Prime 172079 := by
  apply nodeValid_prime [2, 97, 887] ⟨172079, 13, [(2, 1), (97, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_887
  · decide +kernel

theorem prime_178259 : Nat.Prime 178259 := by
  apply nodeValid_prime [2, 19, 4691] ⟨178259, 2, [(2, 1), (19, 1), (4691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4691
  · decide +kernel

theorem prime_204601 : Nat.Prime 204601 := by
  apply nodeValid_prime [2, 3, 5, 11, 31] ⟨204601, 26, [(2, 3), (3, 1), (5, 2), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_215261 : Nat.Prime 215261 := by
  apply nodeValid_prime [2, 5, 47, 229] ⟨215261, 2, [(2, 2), (5, 1), (47, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_229
  · decide +kernel

theorem prime_217033 : Nat.Prime 217033 := by
  apply nodeValid_prime [2, 3, 9043] ⟨217033, 7, [(2, 3), (3, 1), (9043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9043
  · decide +kernel

theorem prime_223621 : Nat.Prime 223621 := by
  apply nodeValid_prime [2, 3, 5, 3727] ⟨223621, 2, [(2, 2), (3, 1), (5, 1), (3727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3727
  · decide +kernel

theorem prime_287731 : Nat.Prime 287731 := by
  apply nodeValid_prime [2, 3, 5, 23, 139] ⟨287731, 10, [(2, 1), (3, 2), (5, 1), (23, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_139
  · decide +kernel

theorem prime_341641 : Nat.Prime 341641 := by
  apply nodeValid_prime [2, 3, 5, 13, 73] ⟨341641, 7, [(2, 3), (3, 2), (5, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_392069 : Nat.Prime 392069 := by
  apply nodeValid_prime [2, 98017] ⟨392069, 2, [(2, 2), (98017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_98017
  · decide +kernel

theorem prime_392647 : Nat.Prime 392647 := by
  apply nodeValid_prime [2, 3, 31, 2111] ⟨392647, 3, [(2, 1), (3, 1), (31, 1), (2111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2111
  · decide +kernel

theorem prime_414049 : Nat.Prime 414049 := by
  apply nodeValid_prime [2, 3, 19, 227] ⟨414049, 7, [(2, 5), (3, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_439339 : Nat.Prime 439339 := by
  apply nodeValid_prime [2, 3, 37, 1979] ⟨439339, 2, [(2, 1), (3, 1), (37, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1979
  · decide +kernel

theorem prime_441053 : Nat.Prime 441053 := by
  apply nodeValid_prime [2, 71, 1553] ⟨441053, 2, [(2, 2), (71, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1553
  · decide +kernel

theorem prime_471403 : Nat.Prime 471403 := by
  apply nodeValid_prime [2, 3, 26189] ⟨471403, 5, [(2, 1), (3, 2), (26189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26189
  · decide +kernel

theorem prime_503213 : Nat.Prime 503213 := by
  apply nodeValid_prime [2, 125803] ⟨503213, 2, [(2, 2), (125803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_125803
  · decide +kernel

theorem prime_824699 : Nat.Prime 824699 := by
  apply nodeValid_prime [2, 7, 58907] ⟨824699, 6, [(2, 1), (7, 1), (58907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_58907
  · decide +kernel

theorem prime_881963 : Nat.Prime 881963 := by
  apply nodeValid_prime [2, 71, 6211] ⟨881963, 2, [(2, 1), (71, 1), (6211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_6211
  · decide +kernel

theorem prime_889237 : Nat.Prime 889237 := by
  apply nodeValid_prime [2, 3, 17, 1453] ⟨889237, 2, [(2, 2), (3, 2), (17, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1453
  · decide +kernel

theorem prime_966521 : Nat.Prime 966521 := by
  apply nodeValid_prime [2, 5, 73, 331] ⟨966521, 3, [(2, 3), (5, 1), (73, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_331
  · decide +kernel

theorem prime_978283 : Nat.Prime 978283 := by
  apply nodeValid_prime [2, 3, 17, 23, 139] ⟨978283, 2, [(2, 1), (3, 2), (17, 1), (23, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_139
  · decide +kernel

theorem prime_1039429 : Nat.Prime 1039429 := by
  apply nodeValid_prime [2, 3, 13, 2221] ⟨1039429, 7, [(2, 2), (3, 2), (13, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2221
  · decide +kernel

theorem prime_1191313 : Nat.Prime 1191313 := by
  apply nodeValid_prime [2, 3, 8273] ⟨1191313, 5, [(2, 4), (3, 2), (8273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8273
  · decide +kernel

theorem prime_1420651 : Nat.Prime 1420651 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 41] ⟨1420651, 3, [(2, 1), (3, 2), (5, 2), (7, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_1690189 : Nat.Prime 1690189 := by
  apply nodeValid_prime [2, 3, 61, 2309] ⟨1690189, 6, [(2, 2), (3, 1), (61, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_2309
  · decide +kernel

theorem prime_1743823 : Nat.Prime 1743823 := by
  apply nodeValid_prime [2, 3, 43, 751] ⟨1743823, 5, [(2, 1), (3, 3), (43, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_751
  · decide +kernel

theorem prime_1749941 : Nat.Prime 1749941 := by
  apply nodeValid_prime [2, 5, 59, 1483] ⟨1749941, 2, [(2, 2), (5, 1), (59, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_1483
  · decide +kernel

theorem prime_1790989 : Nat.Prime 1790989 := by
  apply nodeValid_prime [2, 3, 149249] ⟨1790989, 2, [(2, 2), (3, 1), (149249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149249
  · decide +kernel

theorem prime_1835969 : Nat.Prime 1835969 := by
  apply nodeValid_prime [2, 28687] ⟨1835969, 3, [(2, 6), (28687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28687
  · decide +kernel

theorem prime_1885613 : Nat.Prime 1885613 := by
  apply nodeValid_prime [2, 471403] ⟨1885613, 2, [(2, 2), (471403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_471403
  · decide +kernel

theorem prime_2067811 : Nat.Prime 2067811 := by
  apply nodeValid_prime [2, 3, 5, 68927] ⟨2067811, 2, [(2, 1), (3, 1), (5, 1), (68927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_68927
  · decide +kernel

theorem prime_2135447 : Nat.Prime 2135447 := by
  apply nodeValid_prime [2, 59, 18097] ⟨2135447, 5, [(2, 1), (59, 1), (18097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_18097
  · decide +kernel

theorem prime_2500733 : Nat.Prime 2500733 := by
  apply nodeValid_prime [2, 13, 48091] ⟨2500733, 2, [(2, 2), (13, 1), (48091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_48091
  · decide +kernel

theorem prime_3695089 : Nat.Prime 3695089 := by
  apply nodeValid_prime [2, 3, 23, 3347] ⟨3695089, 11, [(2, 4), (3, 1), (23, 1), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3347
  · decide +kernel

theorem prime_4702283 : Nat.Prime 4702283 := by
  apply nodeValid_prime [2, 13, 83, 2179] ⟨4702283, 2, [(2, 1), (13, 1), (83, 1), (2179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_83
    · exact prime_2179
  · decide +kernel

theorem prime_4927231 : Nat.Prime 4927231 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 79] ⟨4927231, 3, [(2, 1), (3, 4), (5, 1), (7, 1), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_4968589 : Nat.Prime 4968589 := by
  apply nodeValid_prime [2, 3, 414049] ⟨4968589, 2, [(2, 2), (3, 1), (414049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_414049
  · decide +kernel

theorem prime_5162371 : Nat.Prime 5162371 := by
  apply nodeValid_prime [2, 3, 5, 172079] ⟨5162371, 2, [(2, 1), (3, 1), (5, 1), (172079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_172079
  · decide +kernel

theorem prime_5203733 : Nat.Prime 5203733 := by
  apply nodeValid_prime [2, 71, 73, 251] ⟨5203733, 2, [(2, 2), (71, 1), (73, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_73
    · exact prime_251
  · decide +kernel

theorem prime_9977269 : Nat.Prime 9977269 := by
  apply nodeValid_prime [2, 3, 7, 41, 2897] ⟨9977269, 2, [(2, 2), (3, 1), (7, 1), (41, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_2897
  · decide +kernel

theorem prime_11642473 : Nat.Prime 11642473 := by
  apply nodeValid_prime [2, 3, 101, 1601] ⟨11642473, 11, [(2, 3), (3, 2), (101, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1601
  · decide +kernel

theorem prime_16901891 : Nat.Prime 16901891 := by
  apply nodeValid_prime [2, 5, 1690189] ⟨16901891, 2, [(2, 1), (5, 1), (1690189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1690189
  · decide +kernel

theorem prime_17263861 : Nat.Prime 17263861 := by
  apply nodeValid_prime [2, 3, 5, 287731] ⟨17263861, 2, [(2, 2), (3, 1), (5, 1), (287731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_287731
  · decide +kernel

theorem prime_17267297 : Nat.Prime 17267297 := by
  apply nodeValid_prime [2, 23, 29, 809] ⟨17267297, 3, [(2, 5), (23, 1), (29, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_809
  · decide +kernel

theorem prime_22771607 : Nat.Prime 22771607 := by
  apply nodeValid_prime [2, 11, 13, 79621] ⟨22771607, 5, [(2, 1), (11, 1), (13, 1), (79621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_79621
  · decide +kernel

theorem prime_25320929 : Nat.Prime 25320929 := by
  apply nodeValid_prime [2, 599, 1321] ⟨25320929, 3, [(2, 5), (599, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_599
    · exact prime_1321
  · decide +kernel

theorem prime_31698911 : Nat.Prime 31698911 := by
  apply nodeValid_prime [2, 5, 827, 3833] ⟨31698911, 23, [(2, 1), (5, 1), (827, 1), (3833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_827
    · exact prime_3833
  · decide +kernel

theorem prime_63397823 : Nat.Prime 63397823 := by
  apply nodeValid_prime [2, 31698911] ⟨63397823, 5, [(2, 1), (31698911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31698911
  · decide +kernel

theorem prime_65273167 : Nat.Prime 65273167 := by
  apply nodeValid_prime [2, 3, 7, 17, 31, 983] ⟨65273167, 5, [(2, 1), (3, 2), (7, 1), (17, 1), (31, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_983
  · decide +kernel

theorem prime_67969771 : Nat.Prime 67969771 := by
  apply nodeValid_prime [2, 3, 5, 11, 59, 3491] ⟨67969771, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (3491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_59
    · exact prime_3491
  · decide +kernel

theorem prime_69178583 : Nat.Prime 69178583 := by
  apply nodeValid_prime [2, 11, 19, 359, 461] ⟨69178583, 5, [(2, 1), (11, 1), (19, 1), (359, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_359
    · exact prime_461
  · decide +kernel

theorem prime_71687873 : Nat.Prime 71687873 := by
  apply nodeValid_prime [2, 23, 31, 1571] ⟨71687873, 3, [(2, 6), (23, 1), (31, 1), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_1571
  · decide +kernel

theorem prime_82165579 : Nat.Prime 82165579 := by
  apply nodeValid_prime [2, 3, 11, 311, 4003] ⟨82165579, 2, [(2, 1), (3, 1), (11, 1), (311, 1), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_311
    · exact prime_4003
  · decide +kernel

theorem prime_96083807 : Nat.Prime 96083807 := by
  apply nodeValid_prime [2, 7, 13, 53, 1423] ⟨96083807, 5, [(2, 1), (7, 2), (13, 1), (53, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_53
    · exact prime_1423
  · decide +kernel

theorem prime_96390529 : Nat.Prime 96390529 := by
  apply nodeValid_prime [2, 3, 13, 19309] ⟨96390529, 38, [(2, 7), (3, 1), (13, 1), (19309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19309
  · decide +kernel

theorem prime_100350641 : Nat.Prime 100350641 := by
  apply nodeValid_prime [2, 5, 13, 47, 2053] ⟨100350641, 3, [(2, 4), (5, 1), (13, 1), (47, 1), (2053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_47
    · exact prime_2053
  · decide +kernel

theorem prime_103583167 : Nat.Prime 103583167 := by
  apply nodeValid_prime [2, 3, 17263861] ⟨103583167, 3, [(2, 1), (3, 1), (17263861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17263861
  · decide +kernel

theorem prime_143375747 : Nat.Prime 143375747 := by
  apply nodeValid_prime [2, 71687873] ⟨143375747, 2, [(2, 1), (71687873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71687873
  · decide +kernel

theorem prime_183471817 : Nat.Prime 183471817 := by
  apply nodeValid_prime [2, 3, 11, 63179] ⟨183471817, 10, [(2, 3), (3, 1), (11, 2), (63179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_63179
  · decide +kernel

theorem prime_199814161 : Nat.Prime 199814161 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 1307] ⟨199814161, 19, [(2, 4), (3, 1), (5, 1), (7, 2), (13, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_1307
  · decide +kernel

theorem prime_232114541 : Nat.Prime 232114541 := by
  apply nodeValid_prime [2, 5, 7, 313, 5297] ⟨232114541, 3, [(2, 2), (5, 1), (7, 1), (313, 1), (5297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_313
    · exact prime_5297
  · decide +kernel

theorem prime_234856553 : Nat.Prime 234856553 := by
  apply nodeValid_prime [2, 7, 1657, 2531] ⟨234856553, 3, [(2, 3), (7, 1), (1657, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1657
    · exact prime_2531
  · decide +kernel

theorem prime_301777837 : Nat.Prime 301777837 := by
  apply nodeValid_prime [2, 3, 19, 109, 12143] ⟨301777837, 6, [(2, 2), (3, 1), (19, 1), (109, 1), (12143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_109
    · exact prime_12143
  · decide +kernel

theorem prime_374537677 : Nat.Prime 374537677 := by
  apply nodeValid_prime [2, 3, 17, 1835969] ⟨374537677, 2, [(2, 2), (3, 1), (17, 1), (1835969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1835969
  · decide +kernel

theorem prime_391591573 : Nat.Prime 391591573 := by
  apply nodeValid_prime [2, 3, 37, 881963] ⟨391591573, 2, [(2, 2), (3, 1), (37, 1), (881963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_881963
  · decide +kernel

theorem prime_421305991 : Nat.Prime 421305991 := by
  apply nodeValid_prime [2, 3, 5, 7, 127, 15797] ⟨421305991, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (15797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_127
    · exact prime_15797
  · decide +kernel

theorem prime_602103847 : Nat.Prime 602103847 := by
  apply nodeValid_prime [2, 3, 100350641] ⟨602103847, 3, [(2, 1), (3, 1), (100350641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_100350641
  · decide +kernel

theorem prime_664977581 : Nat.Prime 664977581 := by
  apply nodeValid_prime [2, 5, 19, 1749941] ⟨664977581, 2, [(2, 2), (5, 1), (19, 1), (1749941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1749941
  · decide +kernel

theorem prime_692609693 : Nat.Prime 692609693 := by
  apply nodeValid_prime [2, 73, 277, 8563] ⟨692609693, 2, [(2, 2), (73, 1), (277, 1), (8563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_277
    · exact prime_8563
  · decide +kernel

theorem prime_737528773 : Nat.Prime 737528773 := by
  apply nodeValid_prime [2, 3, 3967, 15493] ⟨737528773, 2, [(2, 2), (3, 1), (3967, 1), (15493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3967
    · exact prime_15493
  · decide +kernel

theorem prime_746535761 : Nat.Prime 746535761 := by
  apply nodeValid_prime [2, 5, 103, 90599] ⟨746535761, 3, [(2, 4), (5, 1), (103, 1), (90599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_90599
  · decide +kernel

theorem prime_785230163 : Nat.Prime 785230163 := by
  apply nodeValid_prime [2, 157, 2500733] ⟨785230163, 2, [(2, 1), (157, 1), (2500733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_2500733
  · decide +kernel

theorem prime_806200651 : Nat.Prime 806200651 := by
  apply nodeValid_prime [2, 3, 5, 1259, 1423] ⟨806200651, 7, [(2, 1), (3, 2), (5, 2), (1259, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1259
    · exact prime_1423
  · decide +kernel

theorem prime_1207111349 : Nat.Prime 1207111349 := by
  apply nodeValid_prime [2, 301777837] ⟨1207111349, 2, [(2, 2), (301777837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_301777837
  · decide +kernel

theorem prime_1870295249 : Nat.Prime 1870295249 := by
  apply nodeValid_prime [2, 19, 109, 56443] ⟨1870295249, 3, [(2, 4), (19, 1), (109, 1), (56443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_109
    · exact prime_56443
  · decide +kernel

theorem prime_2128743809 : Nat.Prime 2128743809 := by
  apply nodeValid_prime [2, 17, 978283] ⟨2128743809, 3, [(2, 7), (17, 1), (978283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_978283
  · decide +kernel

theorem prime_2349549439 : Nat.Prime 2349549439 := by
  apply nodeValid_prime [2, 3, 391591573] ⟨2349549439, 3, [(2, 1), (3, 1), (391591573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_391591573
  · decide +kernel

theorem prime_2538035099 : Nat.Prime 2538035099 := by
  apply nodeValid_prime [2, 673, 1885613] ⟨2538035099, 2, [(2, 1), (673, 1), (1885613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_673
    · exact prime_1885613
  · decide +kernel

theorem prime_2661492179 : Nat.Prime 2661492179 := by
  apply nodeValid_prime [2, 283, 4702283] ⟨2661492179, 2, [(2, 1), (283, 1), (4702283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_4702283
  · decide +kernel

theorem prime_3798073567 : Nat.Prime 3798073567 := by
  apply nodeValid_prime [2, 3, 7, 29, 1039429] ⟨3798073567, 3, [(2, 1), (3, 2), (7, 1), (29, 1), (1039429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_1039429
  · decide +kernel

theorem prime_7558014967 : Nat.Prime 7558014967 := by
  apply nodeValid_prime [2, 3, 10331, 121931] ⟨7558014967, 3, [(2, 1), (3, 1), (10331, 1), (121931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10331
    · exact prime_121931
  · decide +kernel

theorem prime_7707883241 : Nat.Prime 7707883241 := by
  apply nodeValid_prime [2, 5, 149, 347, 3727] ⟨7707883241, 3, [(2, 3), (5, 1), (149, 1), (347, 1), (3727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_347
    · exact prime_3727
  · decide +kernel

theorem prime_8392194763 : Nat.Prime 8392194763 := by
  apply nodeValid_prime [2, 3, 7, 199814161] ⟨8392194763, 19, [(2, 1), (3, 1), (7, 1), (199814161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199814161
  · decide +kernel

theorem prime_15484692761 : Nat.Prime 15484692761 := by
  apply nodeValid_prime [2, 5, 17, 22771607] ⟨15484692761, 3, [(2, 3), (5, 1), (17, 1), (22771607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_22771607
  · decide +kernel

theorem prime_17034597449 : Nat.Prime 17034597449 := by
  apply nodeValid_prime [2, 11, 17, 29, 392647] ⟨17034597449, 3, [(2, 3), (11, 1), (17, 1), (29, 1), (392647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_29
    · exact prime_392647
  · decide +kernel

theorem prime_18845523913 : Nat.Prime 18845523913 := by
  apply nodeValid_prime [2, 3, 785230163] ⟨18845523913, 10, [(2, 3), (3, 1), (785230163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_785230163
  · decide +kernel

theorem prime_22494627527 : Nat.Prime 22494627527 := by
  apply nodeValid_prime [2, 7, 31, 103, 503213] ⟨22494627527, 5, [(2, 1), (7, 1), (31, 1), (103, 1), (503213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_103
    · exact prime_503213
  · decide +kernel

theorem prime_22725483791 : Nat.Prime 22725483791 := by
  apply nodeValid_prime [2, 5, 101, 179, 337, 373] ⟨22725483791, 29, [(2, 1), (5, 1), (101, 1), (179, 1), (337, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_179
    · exact prime_337
    · exact prime_373
  · decide +kernel

theorem prime_23603048437 : Nat.Prime 23603048437 := by
  apply nodeValid_prime [2, 3, 11, 37, 439339] ⟨23603048437, 2, [(2, 2), (3, 1), (11, 2), (37, 1), (439339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_439339
  · decide +kernel

theorem prime_34764424379 : Nat.Prime 34764424379 := by
  apply nodeValid_prime [2, 1493, 11642473] ⟨34764424379, 2, [(2, 1), (1493, 1), (11642473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1493
    · exact prime_11642473
  · decide +kernel

theorem prime_42297012217 : Nat.Prime 42297012217 := by
  apply nodeValid_prime [2, 3, 65273167] ⟨42297012217, 7, [(2, 3), (3, 4), (65273167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_65273167
  · decide +kernel

theorem prime_44887085977 : Nat.Prime 44887085977 := by
  apply nodeValid_prime [2, 3, 1870295249] ⟨44887085977, 5, [(2, 3), (3, 1), (1870295249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1870295249
  · decide +kernel

theorem prime_45348089803 : Nat.Prime 45348089803 := by
  apply nodeValid_prime [2, 3, 7558014967] ⟨45348089803, 5, [(2, 1), (3, 1), (7558014967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7558014967
  · decide +kernel

theorem prime_63807230873 : Nat.Prime 63807230873 := by
  apply nodeValid_prime [2, 7, 11, 103583167] ⟨63807230873, 5, [(2, 3), (7, 1), (11, 1), (103583167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_103583167
  · decide +kernel

theorem prime_84690334667 : Nat.Prime 84690334667 := by
  apply nodeValid_prime [2, 7, 89, 67969771] ⟨84690334667, 2, [(2, 1), (7, 1), (89, 1), (67969771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_67969771
  · decide +kernel

theorem prime_251765842891 : Nat.Prime 251765842891 := by
  apply nodeValid_prime [2, 3, 5, 8392194763] ⟨251765842891, 10, [(2, 1), (3, 1), (5, 1), (8392194763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8392194763
  · decide +kernel

theorem prime_380673109987 : Nat.Prime 380673109987 := by
  apply nodeValid_prime [2, 3, 13, 23, 2141, 99109] ⟨380673109987, 2, [(2, 1), (3, 1), (13, 1), (23, 1), (2141, 1), (99109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_2141
    · exact prime_99109
  · decide +kernel

theorem prime_384149571073 : Nat.Prime 384149571073 := by
  apply nodeValid_prime [2, 3, 23, 61, 178259] ⟨384149571073, 10, [(2, 9), (3, 1), (23, 1), (61, 1), (178259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_61
    · exact prime_178259
  · decide +kernel

theorem prime_386333240233 : Nat.Prime 386333240233 := by
  apply nodeValid_prime [2, 3, 167, 96390529] ⟨386333240233, 5, [(2, 3), (3, 1), (167, 1), (96390529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_96390529
  · decide +kernel

theorem prime_756159622733 : Nat.Prime 756159622733 := by
  apply nodeValid_prime [2, 38047, 4968589] ⟨756159622733, 2, [(2, 2), (38047, 1), (4968589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_38047
    · exact prime_4968589
  · decide +kernel

theorem prime_765686781143 : Nat.Prime 765686781143 := by
  apply nodeValid_prime [2, 229, 7703, 217033] ⟨765686781143, 5, [(2, 1), (229, 1), (7703, 1), (217033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_7703
    · exact prime_217033
  · decide +kernel

theorem prime_1503711579551 : Nat.Prime 1503711579551 := by
  apply nodeValid_prime [2, 5, 313, 96083807] ⟨1503711579551, 11, [(2, 1), (5, 2), (313, 1), (96083807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_313
    · exact prime_96083807
  · decide +kernel

theorem prime_1503711640961 : Nat.Prime 1503711640961 := by
  apply nodeValid_prime [2, 5, 2349549439] ⟨1503711640961, 3, [(2, 7), (5, 1), (2349549439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2349549439
  · decide +kernel

theorem prime_1505430504731 : Nat.Prime 1505430504731 := by
  apply nodeValid_prime [2, 5, 641, 234856553] ⟨1505430504731, 10, [(2, 1), (5, 1), (641, 1), (234856553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
    · exact prime_234856553
  · decide +kernel

theorem prime_1505430507311 : Nat.Prime 1505430507311 := by
  apply nodeValid_prime [2, 5, 113, 263, 467, 10847] ⟨1505430507311, 11, [(2, 1), (5, 1), (113, 1), (263, 1), (467, 1), (10847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
    · exact prime_263
    · exact prime_467
    · exact prime_10847
  · decide +kernel

theorem prime_1505430512767 : Nat.Prime 1505430512767 := by
  apply nodeValid_prime [2, 3, 367, 25320929] ⟨1505430512767, 3, [(2, 1), (3, 4), (367, 1), (25320929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_25320929
  · decide +kernel

theorem prime_1507150615753 : Nat.Prime 1507150615753 := by
  apply nodeValid_prime [2, 3, 29, 2311, 104113] ⟨1507150615753, 10, [(2, 3), (3, 3), (29, 1), (2311, 1), (104113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2311
    · exact prime_104113
  · decide +kernel

theorem prime_1507150616773 : Nat.Prime 1507150616773 := by
  apply nodeValid_prime [2, 3, 59, 2128743809] ⟨1507150616773, 2, [(2, 2), (3, 1), (59, 1), (2128743809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2128743809
  · decide +kernel

theorem prime_1507150711873 : Nat.Prime 1507150711873 := by
  apply nodeValid_prime [2, 3, 13, 421, 17707] ⟨1507150711873, 17, [(2, 6), (3, 5), (13, 1), (421, 1), (17707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_421
    · exact prime_17707
  · decide +kernel

theorem prime_1508872222307 : Nat.Prime 1508872222307 := by
  apply nodeValid_prime [2, 1409, 2617, 204601] ⟨1508872222307, 2, [(2, 1), (1409, 1), (2617, 1), (204601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1409
    · exact prime_2617
    · exact prime_204601
  · decide +kernel

theorem prime_1508872223009 : Nat.Prime 1508872223009 := by
  apply nodeValid_prime [2, 257, 183471817] ⟨1508872223009, 3, [(2, 5), (257, 1), (183471817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_183471817
  · decide +kernel

theorem prime_1508872240583 : Nat.Prime 1508872240583 := by
  apply nodeValid_prime [2, 7, 179, 602103847] ⟨1508872240583, 5, [(2, 1), (7, 1), (179, 1), (602103847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_179
    · exact prime_602103847
  · decide +kernel

theorem prime_1510595057347 : Nat.Prime 1510595057347 := by
  apply nodeValid_prime [2, 3, 251765842891] ⟨1510595057347, 19, [(2, 1), (3, 1), (251765842891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251765842891
  · decide +kernel

theorem prime_1510595057623 : Nat.Prime 1510595057623 := by
  apply nodeValid_prime [2, 3, 7, 81547, 441053] ⟨1510595057623, 3, [(2, 1), (3, 1), (7, 1), (81547, 1), (441053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_81547
    · exact prime_441053
  · decide +kernel

theorem prime_1510595099969 : Nat.Prime 1510595099969 := by
  apply nodeValid_prime [2, 23603048437] ⟨1510595099969, 3, [(2, 6), (23603048437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23603048437
  · decide +kernel

theorem prime_1512319245467 : Nat.Prime 1512319245467 := by
  apply nodeValid_prime [2, 756159622733] ⟨1512319245467, 2, [(2, 1), (756159622733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_756159622733
  · decide +kernel

theorem prime_1512319246769 : Nat.Prime 1512319246769 := by
  apply nodeValid_prime [2, 11, 92593, 92801] ⟨1512319246769, 3, [(2, 4), (11, 1), (92593, 1), (92801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_92593
    · exact prime_92801
  · decide +kernel

theorem prime_1512319291927 : Nat.Prime 1512319291927 := by
  apply nodeValid_prime [2, 3, 48437, 5203733] ⟨1512319291927, 3, [(2, 1), (3, 1), (48437, 1), (5203733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48437
    · exact prime_5203733
  · decide +kernel

theorem prime_1514044788899 : Nat.Prime 1514044788899 := by
  apply nodeValid_prime [2, 1093, 692609693] ⟨1514044788899, 2, [(2, 1), (1093, 1), (692609693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1093
    · exact prime_692609693
  · decide +kernel

theorem prime_1514044788953 : Nat.Prime 1514044788953 := by
  apply nodeValid_prime [2, 251, 421, 1790989] ⟨1514044788953, 3, [(2, 3), (251, 1), (421, 1), (1790989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_421
    · exact prime_1790989
  · decide +kernel

theorem prime_1514044822579 : Nat.Prime 1514044822579 := by
  apply nodeValid_prime [2, 3, 313, 806200651] ⟨1514044822579, 3, [(2, 1), (3, 1), (313, 1), (806200651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
    · exact prime_806200651
  · decide +kernel

theorem prime_1515771632953 : Nat.Prime 1515771632953 := by
  apply nodeValid_prime [2, 3, 10181, 2067811] ⟨1515771632953, 5, [(2, 3), (3, 2), (10181, 1), (2067811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10181
    · exact prime_2067811
  · decide +kernel

theorem prime_1515771687797 : Nat.Prime 1515771687797 := by
  apply nodeValid_prime [2, 392069, 966521] ⟨1515771687797, 2, [(2, 2), (392069, 1), (966521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_392069
    · exact prime_966521
  · decide +kernel

theorem prime_1517499888929 : Nat.Prime 1517499888929 := by
  apply nodeValid_prime [2, 53, 419, 2135447] ⟨1517499888929, 3, [(2, 5), (53, 1), (419, 1), (2135447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_419
    · exact prime_2135447
  · decide +kernel

theorem prime_1517499889303 : Nat.Prime 1517499889303 := by
  apply nodeValid_prime [2, 3, 41, 103, 127, 409, 1153] ⟨1517499889303, 6, [(2, 1), (3, 1), (41, 1), (103, 1), (127, 1), (409, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_103
    · exact prime_127
    · exact prime_409
    · exact prime_1153
  · decide +kernel

theorem prime_1517499890579 : Nat.Prime 1517499890579 := by
  apply nodeValid_prime [2, 7, 15484692761] ⟨1517499890579, 2, [(2, 1), (7, 2), (15484692761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15484692761
  · decide +kernel

theorem prime_1519229401969 : Nat.Prime 1519229401969 := by
  apply nodeValid_prime [2, 3, 35593, 889237] ⟨1519229401969, 7, [(2, 4), (3, 1), (35593, 1), (889237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35593
    · exact prime_889237
  · decide +kernel

theorem prime_1519229403547 : Nat.Prime 1519229403547 := by
  apply nodeValid_prime [2, 3, 601, 421305991] ⟨1519229403547, 2, [(2, 1), (3, 1), (601, 1), (421305991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
    · exact prime_421305991
  · decide +kernel

theorem prime_1519229426801 : Nat.Prime 1519229426801 := by
  apply nodeValid_prime [2, 5, 3798073567] ⟨1519229426801, 3, [(2, 4), (5, 2), (3798073567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3798073567
  · decide +kernel

theorem prime_1520960299741 : Nat.Prime 1520960299741 := by
  apply nodeValid_prime [2, 3, 5, 7, 1207111349] ⟨1520960299741, 29, [(2, 2), (3, 2), (5, 1), (7, 1), (1207111349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1207111349
  · decide +kernel

theorem prime_1520960325809 : Nat.Prime 1520960325809 := by
  apply nodeValid_prime [2, 7, 11, 79, 1420651] ⟨1520960325809, 3, [(2, 4), (7, 1), (11, 2), (79, 1), (1420651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_79
    · exact prime_1420651
  · decide +kernel

theorem prime_1520960325839 : Nat.Prime 1520960325839 := by
  apply nodeValid_prime [2, 10993, 69178583] ⟨1520960325839, 11, [(2, 1), (10993, 1), (69178583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10993
    · exact prime_69178583
  · decide +kernel

theorem prime_1522692439813 : Nat.Prime 1522692439813 := by
  apply nodeValid_prime [2, 3, 42297012217] ⟨1522692439813, 2, [(2, 2), (3, 2), (42297012217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42297012217
  · decide +kernel

theorem prime_1522692439949 : Nat.Prime 1522692439949 := by
  apply nodeValid_prime [2, 380673109987] ⟨1522692439949, 2, [(2, 2), (380673109987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_380673109987
  · decide +kernel

theorem prime_1522692510029 : Nat.Prime 1522692510029 := by
  apply nodeValid_prime [2, 41, 113, 82165579] ⟨1522692510029, 2, [(2, 2), (41, 1), (113, 1), (82165579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_113
    · exact prime_82165579
  · decide +kernel

theorem prime_1524426023963 : Nat.Prime 1524426023963 := by
  apply nodeValid_prime [2, 1021, 746535761] ⟨1524426023963, 2, [(2, 1), (1021, 1), (746535761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1021
    · exact prime_746535761
  · decide +kernel

theorem prime_1524426024007 : Nat.Prime 1524426024007 := by
  apply nodeValid_prime [2, 3, 84690334667] ⟨1524426024007, 5, [(2, 1), (3, 2), (84690334667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_84690334667
  · decide +kernel

theorem prime_1524426048349 : Nat.Prime 1524426048349 := by
  apply nodeValid_prime [2, 3, 7, 1051, 17267297] ⟨1524426048349, 2, [(2, 2), (3, 1), (7, 1), (1051, 1), (17267297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1051
    · exact prime_17267297
  · decide +kernel

theorem prime_1526160881719 : Nat.Prime 1526160881719 := by
  apply nodeValid_prime [2, 3, 11, 7707883241] ⟨1526160881719, 11, [(2, 1), (3, 2), (11, 1), (7707883241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_7707883241
  · decide +kernel

theorem prime_1526160881977 : Nat.Prime 1526160881977 := by
  apply nodeValid_prime [2, 3, 17, 17377, 215261] ⟨1526160881977, 10, [(2, 3), (3, 1), (17, 1), (17377, 1), (215261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_17377
    · exact prime_215261
  · decide +kernel

theorem prime_1526160923219 : Nat.Prime 1526160923219 := by
  apply nodeValid_prime [2, 17, 44887085977] ⟨1526160923219, 2, [(2, 1), (17, 1), (44887085977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_44887085977
  · decide +kernel

theorem prime_1527897129431 : Nat.Prime 1527897129431 := by
  apply nodeValid_prime [2, 5, 7, 9127, 341641] ⟨1527897129431, 7, [(2, 1), (5, 1), (7, 2), (9127, 1), (341641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_9127
    · exact prime_341641
  · decide +kernel

theorem prime_1527897129599 : Nat.Prime 1527897129599 := by
  apply nodeValid_prime [2, 7, 43, 2538035099] ⟨1527897129599, 7, [(2, 1), (7, 1), (43, 1), (2538035099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_2538035099
  · decide +kernel

theorem prime_1527897130967 : Nat.Prime 1527897130967 := by
  apply nodeValid_prime [2, 23, 89, 101, 3695089] ⟨1527897130967, 5, [(2, 1), (23, 1), (89, 1), (101, 1), (3695089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_89
    · exact prime_101
    · exact prime_3695089
  · decide +kernel

theorem prime_1529634671837 : Nat.Prime 1529634671837 := by
  apply nodeValid_prime [2, 17, 22494627527] ⟨1529634671837, 2, [(2, 2), (17, 1), (22494627527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_22494627527
  · decide +kernel

theorem prime_1529634672677 : Nat.Prime 1529634672677 := by
  apply nodeValid_prime [2, 11, 34764424379] ⟨1529634672677, 2, [(2, 2), (11, 1), (34764424379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_34764424379
  · decide +kernel

theorem prime_1529634675203 : Nat.Prime 1529634675203 := by
  apply nodeValid_prime [2, 17, 61, 737528773] ⟨1529634675203, 2, [(2, 1), (17, 1), (61, 1), (737528773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_737528773
  · decide +kernel

theorem prime_1531373540339 : Nat.Prime 1531373540339 := by
  apply nodeValid_prime [2, 155399, 4927231] ⟨1531373540339, 2, [(2, 1), (155399, 1), (4927231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_155399
    · exact prime_4927231
  · decide +kernel

theorem prime_1531373540953 : Nat.Prime 1531373540953 := by
  apply nodeValid_prime [2, 3, 63807230873] ⟨1531373540953, 5, [(2, 3), (3, 1), (63807230873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63807230873
  · decide +kernel

theorem prime_1531373562287 : Nat.Prime 1531373562287 := by
  apply nodeValid_prime [2, 765686781143] ⟨1531373562287, 5, [(2, 1), (765686781143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_765686781143
  · decide +kernel

theorem prime_1533113770411 : Nat.Prime 1533113770411 := by
  apply nodeValid_prime [2, 3, 5, 17034597449] ⟨1533113770411, 13, [(2, 1), (3, 2), (5, 1), (17034597449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17034597449
  · decide +kernel

theorem prime_1533113771311 : Nat.Prime 1533113771311 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 193, 15641] ⟨1533113771311, 6, [(2, 1), (3, 5), (5, 1), (11, 1), (19, 1), (193, 1), (15641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_193
    · exact prime_15641
  · decide +kernel

theorem prime_1533113791603 : Nat.Prime 1533113791603 := by
  apply nodeValid_prime [2, 3, 19, 23, 709, 824699] ⟨1533113791603, 2, [(2, 1), (3, 1), (19, 1), (23, 1), (709, 1), (824699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_709
    · exact prime_824699
  · decide +kernel

theorem prime_1534855356037 : Nat.Prime 1534855356037 := by
  apply nodeValid_prime [2, 3, 19, 13267, 18793] ⟨1534855356037, 2, [(2, 2), (3, 4), (19, 1), (13267, 1), (18793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_13267
    · exact prime_18793
  · decide +kernel

theorem prime_1534855400317 : Nat.Prime 1534855400317 := by
  apply nodeValid_prime [2, 3, 7, 23, 2791, 31627] ⟨1534855400317, 2, [(2, 2), (3, 3), (7, 1), (23, 1), (2791, 1), (31627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_2791
    · exact prime_31627
  · decide +kernel

theorem prime_1534855400347 : Nat.Prime 1534855400347 := by
  apply nodeValid_prime [2, 3, 683, 374537677] ⟨1534855400347, 2, [(2, 1), (3, 1), (683, 1), (374537677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_374537677
  · decide +kernel

theorem prime_1536598261421 : Nat.Prime 1536598261421 := by
  apply nodeValid_prime [2, 5, 331, 232114541] ⟨1536598261421, 2, [(2, 2), (5, 1), (331, 1), (232114541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_331
    · exact prime_232114541
  · decide +kernel

theorem prime_1536598284241 : Nat.Prime 1536598284241 := by
  apply nodeValid_prime [2, 3, 5, 28631, 223621] ⟨1536598284241, 7, [(2, 4), (3, 1), (5, 1), (28631, 1), (223621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28631
    · exact prime_223621
  · decide +kernel

theorem prime_1536598284293 : Nat.Prime 1536598284293 := by
  apply nodeValid_prime [2, 384149571073] ⟨1536598284293, 2, [(2, 2), (384149571073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_384149571073
  · decide +kernel

theorem prime_1538342476901 : Nat.Prime 1538342476901 := by
  apply nodeValid_prime [2, 5, 37, 349, 1191313] ⟨1538342476901, 2, [(2, 2), (5, 2), (37, 1), (349, 1), (1191313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_349
    · exact prime_1191313
  · decide +kernel

theorem prime_1538342479463 : Nat.Prime 1538342479463 := by
  apply nodeValid_prime [2, 17, 2661492179] ⟨1538342479463, 5, [(2, 1), (17, 2), (2661492179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2661492179
  · decide +kernel

theorem prime_1538342511257 : Nat.Prime 1538342511257 := by
  apply nodeValid_prime [2, 31, 367, 16901891] ⟨1538342511257, 3, [(2, 3), (31, 1), (367, 1), (16901891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_367
    · exact prime_16901891
  · decide +kernel

theorem prime_1540088077519 : Nat.Prime 1540088077519 := by
  apply nodeValid_prime [2, 3, 137, 23053, 27091] ⟨1540088077519, 3, [(2, 1), (3, 2), (137, 1), (23053, 1), (27091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_23053
    · exact prime_27091
  · decide +kernel

theorem prime_1540088077597 : Nat.Prime 1540088077597 := by
  apply nodeValid_prime [2, 3, 193, 664977581] ⟨1540088077597, 2, [(2, 2), (3, 1), (193, 1), (664977581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_664977581
  · decide +kernel

theorem prime_1540088099131 : Nat.Prime 1540088099131 := by
  apply nodeValid_prime [2, 3, 5, 7, 7211, 145289] ⟨1540088099131, 15, [(2, 1), (3, 1), (5, 1), (7, 2), (7211, 1), (145289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_7211
    · exact prime_145289
  · decide +kernel

theorem prime_1541835021829 : Nat.Prime 1541835021829 := by
  apply nodeValid_prime [2, 3, 24889, 5162371] ⟨1541835021829, 6, [(2, 2), (3, 1), (24889, 1), (5162371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24889
    · exact prime_5162371
  · decide +kernel

theorem prime_1541835053303 : Nat.Prime 1541835053303 := by
  apply nodeValid_prime [2, 17, 45348089803] ⟨1541835053303, 5, [(2, 1), (17, 1), (45348089803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_45348089803
  · decide +kernel

theorem prime_1541835055361 : Nat.Prime 1541835055361 := by
  apply nodeValid_prime [2, 5, 19, 63397823] ⟨1541835055361, 3, [(2, 8), (5, 1), (19, 1), (63397823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_63397823
  · decide +kernel

theorem prime_1543583286991 : Nat.Prime 1543583286991 := by
  apply nodeValid_prime [2, 3, 5, 191, 9977269] ⟨1543583286991, 3, [(2, 1), (3, 4), (5, 1), (191, 1), (9977269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
    · exact prime_9977269
  · decide +kernel

theorem prime_1543583292203 : Nat.Prime 1543583292203 := by
  apply nodeValid_prime [2, 7, 769, 143375747] ⟨1543583292203, 2, [(2, 1), (7, 1), (769, 1), (143375747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_769
    · exact prime_143375747
  · decide +kernel

theorem prime_1543583292557 : Nat.Prime 1543583292557 := by
  apply nodeValid_prime [2, 19, 613, 1743823] ⟨1543583292557, 2, [(2, 2), (19, 2), (613, 1), (1743823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_613
    · exact prime_1743823
  · decide +kernel

theorem prime_1545332897789 : Nat.Prime 1545332897789 := by
  apply nodeValid_prime [2, 17, 22725483791] ⟨1545332897789, 2, [(2, 2), (17, 1), (22725483791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_22725483791
  · decide +kernel

theorem prime_1545332960867 : Nat.Prime 1545332960867 := by
  apply nodeValid_prime [2, 41, 18845523913] ⟨1545332960867, 2, [(2, 1), (41, 1), (18845523913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_18845523913
  · decide +kernel

theorem prime_1545332960933 : Nat.Prime 1545332960933 := by
  apply nodeValid_prime [2, 386333240233] ⟨1545332960933, 2, [(2, 2), (386333240233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_386333240233
  · decide +kernel

end Sude.Lucas.Generated
