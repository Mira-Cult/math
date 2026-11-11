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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0095

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4259 : Nat.Prime 4259 := by
  apply nodeValid_prime [2, 2129] ⟨4259, 2, [(2, 1), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2129
  · decide +kernel

theorem prime_9931 : Nat.Prime 9931 := by
  apply nodeValid_prime [2, 3, 5, 331] ⟨9931, 10, [(2, 1), (3, 1), (5, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_331
  · decide +kernel

theorem prime_11497 : Nat.Prime 11497 := by
  apply nodeValid_prime [2, 3, 479] ⟨11497, 7, [(2, 3), (3, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
  · decide +kernel

theorem prime_11719 : Nat.Prime 11719 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨11719, 6, [(2, 1), (3, 3), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_17107 : Nat.Prime 17107 := by
  apply nodeValid_prime [2, 3, 2851] ⟨17107, 3, [(2, 1), (3, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2851
  · decide +kernel

theorem prime_19069 : Nat.Prime 19069 := by
  apply nodeValid_prime [2, 3, 7, 227] ⟨19069, 2, [(2, 2), (3, 1), (7, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_227
  · decide +kernel

theorem prime_20101 : Nat.Prime 20101 := by
  apply nodeValid_prime [2, 3, 5, 67] ⟨20101, 6, [(2, 2), (3, 1), (5, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_22147 : Nat.Prime 22147 := by
  apply nodeValid_prime [2, 3, 3691] ⟨22147, 5, [(2, 1), (3, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3691
  · decide +kernel

theorem prime_27943 : Nat.Prime 27943 := by
  apply nodeValid_prime [2, 3, 4657] ⟨27943, 5, [(2, 1), (3, 1), (4657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4657
  · decide +kernel

theorem prime_31541 : Nat.Prime 31541 := by
  apply nodeValid_prime [2, 5, 19, 83] ⟨31541, 3, [(2, 2), (5, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_39089 : Nat.Prime 39089 := by
  apply nodeValid_prime [2, 7, 349] ⟨39089, 3, [(2, 4), (7, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_349
  · decide +kernel

theorem prime_39623 : Nat.Prime 39623 := by
  apply nodeValid_prime [2, 11, 1801] ⟨39623, 5, [(2, 1), (11, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1801
  · decide +kernel

theorem prime_49117 : Nat.Prime 49117 := by
  apply nodeValid_prime [2, 3, 4093] ⟨49117, 2, [(2, 2), (3, 1), (4093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4093
  · decide +kernel

theorem prime_50461 : Nat.Prime 50461 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨50461, 7, [(2, 2), (3, 1), (5, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_54293 : Nat.Prime 54293 := by
  apply nodeValid_prime [2, 7, 277] ⟨54293, 2, [(2, 2), (7, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_64763 : Nat.Prime 64763 := by
  apply nodeValid_prime [2, 32381] ⟨64763, 2, [(2, 1), (32381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32381
  · decide +kernel

theorem prime_65357 : Nat.Prime 65357 := by
  apply nodeValid_prime [2, 16339] ⟨65357, 2, [(2, 2), (16339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16339
  · decide +kernel

theorem prime_70957 : Nat.Prime 70957 := by
  apply nodeValid_prime [2, 3, 73] ⟨70957, 2, [(2, 2), (3, 5), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_73943 : Nat.Prime 73943 := by
  apply nodeValid_prime [2, 11, 3361] ⟨73943, 5, [(2, 1), (11, 1), (3361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3361
  · decide +kernel

theorem prime_74093 : Nat.Prime 74093 := by
  apply nodeValid_prime [2, 18523] ⟨74093, 2, [(2, 2), (18523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18523
  · decide +kernel

theorem prime_83701 : Nat.Prime 83701 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨83701, 6, [(2, 2), (3, 3), (5, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_85361 : Nat.Prime 85361 := by
  apply nodeValid_prime [2, 5, 11, 97] ⟨85361, 3, [(2, 4), (5, 1), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_100291 : Nat.Prime 100291 := by
  apply nodeValid_prime [2, 3, 5, 3343] ⟨100291, 3, [(2, 1), (3, 1), (5, 1), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3343
  · decide +kernel

theorem prime_107747 : Nat.Prime 107747 := by
  apply nodeValid_prime [2, 17, 3169] ⟨107747, 2, [(2, 1), (17, 1), (3169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3169
  · decide +kernel

theorem prime_117991 : Nat.Prime 117991 := by
  apply nodeValid_prime [2, 3, 5, 19, 23] ⟨117991, 3, [(2, 1), (3, 3), (5, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_125287 : Nat.Prime 125287 := by
  apply nodeValid_prime [2, 3, 7, 19, 157] ⟨125287, 3, [(2, 1), (3, 1), (7, 1), (19, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_157
  · decide +kernel

theorem prime_152563 : Nat.Prime 152563 := by
  apply nodeValid_prime [2, 3, 47, 541] ⟨152563, 3, [(2, 1), (3, 1), (47, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_541
  · decide +kernel

theorem prime_187573 : Nat.Prime 187573 := by
  apply nodeValid_prime [2, 3, 7, 11, 29] ⟨187573, 2, [(2, 2), (3, 1), (7, 2), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_200989 : Nat.Prime 200989 := by
  apply nodeValid_prime [2, 3, 1861] ⟨200989, 2, [(2, 2), (3, 3), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1861
  · decide +kernel

theorem prime_210533 : Nat.Prime 210533 := by
  apply nodeValid_prime [2, 7, 73, 103] ⟨210533, 2, [(2, 2), (7, 1), (73, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_103
  · decide +kernel

theorem prime_234281 : Nat.Prime 234281 := by
  apply nodeValid_prime [2, 5, 5857] ⟨234281, 6, [(2, 3), (5, 1), (5857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5857
  · decide +kernel

theorem prime_262553 : Nat.Prime 262553 := by
  apply nodeValid_prime [2, 37, 887] ⟨262553, 3, [(2, 3), (37, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_887
  · decide +kernel

theorem prime_264343 : Nat.Prime 264343 := by
  apply nodeValid_prime [2, 3, 13, 3389] ⟨264343, 3, [(2, 1), (3, 1), (13, 1), (3389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3389
  · decide +kernel

theorem prime_274283 : Nat.Prime 274283 := by
  apply nodeValid_prime [2, 29, 4729] ⟨274283, 2, [(2, 1), (29, 1), (4729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_4729
  · decide +kernel

theorem prime_294703 : Nat.Prime 294703 := by
  apply nodeValid_prime [2, 3, 49117] ⟨294703, 5, [(2, 1), (3, 1), (49117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49117
  · decide +kernel

theorem prime_319129 : Nat.Prime 319129 := by
  apply nodeValid_prime [2, 3, 13297] ⟨319129, 11, [(2, 3), (3, 1), (13297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13297
  · decide +kernel

theorem prime_461627 : Nat.Prime 461627 := by
  apply nodeValid_prime [2, 11, 20983] ⟨461627, 6, [(2, 1), (11, 1), (20983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_20983
  · decide +kernel

theorem prime_467063 : Nat.Prime 467063 := by
  apply nodeValid_prime [2, 347, 673] ⟨467063, 5, [(2, 1), (347, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_673
  · decide +kernel

theorem prime_471089 : Nat.Prime 471089 := by
  apply nodeValid_prime [2, 29443] ⟨471089, 3, [(2, 4), (29443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29443
  · decide +kernel

theorem prime_522857 : Nat.Prime 522857 := by
  apply nodeValid_prime [2, 65357] ⟨522857, 3, [(2, 3), (65357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_65357
  · decide +kernel

theorem prime_581639 : Nat.Prime 581639 := by
  apply nodeValid_prime [2, 17, 17107] ⟨581639, 7, [(2, 1), (17, 1), (17107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_17107
  · decide +kernel

theorem prime_773939 : Nat.Prime 773939 := by
  apply nodeValid_prime [2, 11, 127, 277] ⟨773939, 2, [(2, 1), (11, 1), (127, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_277
  · decide +kernel

theorem prime_826349 : Nat.Prime 826349 := by
  apply nodeValid_prime [2, 19, 83, 131] ⟨826349, 2, [(2, 2), (19, 1), (83, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_83
    · exact prime_131
  · decide +kernel

theorem prime_885881 : Nat.Prime 885881 := by
  apply nodeValid_prime [2, 5, 22147] ⟨885881, 3, [(2, 3), (5, 1), (22147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22147
  · decide +kernel

theorem prime_886537 : Nat.Prime 886537 := by
  apply nodeValid_prime [2, 3, 7, 1759] ⟨886537, 5, [(2, 3), (3, 2), (7, 1), (1759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1759
  · decide +kernel

theorem prime_1547879 : Nat.Prime 1547879 := by
  apply nodeValid_prime [2, 773939] ⟨1547879, 7, [(2, 1), (773939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_773939
  · decide +kernel

theorem prime_1575653 : Nat.Prime 1575653 := by
  apply nodeValid_prime [2, 13, 157, 193] ⟨1575653, 2, [(2, 2), (13, 1), (157, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_157
    · exact prime_193
  · decide +kernel

theorem prime_1892461 : Nat.Prime 1892461 := by
  apply nodeValid_prime [2, 3, 5, 31541] ⟨1892461, 2, [(2, 2), (3, 1), (5, 1), (31541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31541
  · decide +kernel

theorem prime_2208337 : Nat.Prime 2208337 := by
  apply nodeValid_prime [2, 3, 13, 3539] ⟨2208337, 11, [(2, 4), (3, 1), (13, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3539
  · decide +kernel

theorem prime_2411869 : Nat.Prime 2411869 := by
  apply nodeValid_prime [2, 3, 200989] ⟨2411869, 6, [(2, 2), (3, 1), (200989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_200989
  · decide +kernel

theorem prime_2479691 : Nat.Prime 2479691 := by
  apply nodeValid_prime [2, 5, 19, 31, 421] ⟨2479691, 2, [(2, 1), (5, 1), (19, 1), (31, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_31
    · exact prime_421
  · decide +kernel

theorem prime_2667349 : Nat.Prime 2667349 := by
  apply nodeValid_prime [2, 3, 74093] ⟨2667349, 2, [(2, 2), (3, 2), (74093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74093
  · decide +kernel

theorem prime_2891789 : Nat.Prime 2891789 := by
  apply nodeValid_prime [2, 89, 8123] ⟨2891789, 2, [(2, 2), (89, 1), (8123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_8123
  · decide +kernel

theorem prime_3013237 : Nat.Prime 3013237 := by
  apply nodeValid_prime [2, 3, 83701] ⟨3013237, 6, [(2, 2), (3, 2), (83701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83701
  · decide +kernel

theorem prime_3365833 : Nat.Prime 3365833 := by
  apply nodeValid_prime [2, 3, 59, 2377] ⟨3365833, 43, [(2, 3), (3, 1), (59, 1), (2377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2377
  · decide +kernel

theorem prime_3463307 : Nat.Prime 3463307 := by
  apply nodeValid_prime [2, 7, 11, 43, 523] ⟨3463307, 2, [(2, 1), (7, 1), (11, 1), (43, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_43
    · exact prime_523
  · decide +kernel

theorem prime_3850837 : Nat.Prime 3850837 := by
  apply nodeValid_prime [2, 3, 11, 29173] ⟨3850837, 2, [(2, 2), (3, 1), (11, 1), (29173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29173
  · decide +kernel

theorem prime_4921061 : Nat.Prime 4921061 := by
  apply nodeValid_prime [2, 5, 197, 1249] ⟨4921061, 2, [(2, 2), (5, 1), (197, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
    · exact prime_1249
  · decide +kernel

theorem prime_5783579 : Nat.Prime 5783579 := by
  apply nodeValid_prime [2, 2891789] ⟨5783579, 2, [(2, 1), (2891789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2891789
  · decide +kernel

theorem prime_5960389 : Nat.Prime 5960389 := by
  apply nodeValid_prime [2, 3, 7, 70957] ⟨5960389, 2, [(2, 2), (3, 1), (7, 1), (70957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_70957
  · decide +kernel

theorem prime_6740387 : Nat.Prime 6740387 := by
  apply nodeValid_prime [2, 229, 14717] ⟨6740387, 2, [(2, 1), (229, 1), (14717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_14717
  · decide +kernel

theorem prime_6824369 : Nat.Prime 6824369 := by
  apply nodeValid_prime [2, 41, 101, 103] ⟨6824369, 3, [(2, 4), (41, 1), (101, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_101
    · exact prime_103
  · decide +kernel

theorem prime_7072873 : Nat.Prime 7072873 := by
  apply nodeValid_prime [2, 3, 294703] ⟨7072873, 7, [(2, 3), (3, 1), (294703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_294703
  · decide +kernel

theorem prime_7127639 : Nat.Prime 7127639 := by
  apply nodeValid_prime [2, 7, 257, 283] ⟨7127639, 7, [(2, 1), (7, 2), (257, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_257
    · exact prime_283
  · decide +kernel

theorem prime_9417701 : Nat.Prime 9417701 := by
  apply nodeValid_prime [2, 5, 41, 2297] ⟨9417701, 2, [(2, 2), (5, 2), (41, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_2297
  · decide +kernel

theorem prime_10228219 : Nat.Prime 10228219 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 131] ⟨10228219, 10, [(2, 1), (3, 1), (7, 1), (11, 1), (13, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_131
  · decide +kernel

theorem prime_10294169 : Nat.Prime 10294169 := by
  apply nodeValid_prime [2, 73, 17627] ⟨10294169, 3, [(2, 3), (73, 1), (17627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_17627
  · decide +kernel

theorem prime_11423459 : Nat.Prime 11423459 := by
  apply nodeValid_prime [2, 449, 12721] ⟨11423459, 2, [(2, 1), (449, 1), (12721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_449
    · exact prime_12721
  · decide +kernel

theorem prime_11770357 : Nat.Prime 11770357 := by
  apply nodeValid_prime [2, 3, 13, 197, 383] ⟨11770357, 2, [(2, 2), (3, 1), (13, 1), (197, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_197
    · exact prime_383
  · decide +kernel

theorem prime_18903817 : Nat.Prime 18903817 := by
  apply nodeValid_prime [2, 3, 262553] ⟨18903817, 5, [(2, 3), (3, 2), (262553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_262553
  · decide +kernel

theorem prime_21379399 : Nat.Prime 21379399 := by
  apply nodeValid_prime [2, 3, 31, 137, 839] ⟨21379399, 17, [(2, 1), (3, 1), (31, 1), (137, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_137
    · exact prime_839
  · decide +kernel

theorem prime_22781393 : Nat.Prime 22781393 := by
  apply nodeValid_prime [2, 313, 4549] ⟨22781393, 3, [(2, 4), (313, 1), (4549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_4549
  · decide +kernel

theorem prime_32968877 : Nat.Prime 32968877 := by
  apply nodeValid_prime [2, 19, 461, 941] ⟨32968877, 2, [(2, 2), (19, 1), (461, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_461
    · exact prime_941
  · decide +kernel

theorem prime_33663479 : Nat.Prime 33663479 := by
  apply nodeValid_prime [2, 19, 885881] ⟨33663479, 11, [(2, 1), (19, 1), (885881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_885881
  · decide +kernel

theorem prime_33813991 : Nat.Prime 33813991 := by
  apply nodeValid_prime [2, 3, 5, 7, 17891] ⟨33813991, 12, [(2, 1), (3, 3), (5, 1), (7, 1), (17891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17891
  · decide +kernel

theorem prime_35501077 : Nat.Prime 35501077 := by
  apply nodeValid_prime [2, 3, 13, 31, 2447] ⟨35501077, 5, [(2, 2), (3, 2), (13, 1), (31, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_2447
  · decide +kernel

theorem prime_53000089 : Nat.Prime 53000089 := by
  apply nodeValid_prime [2, 3, 2208337] ⟨53000089, 11, [(2, 3), (3, 1), (2208337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2208337
  · decide +kernel

theorem prime_72356071 : Nat.Prime 72356071 := by
  apply nodeValid_prime [2, 3, 5, 2411869] ⟨72356071, 3, [(2, 1), (3, 1), (5, 1), (2411869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2411869
  · decide +kernel

theorem prime_84874477 : Nat.Prime 84874477 := by
  apply nodeValid_prime [2, 3, 7072873] ⟨84874477, 2, [(2, 2), (3, 1), (7072873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7072873
  · decide +kernel

theorem prime_94182301 : Nat.Prime 94182301 := by
  apply nodeValid_prime [2, 3, 5, 227, 461] ⟨94182301, 2, [(2, 2), (3, 2), (5, 2), (227, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_227
    · exact prime_461
  · decide +kernel

theorem prime_123307469 : Nat.Prime 123307469 := by
  apply nodeValid_prime [2, 53, 581639] ⟨123307469, 2, [(2, 2), (53, 1), (581639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_581639
  · decide +kernel

theorem prime_144336737 : Nat.Prime 144336737 := by
  apply nodeValid_prime [2, 61, 73943] ⟨144336737, 3, [(2, 5), (61, 1), (73943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_73943
  · decide +kernel

theorem prime_147631831 : Nat.Prime 147631831 := by
  apply nodeValid_prime [2, 3, 5, 4921061] ⟨147631831, 6, [(2, 1), (3, 1), (5, 1), (4921061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4921061
  · decide +kernel

theorem prime_246614939 : Nat.Prime 246614939 := by
  apply nodeValid_prime [2, 123307469] ⟨246614939, 2, [(2, 1), (123307469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_123307469
  · decide +kernel

theorem prime_267949841 : Nat.Prime 267949841 := by
  apply nodeValid_prime [2, 5, 601, 5573] ⟨267949841, 3, [(2, 4), (5, 1), (601, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_601
    · exact prime_5573
  · decide +kernel

theorem prime_486034007 : Nat.Prime 486034007 := by
  apply nodeValid_prime [2, 157, 1547879] ⟨486034007, 5, [(2, 1), (157, 1), (1547879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_1547879
  · decide +kernel

theorem prime_493229879 : Nat.Prime 493229879 := by
  apply nodeValid_prime [2, 246614939] ⟨493229879, 7, [(2, 1), (246614939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_246614939
  · decide +kernel

theorem prime_594256697 : Nat.Prime 594256697 := by
  apply nodeValid_prime [2, 11, 1151, 5867] ⟨594256697, 3, [(2, 3), (11, 1), (1151, 1), (5867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1151
    · exact prime_5867
  · decide +kernel

theorem prime_759429383 : Nat.Prime 759429383 := by
  apply nodeValid_prime [2, 31, 61, 113, 1777] ⟨759429383, 5, [(2, 1), (31, 1), (61, 1), (113, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_61
    · exact prime_113
    · exact prime_1777
  · decide +kernel

theorem prime_1199602631 : Nat.Prime 1199602631 := by
  apply nodeValid_prime [2, 5, 127, 661, 1429] ⟨1199602631, 13, [(2, 1), (5, 1), (127, 1), (661, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_661
    · exact prime_1429
  · decide +kernel

theorem prime_1601671657 : Nat.Prime 1601671657 := by
  apply nodeValid_prime [2, 3, 13, 1129, 4547] ⟨1601671657, 5, [(2, 3), (3, 1), (13, 1), (1129, 1), (4547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1129
    · exact prime_4547
  · decide +kernel

theorem prime_1881903967 : Nat.Prime 1881903967 := by
  apply nodeValid_prime [2, 3, 53, 109, 54293] ⟨1881903967, 5, [(2, 1), (3, 1), (53, 1), (109, 1), (54293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_109
    · exact prime_54293
  · decide +kernel

theorem prime_3125341327 : Nat.Prime 3125341327 := by
  apply nodeValid_prime [2, 3, 2777, 187573] ⟨3125341327, 3, [(2, 1), (3, 1), (2777, 1), (187573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2777
    · exact prime_187573
  · decide +kernel

theorem prime_3247900283 : Nat.Prime 3247900283 := by
  apply nodeValid_prime [2, 11, 147631831] ⟨3247900283, 2, [(2, 1), (11, 1), (147631831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_147631831
  · decide +kernel

theorem prime_3456517951 : Nat.Prime 3456517951 := by
  apply nodeValid_prime [2, 3, 5, 59, 101, 1289] ⟨3456517951, 6, [(2, 1), (3, 2), (5, 2), (59, 1), (101, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_101
    · exact prime_1289
  · decide +kernel

theorem prime_3956265241 : Nat.Prime 3956265241 := by
  apply nodeValid_prime [2, 3, 5, 32968877] ⟨3956265241, 13, [(2, 3), (3, 1), (5, 1), (32968877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_32968877
  · decide +kernel

theorem prime_4284409949 : Nat.Prime 4284409949 := by
  apply nodeValid_prime [2, 7, 13, 11770357] ⟨4284409949, 2, [(2, 2), (7, 1), (13, 1), (11770357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_11770357
  · decide +kernel

theorem prime_5961191963 : Nat.Prime 5961191963 := by
  apply nodeValid_prime [2, 11, 9697, 27943] ⟨5961191963, 2, [(2, 1), (11, 1), (9697, 1), (27943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9697
    · exact prime_27943
  · decide +kernel

theorem prime_7312171681 : Nat.Prime 7312171681 := by
  apply nodeValid_prime [2, 3, 5, 11, 461627] ⟨7312171681, 7, [(2, 5), (3, 2), (5, 1), (11, 1), (461627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_461627
  · decide +kernel

theorem prime_8748612127 : Nat.Prime 8748612127 := by
  apply nodeValid_prime [2, 3, 486034007] ⟨8748612127, 3, [(2, 1), (3, 2), (486034007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_486034007
  · decide +kernel

theorem prime_8987681767 : Nat.Prime 8987681767 := by
  apply nodeValid_prime [2, 3, 7, 37, 5783579] ⟨8987681767, 6, [(2, 1), (3, 1), (7, 1), (37, 1), (5783579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_5783579
  · decide +kernel

theorem prime_11922383927 : Nat.Prime 11922383927 := by
  apply nodeValid_prime [2, 5961191963] ⟨11922383927, 5, [(2, 1), (5961191963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5961191963
  · decide +kernel

theorem prime_19522340671 : Nat.Prime 19522340671 := by
  apply nodeValid_prime [2, 3, 5, 7, 59, 1575653] ⟨19522340671, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (1575653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_1575653
  · decide +kernel

theorem prime_24990608407 : Nat.Prime 24990608407 := by
  apply nodeValid_prime [2, 3, 59, 1399, 50461] ⟨24990608407, 6, [(2, 1), (3, 1), (59, 1), (1399, 1), (50461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_1399
    · exact prime_50461
  · decide +kernel

theorem prime_25183202221 : Nat.Prime 25183202221 := by
  apply nodeValid_prime [2, 3, 5, 11, 149, 85361] ⟨25183202221, 2, [(2, 2), (3, 2), (5, 1), (11, 1), (149, 1), (85361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_149
    · exact prime_85361
  · decide +kernel

theorem prime_33261161707 : Nat.Prime 33261161707 := by
  apply nodeValid_prime [2, 3, 61, 3365833] ⟨33261161707, 2, [(2, 1), (3, 4), (61, 1), (3365833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_3365833
  · decide +kernel

theorem prime_47475182893 : Nat.Prime 47475182893 := by
  apply nodeValid_prime [2, 3, 3956265241] ⟨47475182893, 2, [(2, 2), (3, 1), (3956265241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3956265241
  · decide +kernel

theorem prime_52364087933 : Nat.Prime 52364087933 := by
  apply nodeValid_prime [2, 13, 19, 53000089] ⟨52364087933, 2, [(2, 2), (13, 1), (19, 1), (53000089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_53000089
  · decide +kernel

theorem prime_99962433629 : Nat.Prime 99962433629 := by
  apply nodeValid_prime [2, 24990608407] ⟨99962433629, 2, [(2, 2), (24990608407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24990608407
  · decide +kernel

theorem prime_133044646829 : Nat.Prime 133044646829 := by
  apply nodeValid_prime [2, 33261161707] ⟨133044646829, 2, [(2, 2), (33261161707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33261161707
  · decide +kernel

theorem prime_143326380811 : Nat.Prime 143326380811 := by
  apply nodeValid_prime [2, 3, 5, 131, 4259, 8563] ⟨143326380811, 3, [(2, 1), (3, 1), (5, 1), (131, 1), (4259, 1), (8563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_4259
    · exact prime_8563
  · decide +kernel

theorem prime_798983469619 : Nat.Prime 798983469619 := by
  apply nodeValid_prime [2, 3, 41, 3247900283] ⟨798983469619, 2, [(2, 1), (3, 1), (41, 1), (3247900283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_3247900283
  · decide +kernel

theorem prime_1600831935023 : Nat.Prime 1600831935023 := by
  apply nodeValid_prime [2, 41, 19522340671] ⟨1600831935023, 5, [(2, 1), (41, 1), (19522340671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_19522340671
  · decide +kernel

theorem prime_3133362070939 : Nat.Prime 3133362070939 := by
  apply nodeValid_prime [2, 3, 11, 47475182893] ⟨3133362070939, 3, [(2, 1), (3, 1), (11, 1), (47475182893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47475182893
  · decide +kernel

theorem prime_3133362072173 : Nat.Prime 3133362072173 := by
  apply nodeValid_prime [2, 653, 1199602631] ⟨3133362072173, 2, [(2, 2), (653, 1), (1199602631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_653
    · exact prime_1199602631
  · decide +kernel

theorem prime_3136188077707 : Nat.Prime 3136188077707 := by
  apply nodeValid_prime [2, 3, 37, 101, 3163, 44221] ⟨3136188077707, 2, [(2, 1), (3, 1), (37, 1), (101, 1), (3163, 1), (44221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_101
    · exact prime_3163
    · exact prime_44221
  · decide +kernel

theorem prime_3136188081079 : Nat.Prime 3136188081079 := by
  apply nodeValid_prime [2, 3, 13, 19069, 234281] ⟨3136188081079, 3, [(2, 1), (3, 3), (13, 1), (19069, 1), (234281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19069
    · exact prime_234281
  · decide +kernel

theorem prime_3136188082669 : Nat.Prime 3136188082669 := by
  apply nodeValid_prime [2, 3, 61, 4284409949] ⟨3136188082669, 6, [(2, 2), (3, 1), (61, 1), (4284409949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_4284409949
  · decide +kernel

theorem prime_3139015813303 : Nat.Prime 3139015813303 := by
  apply nodeValid_prime [2, 3, 97, 107, 471089] ⟨3139015813303, 5, [(2, 1), (3, 1), (97, 1), (107, 2), (471089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_107
    · exact prime_471089
  · decide +kernel

theorem prime_3139015813597 : Nat.Prime 3139015813597 := by
  apply nodeValid_prime [2, 3, 13, 151, 311, 47609] ⟨3139015813597, 18, [(2, 2), (3, 3), (13, 1), (151, 1), (311, 1), (47609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_151
    · exact prime_311
    · exact prime_47609
  · decide +kernel

theorem prime_3139015816957 : Nat.Prime 3139015816957 := by
  apply nodeValid_prime [2, 3, 139, 1881903967] ⟨3139015816957, 2, [(2, 2), (3, 1), (139, 1), (1881903967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_1881903967
  · decide +kernel

theorem prime_3141845275981 : Nat.Prime 3141845275981 := by
  apply nodeValid_prime [2, 3, 5, 52364087933] ⟨3141845275981, 10, [(2, 2), (3, 1), (5, 1), (52364087933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_52364087933
  · decide +kernel

theorem prime_3141845314501 : Nat.Prime 3141845314501 := by
  apply nodeValid_prime [2, 3, 5, 59, 35501077] ⟨3141845314501, 2, [(2, 2), (3, 1), (5, 3), (59, 1), (35501077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_35501077
  · decide +kernel

theorem prime_3141845314963 : Nat.Prime 3141845314963 := by
  apply nodeValid_prime [2, 3, 7237, 72356071] ⟨3141845314963, 2, [(2, 1), (3, 1), (7237, 1), (72356071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7237
    · exact prime_72356071
  · decide +kernel

theorem prime_3144676438249 : Nat.Prime 3144676438249 := by
  apply nodeValid_prime [2, 3, 49123, 2667349] ⟨3144676438249, 13, [(2, 3), (3, 1), (49123, 1), (2667349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49123
    · exact prime_2667349
  · decide +kernel

theorem prime_3144676456321 : Nat.Prime 3144676456321 := by
  apply nodeValid_prime [2, 3, 5, 7, 2333, 100291] ⟨3144676456321, 19, [(2, 7), (3, 1), (5, 1), (7, 1), (2333, 1), (100291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2333
    · exact prime_100291
  · decide +kernel

theorem prime_3147509356729 : Nat.Prime 3147509356729 := by
  apply nodeValid_prime [2, 3, 11, 11922383927] ⟨3147509356729, 14, [(2, 3), (3, 1), (11, 1), (11922383927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_11922383927
  · decide +kernel

theorem prime_3147509376317 : Nat.Prime 3147509376317 := by
  apply nodeValid_prime [2, 619, 20101, 63241] ⟨3147509376317, 2, [(2, 2), (619, 1), (20101, 1), (63241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_20101
    · exact prime_63241
  · decide +kernel

theorem prime_3147509376433 : Nat.Prime 3147509376433 := by
  apply nodeValid_prime [2, 3, 2137, 10228219] ⟨3147509376433, 5, [(2, 4), (3, 2), (2137, 1), (10228219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2137
    · exact prime_10228219
  · decide +kernel

theorem prime_3150343988279 : Nat.Prime 3150343988279 := by
  apply nodeValid_prime [2, 83, 193, 1621, 60661] ⟨3150343988279, 11, [(2, 1), (83, 1), (193, 1), (1621, 1), (60661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_193
    · exact prime_1621
    · exact prime_60661
  · decide +kernel

theorem prime_3150344057573 : Nat.Prime 3150344057573 := by
  apply nodeValid_prime [2, 23, 409, 2113, 39623] ⟨3150344057573, 2, [(2, 2), (23, 1), (409, 1), (2113, 1), (39623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_409
    · exact prime_2113
    · exact prime_39623
  · decide +kernel

theorem prime_3150344057617 : Nat.Prime 3150344057617 := by
  apply nodeValid_prime [2, 3, 7, 3125341327] ⟨3150344057617, 20, [(2, 4), (3, 2), (7, 1), (3125341327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3125341327
  · decide +kernel

theorem prime_3153180356503 : Nat.Prime 3153180356503 := by
  apply nodeValid_prime [2, 3, 11, 331, 144336737] ⟨3153180356503, 3, [(2, 1), (3, 1), (11, 1), (331, 1), (144336737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_331
    · exact prime_144336737
  · decide +kernel

theorem prime_3153180377843 : Nat.Prime 3153180377843 := by
  apply nodeValid_prime [2, 11, 143326380811] ⟨3153180377843, 2, [(2, 1), (11, 1), (143326380811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_143326380811
  · decide +kernel

theorem prime_3156018454471 : Nat.Prime 3156018454471 := by
  apply nodeValid_prime [2, 3, 5, 7, 101, 1381, 107747] ⟨3156018454471, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (101, 1), (1381, 1), (107747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_101
    · exact prime_1381
    · exact prime_107747
  · decide +kernel

theorem prime_3156018482443 : Nat.Prime 3156018482443 := by
  apply nodeValid_prime [2, 3, 7, 17, 19, 229, 8537] ⟨3156018482443, 2, [(2, 1), (3, 1), (7, 2), (17, 2), (19, 1), (229, 1), (8537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
    · exact prime_229
    · exact prime_8537
  · decide +kernel

theorem prime_3156018483209 : Nat.Prime 3156018483209 := by
  apply nodeValid_prime [2, 11719, 33663479] ⟨3156018483209, 3, [(2, 3), (11719, 1), (33663479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11719
    · exact prime_33663479
  · decide +kernel

theorem prime_3158858166019 : Nat.Prime 3158858166019 := by
  apply nodeValid_prime [2, 3, 6569, 6971, 11497] ⟨3158858166019, 3, [(2, 1), (3, 1), (6569, 1), (6971, 1), (11497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6569
    · exact prime_6971
    · exact prime_11497
  · decide +kernel

theorem prime_3158858166193 : Nat.Prime 3158858166193 := by
  apply nodeValid_prime [2, 3, 7312171681] ⟨3158858166193, 5, [(2, 4), (3, 3), (7312171681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7312171681
  · decide +kernel

theorem prime_3158858284987 : Nat.Prime 3158858284987 := by
  apply nodeValid_prime [2, 3, 6203, 84874477] ⟨3158858284987, 2, [(2, 1), (3, 1), (6203, 1), (84874477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6203
    · exact prime_84874477
  · decide +kernel

theorem prime_3161699844571 : Nat.Prime 3161699844571 := by
  apply nodeValid_prime [2, 3, 5, 373, 94182301] ⟨3161699844571, 2, [(2, 1), (3, 2), (5, 1), (373, 1), (94182301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_373
    · exact prime_94182301
  · decide +kernel

theorem prime_3161699849317 : Nat.Prime 3161699849317 := by
  apply nodeValid_prime [2, 3, 39089, 6740387] ⟨3161699849317, 5, [(2, 2), (3, 1), (39089, 1), (6740387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39089
    · exact prime_6740387
  · decide +kernel

theorem prime_3161699850919 : Nat.Prime 3161699850919 := by
  apply nodeValid_prime [2, 3, 7, 47, 1601671657] ⟨3161699850919, 3, [(2, 1), (3, 1), (7, 1), (47, 1), (1601671657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_1601671657
  · decide +kernel

theorem prime_3164543139437 : Nat.Prime 3164543139437 := by
  apply nodeValid_prime [2, 7, 31, 241, 2749, 5503] ⟨3164543139437, 2, [(2, 2), (7, 1), (31, 1), (241, 1), (2749, 1), (5503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_241
    · exact prime_2749
    · exact prime_5503
  · decide +kernel

theorem prime_3164543159821 : Nat.Prime 3164543159821 := by
  apply nodeValid_prime [2, 3, 5, 7, 67, 71, 593, 2671] ⟨3164543159821, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (67, 1), (71, 1), (593, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_67
    · exact prime_71
    · exact prime_593
    · exact prime_2671
  · decide +kernel

theorem prime_3164543160253 : Nat.Prime 3164543160253 := by
  apply nodeValid_prime [2, 3, 319129, 826349] ⟨3164543160253, 2, [(2, 2), (3, 1), (319129, 1), (826349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_319129
    · exact prime_826349
  · decide +kernel

theorem prime_3167388178447 : Nat.Prime 3167388178447 := by
  apply nodeValid_prime [2, 3, 41, 4273, 3013237] ⟨3167388178447, 3, [(2, 1), (3, 1), (41, 1), (4273, 1), (3013237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_4273
    · exact prime_3013237
  · decide +kernel

theorem prime_3167388194363 : Nat.Prime 3167388194363 := by
  apply nodeValid_prime [2, 7, 9931, 22781393] ⟨3167388194363, 2, [(2, 1), (7, 1), (9931, 1), (22781393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9931
    · exact prime_22781393
  · decide +kernel

theorem prime_3167388195011 : Nat.Prime 3167388195011 := by
  apply nodeValid_prime [2, 5, 13, 41, 594256697] ⟨3167388195011, 6, [(2, 1), (5, 1), (13, 1), (41, 1), (594256697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_594256697
  · decide +kernel

theorem prime_3170234950549 : Nat.Prime 3170234950549 := by
  apply nodeValid_prime [2, 3, 59, 9587, 467063] ⟨3170234950549, 2, [(2, 2), (3, 1), (59, 1), (9587, 1), (467063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_9587
    · exact prime_467063
  · decide +kernel

theorem prime_3170235035047 : Nat.Prime 3170235035047 := by
  apply nodeValid_prime [2, 3, 152563, 3463307] ⟨3170235035047, 3, [(2, 1), (3, 1), (152563, 1), (3463307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152563
    · exact prime_3463307
  · decide +kernel

theorem prime_3170235035113 : Nat.Prime 3170235035113 := by
  apply nodeValid_prime [2, 3, 37, 4027, 886537] ⟨3170235035113, 5, [(2, 3), (3, 1), (37, 1), (4027, 1), (886537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4027
    · exact prime_886537
  · decide +kernel

theorem prime_3173083447231 : Nat.Prime 3173083447231 := by
  apply nodeValid_prime [2, 3, 5, 61, 103, 971, 5779] ⟨3173083447231, 6, [(2, 1), (3, 2), (5, 1), (61, 1), (103, 1), (971, 1), (5779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_103
    · exact prime_971
    · exact prime_5779
  · decide +kernel

theorem prime_3173083479019 : Nat.Prime 3173083479019 := by
  apply nodeValid_prime [2, 3, 17, 3456517951] ⟨3173083479019, 2, [(2, 1), (3, 3), (17, 1), (3456517951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3456517951
  · decide +kernel

theorem prime_3173083479847 : Nat.Prime 3173083479847 := by
  apply nodeValid_prime [2, 3, 7, 25183202221] ⟨3173083479847, 5, [(2, 1), (3, 2), (7, 1), (25183202221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_25183202221
  · decide +kernel

theorem prime_3175933674761 : Nat.Prime 3175933674761 := by
  apply nodeValid_prime [2, 5, 7, 11, 173, 5960389] ⟨3175933674761, 12, [(2, 3), (5, 1), (7, 1), (11, 1), (173, 1), (5960389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_173
    · exact prime_5960389
  · decide +kernel

theorem prime_3175933679599 : Nat.Prime 3175933679599 := by
  apply nodeValid_prime [2, 3, 23, 9281, 2479691] ⟨3175933679599, 3, [(2, 1), (3, 1), (23, 1), (9281, 1), (2479691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_9281
    · exact prime_2479691
  · decide +kernel

theorem prime_3175933679707 : Nat.Prime 3175933679707 := by
  apply nodeValid_prime [2, 3, 17, 41, 759429383] ⟨3175933679707, 2, [(2, 1), (3, 1), (17, 1), (41, 1), (759429383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_759429383
  · decide +kernel

theorem prime_3178785643681 : Nat.Prime 3178785643681 := by
  apply nodeValid_prime [2, 3, 5, 293, 349, 64763] ⟨3178785643681, 19, [(2, 5), (3, 1), (5, 1), (293, 1), (349, 1), (64763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_349
    · exact prime_64763
  · decide +kernel

theorem prime_3178785665929 : Nat.Prime 3178785665929 := by
  apply nodeValid_prime [2, 3, 3917, 33813991] ⟨3178785665929, 19, [(2, 3), (3, 1), (3917, 1), (33813991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3917
    · exact prime_33813991
  · decide +kernel

theorem prime_3178785666311 : Nat.Prime 3178785666311 := by
  apply nodeValid_prime [2, 5, 167971, 1892461] ⟨3178785666311, 13, [(2, 1), (5, 1), (167971, 1), (1892461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167971
    · exact prime_1892461
  · decide +kernel

theorem prime_3181639345519 : Nat.Prime 3181639345519 := by
  apply nodeValid_prime [2, 3, 59, 8987681767] ⟨3181639345519, 3, [(2, 1), (3, 1), (59, 1), (8987681767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_8987681767
  · decide +kernel

theorem prime_3181639400383 : Nat.Prime 3181639400383 := by
  apply nodeValid_prime [2, 3, 17, 1459, 21379399] ⟨3181639400383, 3, [(2, 1), (3, 1), (17, 1), (1459, 1), (21379399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1459
    · exact prime_21379399
  · decide +kernel

theorem prime_3181639401169 : Nat.Prime 3181639401169 := by
  apply nodeValid_prime [2, 3, 47, 137, 10294169] ⟨3181639401169, 14, [(2, 4), (3, 1), (47, 1), (137, 1), (10294169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_137
    · exact prime_10294169
  · decide +kernel

theorem prime_3184494788711 : Nat.Prime 3184494788711 := by
  apply nodeValid_prime [2, 5, 269, 5623, 210533] ⟨3184494788711, 11, [(2, 1), (5, 1), (269, 1), (5623, 1), (210533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_5623
    · exact prime_210533
  · decide +kernel

theorem prime_3184494814229 : Nat.Prime 3184494814229 := by
  apply nodeValid_prime [2, 7, 13, 8748612127] ⟨3184494814229, 2, [(2, 2), (7, 1), (13, 1), (8748612127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_8748612127
  · decide +kernel

theorem prime_3184494818513 : Nat.Prime 3184494818513 := by
  apply nodeValid_prime [2, 7, 19, 131, 11423459] ⟨3184494818513, 3, [(2, 4), (7, 1), (19, 1), (131, 1), (11423459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_131
    · exact prime_11423459
  · decide +kernel

theorem prime_3187351863259 : Nat.Prime 3187351863259 := by
  apply nodeValid_prime [2, 3, 17, 397, 3533, 22279] ⟨3187351863259, 2, [(2, 1), (3, 1), (17, 1), (397, 1), (3533, 1), (22279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_397
    · exact prime_3533
    · exact prime_22279
  · decide +kernel

theorem prime_3187351863299 : Nat.Prime 3187351863299 := by
  apply nodeValid_prime [2, 37, 6043, 7127639] ⟨3187351863299, 2, [(2, 1), (37, 1), (6043, 1), (7127639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_6043
    · exact prime_7127639
  · decide +kernel

theorem prime_3187351957711 : Nat.Prime 3187351957711 := by
  apply nodeValid_prime [2, 3, 5, 17, 11953, 522857] ⟨3187351957711, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (11953, 1), (522857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_11953
    · exact prime_522857
  · decide +kernel

theorem prime_3190210806947 : Nat.Prime 3190210806947 := by
  apply nodeValid_prime [2, 5953, 267949841] ⟨3190210806947, 2, [(2, 1), (5953, 1), (267949841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5953
    · exact prime_267949841
  · decide +kernel

theorem prime_3190210807037 : Nat.Prime 3190210807037 := by
  apply nodeValid_prime [2, 11, 264343, 274283] ⟨3190210807037, 2, [(2, 2), (11, 1), (264343, 1), (274283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_264343
    · exact prime_274283
  · decide +kernel

theorem prime_3190210857373 : Nat.Prime 3190210857373 := by
  apply nodeValid_prime [2, 3, 7, 11, 493229879] ⟨3190210857373, 2, [(2, 2), (3, 1), (7, 2), (11, 1), (493229879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_493229879
  · decide +kernel

theorem prime_3193071498073 : Nat.Prime 3193071498073 := by
  apply nodeValid_prime [2, 3, 117991, 125287] ⟨3193071498073, 5, [(2, 3), (3, 3), (117991, 1), (125287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_117991
    · exact prime_125287
  · decide +kernel

theorem prime_3193071523897 : Nat.Prime 3193071523897 := by
  apply nodeValid_prime [2, 3, 133044646829] ⟨3193071523897, 7, [(2, 3), (3, 1), (133044646829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_133044646829
  · decide +kernel

theorem prime_3193071524051 : Nat.Prime 3193071524051 := by
  apply nodeValid_prime [2, 5, 6781, 9417701] ⟨3193071524051, 2, [(2, 1), (5, 2), (6781, 1), (9417701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6781
    · exact prime_9417701
  · decide +kernel

theorem prime_3195933878477 : Nat.Prime 3195933878477 := by
  apply nodeValid_prime [2, 798983469619] ⟨3195933878477, 2, [(2, 2), (798983469619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_798983469619
  · decide +kernel

theorem prime_3195933894553 : Nat.Prime 3195933894553 := by
  apply nodeValid_prime [2, 3, 7, 1553, 3221, 3803] ⟨3195933894553, 19, [(2, 3), (3, 1), (7, 1), (1553, 1), (3221, 1), (3803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1553
    · exact prime_3221
    · exact prime_3803
  · decide +kernel

theorem prime_3195933895129 : Nat.Prime 3195933895129 := by
  apply nodeValid_prime [2, 3, 13, 19, 79, 6824369] ⟨3195933895129, 7, [(2, 3), (3, 1), (13, 1), (19, 1), (79, 1), (6824369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_79
    · exact prime_6824369
  · decide +kernel

theorem prime_3198797875813 : Nat.Prime 3198797875813 := by
  apply nodeValid_prime [2, 3, 7, 11, 29, 31, 3850837] ⟨3198797875813, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (29, 1), (31, 1), (3850837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_31
    · exact prime_3850837
  · decide +kernel

theorem prime_3198797876129 : Nat.Prime 3198797876129 := by
  apply nodeValid_prime [2, 99962433629] ⟨3198797876129, 3, [(2, 5), (99962433629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_99962433629
  · decide +kernel

theorem prime_3198797992771 : Nat.Prime 3198797992771 := by
  apply nodeValid_prime [2, 3, 5, 17, 191, 1259, 26083] ⟨3198797992771, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (191, 1), (1259, 1), (26083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_191
    · exact prime_1259
    · exact prime_26083
  · decide +kernel

theorem prime_3201663846583 : Nat.Prime 3201663846583 := by
  apply nodeValid_prime [2, 3, 17, 31, 8389, 13411] ⟨3201663846583, 3, [(2, 1), (3, 3), (17, 1), (31, 1), (8389, 1), (13411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_8389
    · exact prime_13411
  · decide +kernel

theorem prime_3201663870023 : Nat.Prime 3201663870023 := by
  apply nodeValid_prime [2, 19, 4457, 18903817] ⟨3201663870023, 5, [(2, 1), (19, 1), (4457, 1), (18903817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4457
    · exact prime_18903817
  · decide +kernel

theorem prime_3201663870047 : Nat.Prime 3201663870047 := by
  apply nodeValid_prime [2, 1600831935023] ⟨3201663870047, 5, [(2, 1), (1600831935023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1600831935023
  · decide +kernel

end Sude.Lucas.Generated
