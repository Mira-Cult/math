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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0128
import Sude.GeneratedFTT.N0129

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_16453 : Nat.Prime 16453 := by
  apply nodeValid_prime [2, 3, 457] ⟨16453, 2, [(2, 2), (3, 2), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_457
  · decide +kernel

theorem prime_16519 : Nat.Prime 16519 := by
  apply nodeValid_prime [2, 3, 2753] ⟨16519, 3, [(2, 1), (3, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2753
  · decide +kernel

theorem prime_20107 : Nat.Prime 20107 := by
  apply nodeValid_prime [2, 3, 1117] ⟨20107, 2, [(2, 1), (3, 2), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1117
  · decide +kernel

theorem prime_23537 : Nat.Prime 23537 := by
  apply nodeValid_prime [2, 1471] ⟨23537, 3, [(2, 4), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1471
  · decide +kernel

theorem prime_33107 : Nat.Prime 33107 := by
  apply nodeValid_prime [2, 16553] ⟨33107, 2, [(2, 1), (16553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16553
  · decide +kernel

theorem prime_34019 : Nat.Prime 34019 := by
  apply nodeValid_prime [2, 73, 233] ⟨34019, 2, [(2, 1), (73, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_233
  · decide +kernel

theorem prime_34501 : Nat.Prime 34501 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨34501, 7, [(2, 2), (3, 1), (5, 3), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_39929 : Nat.Prime 39929 := by
  apply nodeValid_prime [2, 7, 23, 31] ⟨39929, 3, [(2, 3), (7, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_41681 : Nat.Prime 41681 := by
  apply nodeValid_prime [2, 5, 521] ⟨41681, 3, [(2, 4), (5, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_521
  · decide +kernel

theorem prime_46171 : Nat.Prime 46171 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨46171, 3, [(2, 1), (3, 5), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_47977 : Nat.Prime 47977 := by
  apply nodeValid_prime [2, 3, 1999] ⟨47977, 7, [(2, 3), (3, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1999
  · decide +kernel

theorem prime_73867 : Nat.Prime 73867 := by
  apply nodeValid_prime [2, 3, 13, 947] ⟨73867, 2, [(2, 1), (3, 1), (13, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_947
  · decide +kernel

theorem prime_74357 : Nat.Prime 74357 := by
  apply nodeValid_prime [2, 29, 641] ⟨74357, 2, [(2, 2), (29, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_641
  · decide +kernel

theorem prime_80191 : Nat.Prime 80191 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨80191, 11, [(2, 1), (3, 6), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_106453 : Nat.Prime 106453 := by
  apply nodeValid_prime [2, 3, 2957] ⟨106453, 6, [(2, 2), (3, 2), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2957
  · decide +kernel

theorem prime_116201 : Nat.Prime 116201 := by
  apply nodeValid_prime [2, 5, 7, 83] ⟨116201, 3, [(2, 3), (5, 2), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_121711 : Nat.Prime 121711 := by
  apply nodeValid_prime [2, 3, 5, 4057] ⟨121711, 3, [(2, 1), (3, 1), (5, 1), (4057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4057
  · decide +kernel

theorem prime_135559 : Nat.Prime 135559 := by
  apply nodeValid_prime [2, 3, 17, 443] ⟨135559, 3, [(2, 1), (3, 2), (17, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_443
  · decide +kernel

theorem prime_138179 : Nat.Prime 138179 := by
  apply nodeValid_prime [2, 59, 1171] ⟨138179, 2, [(2, 1), (59, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_1171
  · decide +kernel

theorem prime_157823 : Nat.Prime 157823 := by
  apply nodeValid_prime [2, 7, 11273] ⟨157823, 5, [(2, 1), (7, 1), (11273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11273
  · decide +kernel

theorem prime_167221 : Nat.Prime 167221 := by
  apply nodeValid_prime [2, 3, 5, 929] ⟨167221, 2, [(2, 2), (3, 2), (5, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_929
  · decide +kernel

theorem prime_167443 : Nat.Prime 167443 := by
  apply nodeValid_prime [2, 3, 11, 43, 59] ⟨167443, 2, [(2, 1), (3, 1), (11, 1), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_174337 : Nat.Prime 174337 := by
  apply nodeValid_prime [2, 3, 227] ⟨174337, 5, [(2, 8), (3, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
  · decide +kernel

theorem prime_205357 : Nat.Prime 205357 := by
  apply nodeValid_prime [2, 3, 109, 157] ⟨205357, 6, [(2, 2), (3, 1), (109, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_157
  · decide +kernel

theorem prime_238921 : Nat.Prime 238921 := by
  apply nodeValid_prime [2, 3, 5, 11, 181] ⟨238921, 23, [(2, 3), (3, 1), (5, 1), (11, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_181
  · decide +kernel

theorem prime_376769 : Nat.Prime 376769 := by
  apply nodeValid_prime [2, 7, 29] ⟨376769, 6, [(2, 6), (7, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_503653 : Nat.Prime 503653 := by
  apply nodeValid_prime [2, 3, 19, 47] ⟨503653, 5, [(2, 2), (3, 1), (19, 1), (47, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_506983 : Nat.Prime 506983 := by
  apply nodeValid_prime [2, 3, 7, 12071] ⟨506983, 5, [(2, 1), (3, 1), (7, 1), (12071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12071
  · decide +kernel

theorem prime_641833 : Nat.Prime 641833 := by
  apply nodeValid_prime [2, 3, 47, 569] ⟨641833, 5, [(2, 3), (3, 1), (47, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_569
  · decide +kernel

theorem prime_720763 : Nat.Prime 720763 := by
  apply nodeValid_prime [2, 3, 7, 131] ⟨720763, 2, [(2, 1), (3, 1), (7, 1), (131, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_131
  · decide +kernel

theorem prime_740191 : Nat.Prime 740191 := by
  apply nodeValid_prime [2, 3, 5, 11, 2243] ⟨740191, 12, [(2, 1), (3, 1), (5, 1), (11, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2243
  · decide +kernel

theorem prime_765379 : Nat.Prime 765379 := by
  apply nodeValid_prime [2, 3, 101, 421] ⟨765379, 3, [(2, 1), (3, 2), (101, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_421
  · decide +kernel

theorem prime_807707 : Nat.Prime 807707 := by
  apply nodeValid_prime [2, 223, 1811] ⟨807707, 2, [(2, 1), (223, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_1811
  · decide +kernel

theorem prime_924109 : Nat.Prime 924109 := by
  apply nodeValid_prime [2, 3, 53, 1453] ⟨924109, 2, [(2, 2), (3, 1), (53, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1453
  · decide +kernel

theorem prime_947377 : Nat.Prime 947377 := by
  apply nodeValid_prime [2, 3, 17, 43] ⟨947377, 5, [(2, 4), (3, 4), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_1000981 : Nat.Prime 1000981 := by
  apply nodeValid_prime [2, 3, 5, 67, 83] ⟨1000981, 6, [(2, 2), (3, 2), (5, 1), (67, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_83
  · decide +kernel

theorem prime_1047271 : Nat.Prime 1047271 := by
  apply nodeValid_prime [2, 3, 5, 7, 4987] ⟨1047271, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_4987
  · decide +kernel

theorem prime_1075643 : Nat.Prime 1075643 := by
  apply nodeValid_prime [2, 47, 11443] ⟨1075643, 2, [(2, 1), (47, 1), (11443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_11443
  · decide +kernel

theorem prime_1175149 : Nat.Prime 1175149 := by
  apply nodeValid_prime [2, 3, 13, 31] ⟨1175149, 6, [(2, 2), (3, 6), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_1249433 : Nat.Prime 1249433 := by
  apply nodeValid_prime [2, 17, 9187] ⟨1249433, 3, [(2, 3), (17, 1), (9187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9187
  · decide +kernel

theorem prime_1279253 : Nat.Prime 1279253 := by
  apply nodeValid_prime [2, 13, 73, 337] ⟨1279253, 2, [(2, 2), (13, 1), (73, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_337
  · decide +kernel

theorem prime_1694551 : Nat.Prime 1694551 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 79] ⟨1694551, 3, [(2, 1), (3, 1), (5, 2), (11, 1), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_1819957 : Nat.Prime 1819957 := by
  apply nodeValid_prime [2, 3, 37, 4099] ⟨1819957, 2, [(2, 2), (3, 1), (37, 1), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4099
  · decide +kernel

theorem prime_2040173 : Nat.Prime 2040173 := by
  apply nodeValid_prime [2, 31, 16453] ⟨2040173, 2, [(2, 2), (31, 1), (16453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_16453
  · decide +kernel

theorem prime_2290573 : Nat.Prime 2290573 := by
  apply nodeValid_prime [2, 3, 127, 167] ⟨2290573, 2, [(2, 2), (3, 3), (127, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_167
  · decide +kernel

theorem prime_2466097 : Nat.Prime 2466097 := by
  apply nodeValid_prime [2, 3, 83, 619] ⟨2466097, 23, [(2, 4), (3, 1), (83, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_619
  · decide +kernel

theorem prime_2677643 : Nat.Prime 2677643 := by
  apply nodeValid_prime [2, 11, 121711] ⟨2677643, 2, [(2, 1), (11, 1), (121711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_121711
  · decide +kernel

theorem prime_3462469 : Nat.Prime 3462469 := by
  apply nodeValid_prime [2, 3, 288539] ⟨3462469, 2, [(2, 2), (3, 1), (288539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_288539
  · decide +kernel

theorem prime_4480897 : Nat.Prime 4480897 := by
  apply nodeValid_prime [2, 3, 7, 1667] ⟨4480897, 10, [(2, 7), (3, 1), (7, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1667
  · decide +kernel

theorem prime_4863083 : Nat.Prime 4863083 := by
  apply nodeValid_prime [2, 7, 79, 4397] ⟨4863083, 2, [(2, 1), (7, 1), (79, 1), (4397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_4397
  · decide +kernel

theorem prime_4997689 : Nat.Prime 4997689 := by
  apply nodeValid_prime [2, 3, 53, 3929] ⟨4997689, 17, [(2, 3), (3, 1), (53, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_3929
  · decide +kernel

theorem prime_5249411 : Nat.Prime 5249411 := by
  apply nodeValid_prime [2, 5, 524941] ⟨5249411, 2, [(2, 1), (5, 1), (524941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_524941
  · decide +kernel

theorem prime_5597351 : Nat.Prime 5597351 := by
  apply nodeValid_prime [2, 5, 11, 10177] ⟨5597351, 7, [(2, 1), (5, 2), (11, 1), (10177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_10177
  · decide +kernel

theorem prime_6005887 : Nat.Prime 6005887 := by
  apply nodeValid_prime [2, 3, 1000981] ⟨6005887, 5, [(2, 1), (3, 1), (1000981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1000981
  · decide +kernel

theorem prime_7361551 : Nat.Prime 7361551 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 41] ⟨7361551, 7, [(2, 1), (3, 3), (5, 2), (7, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_7461667 : Nat.Prime 7461667 := by
  apply nodeValid_prime [2, 3, 138179] ⟨7461667, 5, [(2, 1), (3, 3), (138179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_138179
  · decide +kernel

theorem prime_7517287 : Nat.Prime 7517287 := by
  apply nodeValid_prime [2, 3, 7, 947] ⟨7517287, 3, [(2, 1), (3, 4), (7, 2), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_947
  · decide +kernel

theorem prime_8111729 : Nat.Prime 8111729 := by
  apply nodeValid_prime [2, 506983] ⟨8111729, 3, [(2, 4), (506983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_506983
  · decide +kernel

theorem prime_9241091 : Nat.Prime 9241091 := by
  apply nodeValid_prime [2, 5, 924109] ⟨9241091, 2, [(2, 1), (5, 1), (924109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_924109
  · decide +kernel

theorem prime_9316451 : Nat.Prime 9316451 := by
  apply nodeValid_prime [2, 5, 11, 13, 1303] ⟨9316451, 7, [(2, 1), (5, 2), (11, 1), (13, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_1303
  · decide +kernel

theorem prime_9812287 : Nat.Prime 9812287 := by
  apply nodeValid_prime [2, 3, 11, 16519] ⟨9812287, 7, [(2, 1), (3, 3), (11, 1), (16519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_16519
  · decide +kernel

theorem prime_11528417 : Nat.Prime 11528417 := by
  apply nodeValid_prime [2, 313, 1151] ⟨11528417, 3, [(2, 5), (313, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_1151
  · decide +kernel

theorem prime_15635237 : Nat.Prime 15635237 := by
  apply nodeValid_prime [2, 59, 97, 683] ⟨15635237, 2, [(2, 2), (59, 1), (97, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_97
    · exact prime_683
  · decide +kernel

theorem prime_17052787 : Nat.Prime 17052787 := by
  apply nodeValid_prime [2, 3, 947377] ⟨17052787, 2, [(2, 1), (3, 2), (947377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_947377
  · decide +kernel

theorem prime_17752411 : Nat.Prime 17752411 := by
  apply nodeValid_prime [2, 3, 5, 13, 15173] ⟨17752411, 3, [(2, 1), (3, 2), (5, 1), (13, 1), (15173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_15173
  · decide +kernel

theorem prime_20292997 : Nat.Prime 20292997 := by
  apply nodeValid_prime [2, 3, 181, 9343] ⟨20292997, 2, [(2, 2), (3, 1), (181, 1), (9343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_9343
  · decide +kernel

theorem prime_21608029 : Nat.Prime 21608029 := by
  apply nodeValid_prime [2, 3, 13, 46171] ⟨21608029, 2, [(2, 2), (3, 2), (13, 1), (46171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_46171
  · decide +kernel

theorem prime_23909729 : Nat.Prime 23909729 := by
  apply nodeValid_prime [2, 281, 2659] ⟨23909729, 3, [(2, 5), (281, 1), (2659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_2659
  · decide +kernel

theorem prime_34380713 : Nat.Prime 34380713 := by
  apply nodeValid_prime [2, 359, 11971] ⟨34380713, 3, [(2, 3), (359, 1), (11971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_11971
  · decide +kernel

theorem prime_45502057 : Nat.Prime 45502057 := by
  apply nodeValid_prime [2, 3, 521, 1213] ⟨45502057, 5, [(2, 3), (3, 2), (521, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_1213
  · decide +kernel

theorem prime_45515651 : Nat.Prime 45515651 := by
  apply nodeValid_prime [2, 5, 101, 9013] ⟨45515651, 2, [(2, 1), (5, 2), (101, 1), (9013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_9013
  · decide +kernel

theorem prime_47240189 : Nat.Prime 47240189 := by
  apply nodeValid_prime [2, 29, 449, 907] ⟨47240189, 2, [(2, 2), (29, 1), (449, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_449
    · exact prime_907
  · decide +kernel

theorem prime_50852353 : Nat.Prime 50852353 := by
  apply nodeValid_prime [2, 3, 33107] ⟨50852353, 5, [(2, 9), (3, 1), (33107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33107
  · decide +kernel

theorem prime_65435857 : Nat.Prime 65435857 := by
  apply nodeValid_prime [2, 3, 17, 80191] ⟨65435857, 5, [(2, 4), (3, 1), (17, 1), (80191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_80191
  · decide +kernel

theorem prime_122341801 : Nat.Prime 122341801 := by
  apply nodeValid_prime [2, 3, 5, 7, 29129] ⟨122341801, 19, [(2, 3), (3, 1), (5, 2), (7, 1), (29129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29129
  · decide +kernel

theorem prime_146011123 : Nat.Prime 146011123 := by
  apply nodeValid_prime [2, 3, 8111729] ⟨146011123, 11, [(2, 1), (3, 2), (8111729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8111729
  · decide +kernel

theorem prime_157043879 : Nat.Prime 157043879 := by
  apply nodeValid_prime [2, 73, 1075643] ⟨157043879, 11, [(2, 1), (73, 1), (1075643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1075643
  · decide +kernel

theorem prime_158402947 : Nat.Prime 158402947 := by
  apply nodeValid_prime [2, 3, 13, 101, 20107] ⟨158402947, 2, [(2, 1), (3, 1), (13, 1), (101, 1), (20107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
    · exact prime_20107
  · decide +kernel

theorem prime_239525873 : Nat.Prime 239525873 := by
  apply nodeValid_prime [2, 1471, 10177] ⟨239525873, 3, [(2, 4), (1471, 1), (10177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1471
    · exact prime_10177
  · decide +kernel

theorem prime_374054873 : Nat.Prime 374054873 := by
  apply nodeValid_prime [2, 1171, 39929] ⟨374054873, 3, [(2, 3), (1171, 1), (39929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1171
    · exact prime_39929
  · decide +kernel

theorem prime_380302249 : Nat.Prime 380302249 := by
  apply nodeValid_prime [2, 3, 1051, 15077] ⟨380302249, 7, [(2, 3), (3, 1), (1051, 1), (15077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1051
    · exact prime_15077
  · decide +kernel

theorem prime_413726069 : Nat.Prime 413726069 := by
  apply nodeValid_prime [2, 7, 109, 135559] ⟨413726069, 2, [(2, 2), (7, 1), (109, 1), (135559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109
    · exact prime_135559
  · decide +kernel

theorem prime_566882269 : Nat.Prime 566882269 := by
  apply nodeValid_prime [2, 3, 47240189] ⟨566882269, 6, [(2, 2), (3, 1), (47240189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47240189
  · decide +kernel

theorem prime_622534519 : Nat.Prime 622534519 := by
  apply nodeValid_prime [2, 3, 11528417] ⟨622534519, 3, [(2, 1), (3, 3), (11528417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11528417
  · decide +kernel

theorem prime_839602651 : Nat.Prime 839602651 := by
  apply nodeValid_prime [2, 3, 5, 5597351] ⟨839602651, 2, [(2, 1), (3, 1), (5, 2), (5597351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5597351
  · decide +kernel

theorem prime_860366149 : Nat.Prime 860366149 := by
  apply nodeValid_prime [2, 3, 4363, 16433] ⟨860366149, 2, [(2, 2), (3, 1), (4363, 1), (16433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4363
    · exact prime_16433
  · decide +kernel

theorem prime_934866631 : Nat.Prime 934866631 := by
  apply nodeValid_prime [2, 3, 5, 3462469] ⟨934866631, 3, [(2, 1), (3, 3), (5, 1), (3462469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3462469
  · decide +kernel

theorem prime_1975087613 : Nat.Prime 1975087613 := by
  apply nodeValid_prime [2, 53, 9316451] ⟨1975087613, 2, [(2, 2), (53, 1), (9316451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_9316451
  · decide +kernel

theorem prime_2750167169 : Nat.Prime 2750167169 := by
  apply nodeValid_prime [2, 7, 41, 43, 1741] ⟨2750167169, 6, [(2, 7), (7, 1), (41, 1), (43, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_43
    · exact prime_1741
  · decide +kernel

theorem prime_2815438741 : Nat.Prime 2815438741 := by
  apply nodeValid_prime [2, 3, 5, 23, 2040173] ⟨2815438741, 2, [(2, 2), (3, 1), (5, 1), (23, 1), (2040173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_2040173
  · decide +kernel

theorem prime_2894100431 : Nat.Prime 2894100431 := by
  apply nodeValid_prime [2, 5, 13, 631, 35281] ⟨2894100431, 17, [(2, 1), (5, 1), (13, 1), (631, 1), (35281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_631
    · exact prime_35281
  · decide +kernel

theorem prime_3697321819 : Nat.Prime 3697321819 := by
  apply nodeValid_prime [2, 3, 79, 83, 93979] ⟨3697321819, 2, [(2, 1), (3, 1), (79, 1), (83, 1), (93979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_83
    · exact prime_93979
  · decide +kernel

theorem prime_3801670729 : Nat.Prime 3801670729 := by
  apply nodeValid_prime [2, 3, 158402947] ⟨3801670729, 7, [(2, 3), (3, 1), (158402947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_158402947
  · decide +kernel

theorem prime_4345404907 : Nat.Prime 4345404907 := by
  apply nodeValid_prime [2, 3, 61, 71, 167221] ⟨4345404907, 3, [(2, 1), (3, 1), (61, 1), (71, 1), (167221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_71
    · exact prime_167221
  · decide +kernel

theorem prime_4790517461 : Nat.Prime 4790517461 := by
  apply nodeValid_prime [2, 5, 239525873] ⟨4790517461, 2, [(2, 2), (5, 1), (239525873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239525873
  · decide +kernel

theorem prime_4829733287 : Nat.Prime 4829733287 := by
  apply nodeValid_prime [2, 7, 17, 20292997] ⟨4829733287, 5, [(2, 1), (7, 1), (17, 1), (20292997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_20292997
  · decide +kernel

theorem prime_5157106951 : Nat.Prime 5157106951 := by
  apply nodeValid_prime [2, 3, 5, 34380713] ⟨5157106951, 12, [(2, 1), (3, 1), (5, 2), (34380713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_34380713
  · decide +kernel

theorem prime_5568645821 : Nat.Prime 5568645821 := by
  apply nodeValid_prime [2, 5, 739, 376769] ⟨5568645821, 2, [(2, 2), (5, 1), (739, 1), (376769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_739
    · exact prime_376769
  · decide +kernel

theorem prime_6130788817 : Nat.Prime 6130788817 := by
  apply nodeValid_prime [2, 3, 199, 641833] ⟨6130788817, 19, [(2, 4), (3, 1), (199, 1), (641833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_641833
  · decide +kernel

theorem prime_16680017869 : Nat.Prime 16680017869 := by
  apply nodeValid_prime [2, 3, 23539, 59051] ⟨16680017869, 2, [(2, 2), (3, 1), (23539, 1), (59051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23539
    · exact prime_59051
  · decide +kernel

theorem prime_21163521839 : Nat.Prime 21163521839 := by
  apply nodeValid_prime [2, 257, 3167, 13001] ⟨21163521839, 11, [(2, 1), (257, 1), (3167, 1), (13001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_3167
    · exact prime_13001
  · decide +kernel

theorem prime_33098085269 : Nat.Prime 33098085269 := by
  apply nodeValid_prime [2, 257, 433, 74357] ⟨33098085269, 2, [(2, 2), (257, 1), (433, 1), (74357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_433
    · exact prime_74357
  · decide +kernel

theorem prime_35711538263 : Nat.Prime 35711538263 := by
  apply nodeValid_prime [2, 2393, 7461667] ⟨35711538263, 5, [(2, 1), (2393, 1), (7461667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2393
    · exact prime_7461667
  · decide +kernel

theorem prime_36107002103 : Nat.Prime 36107002103 := by
  apply nodeValid_prime [2, 29, 622534519] ⟨36107002103, 7, [(2, 1), (29, 1), (622534519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_622534519
  · decide +kernel

theorem prime_131917918049 : Nat.Prime 131917918049 := by
  apply nodeValid_prime [2, 7, 131, 191, 23537] ⟨131917918049, 3, [(2, 5), (7, 1), (131, 1), (191, 1), (23537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_191
    · exact prime_23537
  · decide +kernel

theorem prime_132012708389 : Nat.Prime 132012708389 := by
  apply nodeValid_prime [2, 11, 59, 50852353] ⟨132012708389, 2, [(2, 2), (11, 1), (59, 1), (50852353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_50852353
  · decide +kernel

theorem prime_132392342081 : Nat.Prime 132392342081 := by
  apply nodeValid_prime [2, 5, 413726069] ⟨132392342081, 3, [(2, 6), (5, 1), (413726069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_413726069
  · decide +kernel

theorem prime_214575751639 : Nat.Prime 214575751639 := by
  apply nodeValid_prime [2, 3, 23, 41, 3041, 4157] ⟨214575751639, 3, [(2, 1), (3, 2), (23, 1), (41, 1), (3041, 1), (4157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_3041
    · exact prime_4157
  · decide +kernel

theorem prime_316603000061 : Nat.Prime 316603000061 := by
  apply nodeValid_prime [2, 5, 6911, 2290573] ⟨316603000061, 2, [(2, 2), (5, 1), (6911, 1), (2290573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6911
    · exact prime_2290573
  · decide +kernel

theorem prime_355585751387 : Nat.Prime 355585751387 := by
  apply nodeValid_prime [2, 29, 6130788817] ⟨355585751387, 2, [(2, 1), (29, 1), (6130788817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_6130788817
  · decide +kernel

theorem prime_792076259069 : Nat.Prime 792076259069 := by
  apply nodeValid_prime [2, 41, 4829733287] ⟨792076259069, 2, [(2, 2), (41, 1), (4829733287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_4829733287
  · decide +kernel

theorem prime_1583015016589 : Nat.Prime 1583015016589 := by
  apply nodeValid_prime [2, 3, 131917918049] ⟨1583015016589, 2, [(2, 2), (3, 1), (131917918049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131917918049
  · decide +kernel

theorem prime_1594415039179 : Nat.Prime 1594415039179 := by
  apply nodeValid_prime [2, 3, 13, 53, 431, 449, 1993] ⟨1594415039179, 17, [(2, 1), (3, 1), (13, 1), (53, 1), (431, 1), (449, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_431
    · exact prime_449
    · exact prime_1993
  · decide +kernel

theorem prime_3172858434611 : Nat.Prime 3172858434611 := by
  apply nodeValid_prime [2, 5, 19, 367, 45502057] ⟨3172858434611, 2, [(2, 1), (5, 1), (19, 1), (367, 1), (45502057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_367
    · exact prime_45502057
  · decide +kernel

theorem prime_3172858435091 : Nat.Prime 3172858435091 := by
  apply nodeValid_prime [2, 5, 174337, 1819957] ⟨3172858435091, 6, [(2, 1), (5, 1), (174337, 1), (1819957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_174337
    · exact prime_1819957
  · decide +kernel

theorem prime_6327512145673 : Nat.Prime 6327512145673 := by
  apply nodeValid_prime [2, 3, 97, 277, 9812287] ⟨6327512145673, 5, [(2, 3), (3, 1), (97, 1), (277, 1), (9812287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_277
    · exact prime_9812287
  · decide +kernel

theorem prime_6327512230667 : Nat.Prime 6327512230667 := by
  apply nodeValid_prime [2, 11, 244747, 1175149] ⟨6327512230667, 2, [(2, 1), (11, 1), (244747, 1), (1175149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_244747
    · exact prime_1175149
  · decide +kernel

theorem prime_6327512231669 : Nat.Prime 6327512231669 := by
  apply nodeValid_prime [2, 4229, 374054873] ⟨6327512231669, 2, [(2, 2), (4229, 1), (374054873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4229
    · exact prime_374054873
  · decide +kernel

theorem prime_6332060001221 : Nat.Prime 6332060001221 := by
  apply nodeValid_prime [2, 5, 316603000061] ⟨6332060001221, 2, [(2, 2), (5, 1), (316603000061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_316603000061
  · decide +kernel

theorem prime_6332060066357 : Nat.Prime 6332060066357 := by
  apply nodeValid_prime [2, 1583015016589] ⟨6332060066357, 2, [(2, 2), (1583015016589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1583015016589
  · decide +kernel

theorem prime_6332060066417 : Nat.Prime 6332060066417 := by
  apply nodeValid_prime [2, 7, 73867, 765379] ⟨6332060066417, 3, [(2, 4), (7, 1), (73867, 1), (765379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73867
    · exact prime_765379
  · decide +kernel

theorem prime_6336610002673 : Nat.Prime 6336610002673 := by
  apply nodeValid_prime [2, 3, 132012708389] ⟨6336610002673, 5, [(2, 4), (3, 1), (132012708389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132012708389
  · decide +kernel

theorem prime_6336610002883 : Nat.Prime 6336610002883 := by
  apply nodeValid_prime [2, 3, 23, 566882269] ⟨6336610002883, 3, [(2, 1), (3, 5), (23, 1), (566882269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_566882269
  · decide +kernel

theorem prime_6336610072553 : Nat.Prime 6336610072553 := by
  apply nodeValid_prime [2, 792076259069] ⟨6336610072553, 3, [(2, 3), (792076259069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_792076259069
  · decide +kernel

theorem prime_6341162343457 : Nat.Prime 6341162343457 := by
  apply nodeValid_prime [2, 3, 29, 1823, 1249433] ⟨6341162343457, 5, [(2, 5), (3, 1), (29, 1), (1823, 1), (1249433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1823
    · exact prime_1249433
  · decide +kernel

theorem prime_6341162345129 : Nat.Prime 6341162345129 := by
  apply nodeValid_prime [2, 13, 8111, 7517287] ⟨6341162345129, 3, [(2, 3), (13, 1), (8111, 1), (7517287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8111
    · exact prime_7517287
  · decide +kernel

theorem prime_6341162351591 : Nat.Prime 6341162351591 := by
  apply nodeValid_prime [2, 5, 11, 34019, 1694551] ⟨6341162351591, 7, [(2, 1), (5, 1), (11, 1), (34019, 1), (1694551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_34019
    · exact prime_1694551
  · decide +kernel

theorem prime_6345716836259 : Nat.Prime 6345716836259 := by
  apply nodeValid_prime [2, 3779, 839602651] ⟨6345716836259, 2, [(2, 1), (3779, 1), (839602651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3779
    · exact prime_839602651
  · decide +kernel

theorem prime_6345716869223 : Nat.Prime 6345716869223 := by
  apply nodeValid_prime [2, 3172858434611] ⟨6345716869223, 5, [(2, 1), (3172858434611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3172858434611
  · decide +kernel

theorem prime_6345716870183 : Nat.Prime 6345716870183 := by
  apply nodeValid_prime [2, 3172858435091] ⟨6345716870183, 5, [(2, 1), (3172858435091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3172858435091
  · decide +kernel

theorem prime_6350273522707 : Nat.Prime 6350273522707 := by
  apply nodeValid_prime [2, 3, 41, 211, 122341801] ⟨6350273522707, 2, [(2, 1), (3, 1), (41, 1), (211, 1), (122341801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_211
    · exact prime_122341801
  · decide +kernel

theorem prime_6350273546339 : Nat.Prime 6350273546339 := by
  apply nodeValid_prime [2, 211, 3011, 4997689] ⟨6350273546339, 2, [(2, 1), (211, 1), (3011, 1), (4997689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_3011
    · exact prime_4997689
  · decide +kernel

theorem prime_6350273547641 : Nat.Prime 6350273547641 := by
  apply nodeValid_prime [2, 5, 11, 19, 4813, 157823] ⟨6350273547641, 3, [(2, 3), (5, 1), (11, 1), (19, 1), (4813, 1), (157823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_4813
    · exact prime_157823
  · decide +kernel

theorem prime_6354832370129 : Nat.Prime 6354832370129 := by
  apply nodeValid_prime [2, 11, 36107002103] ⟨6354832370129, 6, [(2, 4), (11, 1), (36107002103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_36107002103
  · decide +kernel

theorem prime_6354832371649 : Nat.Prime 6354832371649 := by
  apply nodeValid_prime [2, 3, 33098085269] ⟨6354832371649, 7, [(2, 6), (3, 1), (33098085269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33098085269
  · decide +kernel

theorem prime_6354832419889 : Nat.Prime 6354832419889 := by
  apply nodeValid_prime [2, 3, 132392342081] ⟨6354832419889, 13, [(2, 4), (3, 1), (132392342081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132392342081
  · decide +kernel

theorem prime_6359393527583 : Nat.Prime 6359393527583 := by
  apply nodeValid_prime [2, 571, 5568645821] ⟨6359393527583, 5, [(2, 1), (571, 1), (5568645821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_571
    · exact prime_5568645821
  · decide +kernel

theorem prime_6359393528681 : Nat.Prime 6359393528681 := by
  apply nodeValid_prime [2, 5, 43, 3697321819] ⟨6359393528681, 3, [(2, 3), (5, 1), (43, 1), (3697321819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_3697321819
  · decide +kernel

theorem prime_6359393539189 : Nat.Prime 6359393539189 := by
  apply nodeValid_prime [2, 3, 1151, 17052787] ⟨6359393539189, 2, [(2, 2), (3, 4), (1151, 1), (17052787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1151
    · exact prime_17052787
  · decide +kernel

theorem prime_6363956853959 : Nat.Prime 6363956853959 := by
  apply nodeValid_prime [2, 11, 17, 3499, 4863083] ⟨6363956853959, 11, [(2, 1), (11, 1), (17, 1), (3499, 1), (4863083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_3499
    · exact prime_4863083
  · decide +kernel

theorem prime_6363956854139 : Nat.Prime 6363956854139 := by
  apply nodeValid_prime [2, 13, 211, 24179, 47977] ⟨6363956854139, 6, [(2, 1), (13, 1), (211, 1), (24179, 1), (47977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_211
    · exact prime_24179
    · exact prime_47977
  · decide +kernel

theorem prime_6363956872759 : Nat.Prime 6363956872759 := by
  apply nodeValid_prime [2, 3, 2311, 2741, 167443] ⟨6363956872759, 13, [(2, 1), (3, 1), (2311, 1), (2741, 1), (167443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2311
    · exact prime_2741
    · exact prime_167443
  · decide +kernel

theorem prime_6368522408503 : Nat.Prime 6368522408503 := by
  apply nodeValid_prime [2, 3, 17, 34501, 106453] ⟨6368522408503, 3, [(2, 1), (3, 1), (17, 2), (34501, 1), (106453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_34501
    · exact prime_106453
  · decide +kernel

theorem prime_6368522432143 : Nat.Prime 6368522432143 := by
  apply nodeValid_prime [2, 3, 13, 29, 2815438741] ⟨6368522432143, 6, [(2, 1), (3, 1), (13, 1), (29, 1), (2815438741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_2815438741
  · decide +kernel

theorem prime_6368522432269 : Nat.Prime 6368522432269 := by
  apply nodeValid_prime [2, 3, 17, 19, 313, 5249411] ⟨6368522432269, 2, [(2, 2), (3, 1), (17, 1), (19, 1), (313, 1), (5249411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_313
    · exact prime_5249411
  · decide +kernel

theorem prime_6373090172447 : Nat.Prime 6373090172447 := by
  apply nodeValid_prime [2, 73, 41681, 1047271] ⟨6373090172447, 5, [(2, 1), (73, 1), (41681, 1), (1047271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_41681
    · exact prime_1047271
  · decide +kernel

theorem prime_6373090235873 : Nat.Prime 6373090235873 := by
  apply nodeValid_prime [2, 19, 14543, 720763] ⟨6373090235873, 3, [(2, 5), (19, 1), (14543, 1), (720763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_14543
    · exact prime_720763
  · decide +kernel

theorem prime_6373090236017 : Nat.Prime 6373090236017 := by
  apply nodeValid_prime [2, 7, 79, 269, 2677643] ⟨6373090236017, 5, [(2, 4), (7, 1), (79, 1), (269, 1), (2677643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_269
    · exact prime_2677643
  · decide +kernel

theorem prime_6377660156683 : Nat.Prime 6377660156683 := by
  apply nodeValid_prime [2, 3, 379, 934866631] ⟨6377660156683, 3, [(2, 1), (3, 2), (379, 1), (934866631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_934866631
  · decide +kernel

theorem prime_6377660156717 : Nat.Prime 6377660156717 := by
  apply nodeValid_prime [2, 1594415039179] ⟨6377660156717, 2, [(2, 2), (1594415039179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1594415039179
  · decide +kernel

theorem prime_6377660166217 : Nat.Prime 6377660166217 := by
  apply nodeValid_prime [2, 3, 14969, 17752411] ⟨6377660166217, 5, [(2, 3), (3, 1), (14969, 1), (17752411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14969
    · exact prime_17752411
  · decide +kernel

theorem prime_6382232342449 : Nat.Prime 6382232342449 := by
  apply nodeValid_prime [2, 3, 19, 11171, 32971] ⟨6382232342449, 7, [(2, 4), (3, 1), (19, 2), (11171, 1), (32971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11171
    · exact prime_32971
  · decide +kernel

theorem prime_6382232342719 : Nat.Prime 6382232342719 := by
  apply nodeValid_prime [2, 3, 2797, 380302249] ⟨6382232342719, 3, [(2, 1), (3, 1), (2797, 1), (380302249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2797
    · exact prime_380302249
  · decide +kernel

theorem prime_6382232392253 : Nat.Prime 6382232392253 := by
  apply nodeValid_prime [2, 103, 30757, 503653] ⟨6382232392253, 2, [(2, 2), (103, 1), (30757, 1), (503653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_30757
    · exact prime_503653
  · decide +kernel

theorem prime_6386806824721 : Nat.Prime 6386806824721 := by
  apply nodeValid_prime [2, 3, 5, 7, 3801670729] ⟨6386806824721, 13, [(2, 4), (3, 1), (5, 1), (7, 1), (3801670729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3801670729
  · decide +kernel

theorem prime_6386806824859 : Nat.Prime 6386806824859 := by
  apply nodeValid_prime [2, 3, 709, 2437, 205357] ⟨6386806824859, 2, [(2, 1), (3, 2), (709, 1), (2437, 1), (205357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_709
    · exact prime_2437
    · exact prime_205357
  · decide +kernel

theorem prime_6386806842517 : Nat.Prime 6386806842517 := by
  apply nodeValid_prime [2, 3, 17, 73, 9497, 15053] ⟨6386806842517, 2, [(2, 2), (3, 2), (17, 1), (73, 1), (9497, 1), (15053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_73
    · exact prime_9497
    · exact prime_15053
  · decide +kernel

theorem prime_6391383515669 : Nat.Prime 6391383515669 := by
  apply nodeValid_prime [2, 809, 1975087613] ⟨6391383515669, 2, [(2, 2), (809, 1), (1975087613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_809
    · exact prime_1975087613
  · decide +kernel

theorem prime_6391383594901 : Nat.Prime 6391383594901 := by
  apply nodeValid_prime [2, 3, 5, 53, 163, 2466097] ⟨6391383594901, 2, [(2, 2), (3, 1), (5, 2), (53, 1), (163, 1), (2466097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_163
    · exact prime_2466097
  · decide +kernel

theorem prime_6391383595379 : Nat.Prime 6391383595379 := by
  apply nodeValid_prime [2, 151, 21163521839] ⟨6391383595379, 2, [(2, 1), (151, 1), (21163521839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_21163521839
  · decide +kernel

theorem prime_6395961951667 : Nat.Prime 6395961951667 := by
  apply nodeValid_prime [2, 3, 7, 59, 860366149] ⟨6395961951667, 3, [(2, 1), (3, 2), (7, 1), (59, 1), (860366149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_860366149
  · decide +kernel

theorem prime_6395961952511 : Nat.Prime 6395961952511 := by
  apply nodeValid_prime [2, 5, 13, 17, 2894100431] ⟨6395961952511, 23, [(2, 1), (5, 1), (13, 1), (17, 1), (2894100431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_2894100431
  · decide +kernel

theorem prime_6395962406609 : Nat.Prime 6395962406609 := by
  apply nodeValid_prime [2, 41, 149, 65435857] ⟨6395962406609, 3, [(2, 4), (41, 1), (149, 1), (65435857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_149
    · exact prime_65435857
  · decide +kernel

theorem prime_6400543524967 : Nat.Prime 6400543524967 := by
  apply nodeValid_prime [2, 3, 355585751387] ⟨6400543524967, 5, [(2, 1), (3, 2), (355585751387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_355585751387
  · decide +kernel

theorem prime_6400543587829 : Nat.Prime 6400543587829 := by
  apply nodeValid_prime [2, 3, 13, 281, 146011123] ⟨6400543587829, 6, [(2, 2), (3, 1), (13, 1), (281, 1), (146011123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_281
    · exact prime_146011123
  · decide +kernel

theorem prime_6400543588759 : Nat.Prime 6400543588759 := by
  apply nodeValid_prime [2, 3, 11, 41, 61, 2039, 2113] ⟨6400543588759, 11, [(2, 1), (3, 3), (11, 1), (41, 1), (61, 1), (2039, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_61
    · exact prime_2039
    · exact prime_2113
  · decide +kernel

theorem prime_6405126832919 : Nat.Prime 6405126832919 := by
  apply nodeValid_prime [2, 11, 67, 4345404907] ⟨6405126832919, 11, [(2, 1), (11, 1), (67, 1), (4345404907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_67
    · exact prime_4345404907
  · decide +kernel

theorem prime_6405126833143 : Nat.Prime 6405126833143 := by
  apply nodeValid_prime [2, 3, 23, 5157106951] ⟨6405126833143, 3, [(2, 1), (3, 3), (23, 1), (5157106951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_5157106951
  · decide +kernel

theorem prime_6405126861697 : Nat.Prime 6405126861697 := by
  apply nodeValid_prime [2, 3, 16680017869] ⟨6405126861697, 5, [(2, 7), (3, 1), (16680017869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16680017869
  · decide +kernel

theorem prime_6409712362819 : Nat.Prime 6409712362819 := by
  apply nodeValid_prime [2, 3, 223, 4790517461] ⟨6409712362819, 2, [(2, 1), (3, 1), (223, 1), (4790517461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_4790517461
  · decide +kernel

theorem prime_6409712362831 : Nat.Prime 6409712362831 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 31, 53, 807707] ⟨6409712362831, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (31, 1), (53, 1), (807707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_31
    · exact prime_53
    · exact prime_807707
  · decide +kernel

theorem prime_6409712413073 : Nat.Prime 6409712413073 := by
  apply nodeValid_prime [2, 29, 503, 2039, 13469] ⟨6409712413073, 3, [(2, 4), (29, 1), (503, 1), (2039, 1), (13469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_503
    · exact prime_2039
    · exact prime_13469
  · decide +kernel

theorem prime_6414300185429 : Nat.Prime 6414300185429 := by
  apply nodeValid_prime [2, 101, 109, 6779, 21487] ⟨6414300185429, 2, [(2, 2), (101, 1), (109, 1), (6779, 1), (21487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_109
    · exact prime_6779
    · exact prime_21487
  · decide +kernel

theorem prime_6414300192593 : Nat.Prime 6414300192593 := by
  apply nodeValid_prime [2, 18553, 21608029] ⟨6414300192593, 3, [(2, 4), (18553, 1), (21608029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18553
    · exact prime_21608029
  · decide +kernel

theorem prime_6414300193877 : Nat.Prime 6414300193877 := by
  apply nodeValid_prime [2, 10211, 157043879] ⟨6414300193877, 2, [(2, 2), (10211, 1), (157043879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10211
    · exact prime_157043879
  · decide +kernel

theorem prime_6418890172447 : Nat.Prime 6418890172447 := by
  apply nodeValid_prime [2, 3, 389, 2750167169] ⟨6418890172447, 5, [(2, 1), (3, 1), (389, 1), (2750167169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_2750167169
  · decide +kernel

theorem prime_6418890197927 : Nat.Prime 6418890197927 := by
  apply nodeValid_prime [2, 107, 659, 45515651] ⟨6418890197927, 5, [(2, 1), (107, 1), (659, 1), (45515651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_659
    · exact prime_45515651
  · decide +kernel

theorem prime_6418890197981 : Nat.Prime 6418890197981 := by
  apply nodeValid_prime [2, 5, 13, 1579, 15635237] ⟨6418890197981, 2, [(2, 2), (5, 1), (13, 1), (1579, 1), (15635237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1579
    · exact prime_15635237
  · decide +kernel

theorem prime_6423482352823 : Nat.Prime 6423482352823 := by
  apply nodeValid_prime [2, 3, 238921, 4480897] ⟨6423482352823, 3, [(2, 1), (3, 1), (238921, 1), (4480897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_238921
    · exact prime_4480897
  · decide +kernel

theorem prime_6423482354101 : Nat.Prime 6423482354101 := by
  apply nodeValid_prime [2, 3, 5, 7, 331, 9241091] ⟨6423482354101, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (331, 1), (9241091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_331
    · exact prime_9241091
  · decide +kernel

theorem prime_6423482386829 : Nat.Prime 6423482386829 := by
  apply nodeValid_prime [2, 13, 61, 1583, 1279253] ⟨6423482386829, 2, [(2, 2), (13, 1), (61, 1), (1583, 1), (1279253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_61
    · exact prime_1583
    · exact prime_1279253
  · decide +kernel

theorem prime_6428076832553 : Nat.Prime 6428076832553 := by
  apply nodeValid_prime [2, 353, 379, 6005887] ⟨6428076832553, 3, [(2, 3), (353, 1), (379, 1), (6005887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_379
    · exact prime_6005887
  · decide +kernel

theorem prime_6428076886997 : Nat.Prime 6428076886997 := by
  apply nodeValid_prime [2, 419, 521, 7361551] ⟨6428076886997, 2, [(2, 2), (419, 1), (521, 1), (7361551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_521
    · exact prime_7361551
  · decide +kernel

theorem prime_6428076887341 : Nat.Prime 6428076887341 := by
  apply nodeValid_prime [2, 3, 5, 35711538263] ⟨6428076887341, 2, [(2, 2), (3, 2), (5, 1), (35711538263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35711538263
  · decide +kernel

theorem prime_6432673490161 : Nat.Prime 6432673490161 := by
  apply nodeValid_prime [2, 3, 5, 19, 59, 23909729] ⟨6432673490161, 37, [(2, 4), (3, 1), (5, 1), (19, 1), (59, 1), (23909729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_59
    · exact prime_23909729
  · decide +kernel

theorem prime_6432673550161 : Nat.Prime 6432673550161 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 1613, 116201] ⟨6432673550161, 7, [(2, 4), (3, 1), (5, 1), (11, 1), (13, 1), (1613, 1), (116201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_1613
    · exact prime_116201
  · decide +kernel

theorem prime_6432673550971 : Nat.Prime 6432673550971 := by
  apply nodeValid_prime [2, 3, 5, 61, 443, 2791, 2843] ⟨6432673550971, 10, [(2, 1), (3, 1), (5, 1), (61, 1), (443, 1), (2791, 1), (2843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_443
    · exact prime_2791
    · exact prime_2843
  · decide +kernel

theorem prime_6437272363453 : Nat.Prime 6437272363453 := by
  apply nodeValid_prime [2, 3, 7, 34511, 740191] ⟨6437272363453, 6, [(2, 2), (3, 2), (7, 1), (34511, 1), (740191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_34511
    · exact prime_740191
  · decide +kernel

theorem prime_6437272546477 : Nat.Prime 6437272546477 := by
  apply nodeValid_prime [2, 3, 107, 139, 2851, 4217] ⟨6437272546477, 5, [(2, 2), (3, 2), (107, 1), (139, 1), (2851, 1), (4217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_139
    · exact prime_2851
    · exact prime_4217
  · decide +kernel

theorem prime_6437272549171 : Nat.Prime 6437272549171 := by
  apply nodeValid_prime [2, 3, 5, 214575751639] ⟨6437272549171, 7, [(2, 1), (3, 1), (5, 1), (214575751639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_214575751639
  · decide +kernel

end Sude.Lucas.Generated
