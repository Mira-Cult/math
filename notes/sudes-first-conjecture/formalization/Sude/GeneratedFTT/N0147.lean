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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0139
import Sude.GeneratedFTT.N0142

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_8849 : Nat.Prime 8849 := by
  apply nodeValid_prime [2, 7, 79] ⟨8849, 3, [(2, 4), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_10103 : Nat.Prime 10103 := by
  apply nodeValid_prime [2, 5051] ⟨10103, 5, [(2, 1), (5051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5051
  · decide +kernel

theorem prime_25471 : Nat.Prime 25471 := by
  apply nodeValid_prime [2, 3, 5, 283] ⟨25471, 6, [(2, 1), (3, 2), (5, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_283
  · decide +kernel

theorem prime_32621 : Nat.Prime 32621 := by
  apply nodeValid_prime [2, 5, 7, 233] ⟨32621, 3, [(2, 2), (5, 1), (7, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_233
  · decide +kernel

theorem prime_35831 : Nat.Prime 35831 := by
  apply nodeValid_prime [2, 5, 3583] ⟨35831, 11, [(2, 1), (5, 1), (3583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3583
  · decide +kernel

theorem prime_37447 : Nat.Prime 37447 := by
  apply nodeValid_prime [2, 3, 79] ⟨37447, 3, [(2, 1), (3, 1), (79, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_37951 : Nat.Prime 37951 := by
  apply nodeValid_prime [2, 3, 5, 11, 23] ⟨37951, 3, [(2, 1), (3, 1), (5, 2), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_42509 : Nat.Prime 42509 := by
  apply nodeValid_prime [2, 10627] ⟨42509, 2, [(2, 2), (10627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10627
  · decide +kernel

theorem prime_48187 : Nat.Prime 48187 := by
  apply nodeValid_prime [2, 3, 2677] ⟨48187, 2, [(2, 1), (3, 2), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2677
  · decide +kernel

theorem prime_52583 : Nat.Prime 52583 := by
  apply nodeValid_prime [2, 61, 431] ⟨52583, 5, [(2, 1), (61, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_431
  · decide +kernel

theorem prime_53881 : Nat.Prime 53881 := by
  apply nodeValid_prime [2, 3, 5, 449] ⟨53881, 31, [(2, 3), (3, 1), (5, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_449
  · decide +kernel

theorem prime_56779 : Nat.Prime 56779 := by
  apply nodeValid_prime [2, 3, 9463] ⟨56779, 2, [(2, 1), (3, 1), (9463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9463
  · decide +kernel

theorem prime_62327 : Nat.Prime 62327 := by
  apply nodeValid_prime [2, 11, 2833] ⟨62327, 5, [(2, 1), (11, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2833
  · decide +kernel

theorem prime_67073 : Nat.Prime 67073 := by
  apply nodeValid_prime [2, 131] ⟨67073, 3, [(2, 9), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_131
  · decide +kernel

theorem prime_68099 : Nat.Prime 68099 := by
  apply nodeValid_prime [2, 79, 431] ⟨68099, 2, [(2, 1), (79, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_431
  · decide +kernel

theorem prime_68171 : Nat.Prime 68171 := by
  apply nodeValid_prime [2, 5, 17, 401] ⟨68171, 2, [(2, 1), (5, 1), (17, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_401
  · decide +kernel

theorem prime_74903 : Nat.Prime 74903 := by
  apply nodeValid_prime [2, 17, 2203] ⟨74903, 5, [(2, 1), (17, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2203
  · decide +kernel

theorem prime_98347 : Nat.Prime 98347 := by
  apply nodeValid_prime [2, 3, 37, 443] ⟨98347, 2, [(2, 1), (3, 1), (37, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_443
  · decide +kernel

theorem prime_107791 : Nat.Prime 107791 := by
  apply nodeValid_prime [2, 3, 5, 3593] ⟨107791, 3, [(2, 1), (3, 1), (5, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3593
  · decide +kernel

theorem prime_115163 : Nat.Prime 115163 := by
  apply nodeValid_prime [2, 71, 811] ⟨115163, 2, [(2, 1), (71, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_811
  · decide +kernel

theorem prime_115223 : Nat.Prime 115223 := by
  apply nodeValid_prime [2, 53, 1087] ⟨115223, 5, [(2, 1), (53, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1087
  · decide +kernel

theorem prime_125921 : Nat.Prime 125921 := by
  apply nodeValid_prime [2, 5, 787] ⟨125921, 3, [(2, 5), (5, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_787
  · decide +kernel

theorem prime_136343 : Nat.Prime 136343 := by
  apply nodeValid_prime [2, 68171] ⟨136343, 5, [(2, 1), (68171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68171
  · decide +kernel

theorem prime_154579 : Nat.Prime 154579 := by
  apply nodeValid_prime [2, 3, 25763] ⟨154579, 14, [(2, 1), (3, 1), (25763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25763
  · decide +kernel

theorem prime_158749 : Nat.Prime 158749 := by
  apply nodeValid_prime [2, 3, 13229] ⟨158749, 2, [(2, 2), (3, 1), (13229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13229
  · decide +kernel

theorem prime_200153 : Nat.Prime 200153 := by
  apply nodeValid_prime [2, 127, 197] ⟨200153, 3, [(2, 3), (127, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_197
  · decide +kernel

theorem prime_224683 : Nat.Prime 224683 := by
  apply nodeValid_prime [2, 3, 37447] ⟨224683, 3, [(2, 1), (3, 1), (37447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37447
  · decide +kernel

theorem prime_230327 : Nat.Prime 230327 := by
  apply nodeValid_prime [2, 115163] ⟨230327, 5, [(2, 1), (115163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115163
  · decide +kernel

theorem prime_251843 : Nat.Prime 251843 := by
  apply nodeValid_prime [2, 125921] ⟨251843, 2, [(2, 1), (125921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_125921
  · decide +kernel

theorem prime_323381 : Nat.Prime 323381 := by
  apply nodeValid_prime [2, 5, 19, 23, 37] ⟨323381, 2, [(2, 2), (5, 1), (19, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_373963 : Nat.Prime 373963 := by
  apply nodeValid_prime [2, 3, 62327] ⟨373963, 3, [(2, 1), (3, 1), (62327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62327
  · decide +kernel

theorem prime_383519 : Nat.Prime 383519 := by
  apply nodeValid_prime [2, 233, 823] ⟨383519, 11, [(2, 1), (233, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_823
  · decide +kernel

theorem prime_407633 : Nat.Prime 407633 := by
  apply nodeValid_prime [2, 73, 349] ⟨407633, 3, [(2, 4), (73, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_349
  · decide +kernel

theorem prime_449419 : Nat.Prime 449419 := by
  apply nodeValid_prime [2, 3, 74903] ⟨449419, 2, [(2, 1), (3, 1), (74903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74903
  · decide +kernel

theorem prime_483611 : Nat.Prime 483611 := by
  apply nodeValid_prime [2, 5, 137, 353] ⟨483611, 2, [(2, 1), (5, 1), (137, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_353
  · decide +kernel

theorem prime_492083 : Nat.Prime 492083 := by
  apply nodeValid_prime [2, 17, 41, 353] ⟨492083, 2, [(2, 1), (17, 1), (41, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_353
  · decide +kernel

theorem prime_540629 : Nat.Prime 540629 := by
  apply nodeValid_prime [2, 11, 1117] ⟨540629, 2, [(2, 2), (11, 2), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1117
  · decide +kernel

theorem prime_556693 : Nat.Prime 556693 := by
  apply nodeValid_prime [2, 3, 23, 2017] ⟨556693, 2, [(2, 2), (3, 1), (23, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2017
  · decide +kernel

theorem prime_591791 : Nat.Prime 591791 := by
  apply nodeValid_prime [2, 5, 23, 31, 83] ⟨591791, 14, [(2, 1), (5, 1), (23, 1), (31, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_31
    · exact prime_83
  · decide +kernel

theorem prime_603689 : Nat.Prime 603689 := by
  apply nodeValid_prime [2, 59, 1279] ⟨603689, 3, [(2, 3), (59, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_1279
  · decide +kernel

theorem prime_623699 : Nat.Prime 623699 := by
  apply nodeValid_prime [2, 109, 2861] ⟨623699, 2, [(2, 1), (109, 1), (2861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_2861
  · decide +kernel

theorem prime_777641 : Nat.Prime 777641 := by
  apply nodeValid_prime [2, 5, 19441] ⟨777641, 3, [(2, 3), (5, 1), (19441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19441
  · decide +kernel

theorem prime_820349 : Nat.Prime 820349 := by
  apply nodeValid_prime [2, 67, 3061] ⟨820349, 2, [(2, 2), (67, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_3061
  · decide +kernel

theorem prime_867203 : Nat.Prime 867203 := by
  apply nodeValid_prime [2, 7, 8849] ⟨867203, 2, [(2, 1), (7, 2), (8849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8849
  · decide +kernel

theorem prime_938257 : Nat.Prime 938257 := by
  apply nodeValid_prime [2, 3, 11, 1777] ⟨938257, 13, [(2, 4), (3, 1), (11, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1777
  · decide +kernel

theorem prime_1001017 : Nat.Prime 1001017 := by
  apply nodeValid_prime [2, 3, 13903] ⟨1001017, 7, [(2, 3), (3, 2), (13903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13903
  · decide +kernel

theorem prime_1090979 : Nat.Prime 1090979 := by
  apply nodeValid_prime [2, 7, 149, 523] ⟨1090979, 2, [(2, 1), (7, 1), (149, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_149
    · exact prime_523
  · decide +kernel

theorem prime_1192589 : Nat.Prime 1192589 := by
  apply nodeValid_prime [2, 397, 751] ⟨1192589, 2, [(2, 2), (397, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_751
  · decide +kernel

theorem prime_1290719 : Nat.Prime 1290719 := by
  apply nodeValid_prime [2, 11, 13, 4513] ⟨1290719, 11, [(2, 1), (11, 1), (13, 1), (4513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_4513
  · decide +kernel

theorem prime_1364401 : Nat.Prime 1364401 := by
  apply nodeValid_prime [2, 3, 5, 379] ⟨1364401, 7, [(2, 4), (3, 2), (5, 2), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_379
  · decide +kernel

theorem prime_1719433 : Nat.Prime 1719433 := by
  apply nodeValid_prime [2, 3, 11, 13, 167] ⟨1719433, 5, [(2, 3), (3, 2), (11, 1), (13, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_167
  · decide +kernel

theorem prime_1757923 : Nat.Prime 1757923 := by
  apply nodeValid_prime [2, 3, 29, 10103] ⟨1757923, 2, [(2, 1), (3, 1), (29, 1), (10103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_10103
  · decide +kernel

theorem prime_1816271 : Nat.Prime 1816271 := by
  apply nodeValid_prime [2, 5, 29, 6263] ⟨1816271, 7, [(2, 1), (5, 1), (29, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_6263
  · decide +kernel

theorem prime_2404993 : Nat.Prime 2404993 := by
  apply nodeValid_prime [2, 3, 6263] ⟨2404993, 13, [(2, 7), (3, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6263
  · decide +kernel

theorem prime_2777111 : Nat.Prime 2777111 := by
  apply nodeValid_prime [2, 5, 7, 97, 409] ⟨2777111, 7, [(2, 1), (5, 1), (7, 1), (97, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_97
    · exact prime_409
  · decide +kernel

theorem prime_3111151 : Nat.Prime 3111151 := by
  apply nodeValid_prime [2, 3, 5, 7, 2963] ⟨3111151, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (2963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2963
  · decide +kernel

theorem prime_3776569 : Nat.Prime 3776569 := by
  apply nodeValid_prime [2, 3, 53, 2969] ⟨3776569, 7, [(2, 3), (3, 1), (53, 1), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_2969
  · decide +kernel

theorem prime_4004069 : Nat.Prime 4004069 := by
  apply nodeValid_prime [2, 1001017] ⟨4004069, 2, [(2, 2), (1001017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1001017
  · decide +kernel

theorem prime_4544279 : Nat.Prime 4544279 := by
  apply nodeValid_prime [2, 1217, 1867] ⟨4544279, 11, [(2, 1), (1217, 1), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1217
    · exact prime_1867
  · decide +kernel

theorem prime_5204197 : Nat.Prime 5204197 := by
  apply nodeValid_prime [2, 3, 48187] ⟨5204197, 5, [(2, 2), (3, 3), (48187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48187
  · decide +kernel

theorem prime_5254351 : Nat.Prime 5254351 := by
  apply nodeValid_prime [2, 3, 5, 23, 1523] ⟨5254351, 11, [(2, 1), (3, 1), (5, 2), (23, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1523
  · decide +kernel

theorem prime_5255993 : Nat.Prime 5255993 := by
  apply nodeValid_prime [2, 7, 17, 5521] ⟨5255993, 3, [(2, 3), (7, 1), (17, 1), (5521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_5521
  · decide +kernel

theorem prime_6464483 : Nat.Prime 6464483 := by
  apply nodeValid_prime [2, 137, 23593] ⟨6464483, 2, [(2, 1), (137, 1), (23593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_23593
  · decide +kernel

theorem prime_6772123 : Nat.Prime 6772123 := by
  apply nodeValid_prime [2, 3, 7, 71, 757] ⟨6772123, 2, [(2, 1), (3, 2), (7, 1), (71, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_757
  · decide +kernel

theorem prime_6994417 : Nat.Prime 6994417 := by
  apply nodeValid_prime [2, 3, 11, 13, 1019] ⟨6994417, 5, [(2, 4), (3, 1), (11, 1), (13, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1019
  · decide +kernel

theorem prime_8122903 : Nat.Prime 8122903 := by
  apply nodeValid_prime [2, 3, 1039, 1303] ⟨8122903, 3, [(2, 1), (3, 1), (1039, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1039
    · exact prime_1303
  · decide +kernel

theorem prime_17399929 : Nat.Prime 17399929 := by
  apply nodeValid_prime [2, 3, 7, 13, 31, 257] ⟨17399929, 11, [(2, 3), (3, 1), (7, 1), (13, 1), (31, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_257
  · decide +kernel

theorem prime_19517923 : Nat.Prime 19517923 := by
  apply nodeValid_prime [2, 3, 211, 571] ⟨19517923, 2, [(2, 1), (3, 4), (211, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_571
  · decide +kernel

theorem prime_23060153 : Nat.Prime 23060153 := by
  apply nodeValid_prime [2, 127, 22697] ⟨23060153, 3, [(2, 3), (127, 1), (22697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_22697
  · decide +kernel

theorem prime_30412741 : Nat.Prime 30412741 := by
  apply nodeValid_prime [2, 3, 5, 223, 2273] ⟨30412741, 2, [(2, 2), (3, 1), (5, 1), (223, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
    · exact prime_2273
  · decide +kernel

theorem prime_43247593 : Nat.Prime 43247593 := by
  apply nodeValid_prime [2, 3, 17, 89, 397] ⟨43247593, 5, [(2, 3), (3, 2), (17, 1), (89, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_89
    · exact prime_397
  · decide +kernel

theorem prime_43951889 : Nat.Prime 43951889 := by
  apply nodeValid_prime [2, 1109, 2477] ⟨43951889, 3, [(2, 4), (1109, 1), (2477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1109
    · exact prime_2477
  · decide +kernel

theorem prime_46120307 : Nat.Prime 46120307 := by
  apply nodeValid_prime [2, 23060153] ⟨46120307, 2, [(2, 1), (23060153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23060153
  · decide +kernel

theorem prime_51596641 : Nat.Prime 51596641 := by
  apply nodeValid_prime [2, 3, 5, 35831] ⟨51596641, 13, [(2, 5), (3, 2), (5, 1), (35831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35831
  · decide +kernel

theorem prime_63071917 : Nat.Prime 63071917 := by
  apply nodeValid_prime [2, 3, 5255993] ⟨63071917, 5, [(2, 2), (3, 1), (5255993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5255993
  · decide +kernel

theorem prime_76771181 : Nat.Prime 76771181 := by
  apply nodeValid_prime [2, 5, 73, 52583] ⟨76771181, 2, [(2, 2), (5, 1), (73, 1), (52583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_52583
  · decide +kernel

theorem prime_100676353 : Nat.Prime 100676353 := by
  apply nodeValid_prime [2, 3, 7, 61, 307] ⟨100676353, 11, [(2, 8), (3, 1), (7, 1), (61, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_307
  · decide +kernel

theorem prime_119053993 : Nat.Prime 119053993 := by
  apply nodeValid_prime [2, 3, 17, 103, 2833] ⟨119053993, 5, [(2, 3), (3, 1), (17, 1), (103, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_103
    · exact prime_2833
  · decide +kernel

theorem prime_124542241 : Nat.Prime 124542241 := by
  apply nodeValid_prime [2, 3, 5, 23, 29, 389] ⟨124542241, 13, [(2, 5), (3, 1), (5, 1), (23, 1), (29, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_29
    · exact prime_389
  · decide +kernel

theorem prime_172990373 : Nat.Prime 172990373 := by
  apply nodeValid_prime [2, 43247593] ⟨172990373, 2, [(2, 2), (43247593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43247593
  · decide +kernel

theorem prime_173743741 : Nat.Prime 173743741 := by
  apply nodeValid_prime [2, 3, 5, 17, 56779] ⟨173743741, 7, [(2, 2), (3, 2), (5, 1), (17, 1), (56779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_56779
  · decide +kernel

theorem prime_252287669 : Nat.Prime 252287669 := by
  apply nodeValid_prime [2, 63071917] ⟨252287669, 2, [(2, 2), (63071917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63071917
  · decide +kernel

theorem prime_470347231 : Nat.Prime 470347231 := by
  apply nodeValid_prime [2, 3, 5, 29, 540629] ⟨470347231, 6, [(2, 1), (3, 1), (5, 1), (29, 1), (540629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_540629
  · decide +kernel

theorem prime_669080303 : Nat.Prime 669080303 := by
  apply nodeValid_prime [2, 11, 30412741] ⟨669080303, 10, [(2, 1), (11, 1), (30412741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_30412741
  · decide +kernel

theorem prime_759988171 : Nat.Prime 759988171 := by
  apply nodeValid_prime [2, 3, 5, 938257] ⟨759988171, 2, [(2, 1), (3, 4), (5, 1), (938257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_938257
  · decide +kernel

theorem prime_954083659 : Nat.Prime 954083659 := by
  apply nodeValid_prime [2, 3, 11, 71, 97, 2099] ⟨954083659, 2, [(2, 1), (3, 1), (11, 1), (71, 1), (97, 1), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_71
    · exact prime_97
    · exact prime_2099
  · decide +kernel

theorem prime_1006763531 : Nat.Prime 1006763531 := by
  apply nodeValid_prime [2, 5, 100676353] ⟨1006763531, 2, [(2, 1), (5, 1), (100676353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_100676353
  · decide +kernel

theorem prime_1182240461 : Nat.Prime 1182240461 := by
  apply nodeValid_prime [2, 5, 67, 127, 6947] ⟨1182240461, 2, [(2, 2), (5, 1), (67, 1), (127, 1), (6947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_127
    · exact prime_6947
  · decide +kernel

theorem prime_1313951911 : Nat.Prime 1313951911 := by
  apply nodeValid_prime [2, 3, 5, 2677, 16361] ⟨1313951911, 15, [(2, 1), (3, 1), (5, 1), (2677, 1), (16361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2677
    · exact prime_16361
  · decide +kernel

theorem prime_1426737491 : Nat.Prime 1426737491 := by
  apply nodeValid_prime [2, 5, 31, 863, 5333] ⟨1426737491, 2, [(2, 1), (5, 1), (31, 1), (863, 1), (5333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_863
    · exact prime_5333
  · decide +kernel

theorem prime_2013527063 : Nat.Prime 2013527063 := by
  apply nodeValid_prime [2, 1006763531] ⟨2013527063, 5, [(2, 1), (1006763531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1006763531
  · decide +kernel

theorem prime_3454278589 : Nat.Prime 3454278589 := by
  apply nodeValid_prime [2, 3, 127, 251843] ⟨3454278589, 2, [(2, 2), (3, 3), (127, 1), (251843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_251843
  · decide +kernel

theorem prime_5624390423 : Nat.Prime 5624390423 := by
  apply nodeValid_prime [2, 7, 23, 53, 89] ⟨5624390423, 5, [(2, 1), (7, 2), (23, 3), (53, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_53
    · exact prime_89
  · decide +kernel

theorem prime_6358052549 : Nat.Prime 6358052549 := by
  apply nodeValid_prime [2, 2633, 603689] ⟨6358052549, 2, [(2, 2), (2633, 1), (603689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2633
    · exact prime_603689
  · decide +kernel

theorem prime_6606701627 : Nat.Prime 6606701627 := by
  apply nodeValid_prime [2, 7, 73, 6464483] ⟨6606701627, 2, [(2, 1), (7, 1), (73, 1), (6464483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_6464483
  · decide +kernel

theorem prime_14680918619 : Nat.Prime 14680918619 := by
  apply nodeValid_prime [2, 68099, 107791] ⟨14680918619, 2, [(2, 1), (68099, 1), (107791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_68099
    · exact prime_107791
  · decide +kernel

theorem prime_15137260141 : Nat.Prime 15137260141 := by
  apply nodeValid_prime [2, 3, 5, 252287669] ⟨15137260141, 2, [(2, 2), (3, 1), (5, 1), (252287669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_252287669
  · decide +kernel

theorem prime_16095603169 : Nat.Prime 16095603169 := by
  apply nodeValid_prime [2, 3, 2543, 21977] ⟨16095603169, 11, [(2, 5), (3, 2), (2543, 1), (21977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2543
    · exact prime_21977
  · decide +kernel

theorem prime_16836130807 : Nat.Prime 16836130807 := by
  apply nodeValid_prime [2, 3, 11, 409, 623699] ⟨16836130807, 6, [(2, 1), (3, 1), (11, 1), (409, 1), (623699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_409
    · exact prime_623699
  · decide +kernel

theorem prime_17483306881 : Nat.Prime 17483306881 := by
  apply nodeValid_prime [2, 3, 5, 13, 53881] ⟨17483306881, 21, [(2, 7), (3, 1), (5, 1), (13, 2), (53881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_53881
  · decide +kernel

theorem prime_17533722389 : Nat.Prime 17533722389 := by
  apply nodeValid_prime [2, 7, 13, 23, 31, 67559] ⟨17533722389, 2, [(2, 2), (7, 1), (13, 1), (23, 1), (31, 1), (67559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_31
    · exact prime_67559
  · decide +kernel

theorem prime_24535580887 : Nat.Prime 24535580887 := by
  apply nodeValid_prime [2, 3, 337, 449419] ⟨24535580887, 3, [(2, 1), (3, 4), (337, 1), (449419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
    · exact prime_449419
  · decide +kernel

theorem prime_27195682879 : Nat.Prime 27195682879 := by
  apply nodeValid_prime [2, 3, 7, 13, 1193, 4639] ⟨27195682879, 3, [(2, 1), (3, 3), (7, 1), (13, 1), (1193, 1), (4639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1193
    · exact prime_4639
  · decide +kernel

theorem prime_27739442981 : Nat.Prime 27739442981 := by
  apply nodeValid_prime [2, 5, 17, 41, 71, 28027] ⟨27739442981, 3, [(2, 2), (5, 1), (17, 1), (41, 1), (71, 1), (28027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_41
    · exact prime_71
    · exact prime_28027
  · decide +kernel

theorem prime_32924306171 : Nat.Prime 32924306171 := by
  apply nodeValid_prime [2, 5, 7, 470347231] ⟨32924306171, 7, [(2, 1), (5, 1), (7, 1), (470347231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_470347231
  · decide +kernel

theorem prime_33487392259 : Nat.Prime 33487392259 := by
  apply nodeValid_prime [2, 3, 127, 397, 36899] ⟨33487392259, 2, [(2, 1), (3, 2), (127, 1), (397, 1), (36899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_397
    · exact prime_36899
  · decide +kernel

theorem prime_57775347107 : Nat.Prime 57775347107 := by
  apply nodeValid_prime [2, 239, 1049, 115223] ⟨57775347107, 2, [(2, 1), (239, 1), (1049, 1), (115223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_1049
    · exact prime_115223
  · decide +kernel

theorem prime_78741465923 : Nat.Prime 78741465923 := by
  apply nodeValid_prime [2, 7, 5624390423] ⟨78741465923, 2, [(2, 1), (7, 1), (5624390423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5624390423
  · decide +kernel

theorem prime_114051951367 : Nat.Prime 114051951367 := by
  apply nodeValid_prime [2, 3, 43, 1367, 323381] ⟨114051951367, 5, [(2, 1), (3, 1), (43, 1), (1367, 1), (323381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1367
    · exact prime_323381
  · decide +kernel

theorem prime_133949569037 : Nat.Prime 133949569037 := by
  apply nodeValid_prime [2, 33487392259] ⟨133949569037, 2, [(2, 2), (33487392259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33487392259
  · decide +kernel

theorem prime_173441652253 : Nat.Prime 173441652253 := by
  apply nodeValid_prime [2, 3, 11, 1313951911] ⟨173441652253, 2, [(2, 2), (3, 1), (11, 1), (1313951911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1313951911
  · decide +kernel

theorem prime_287225754869 : Nat.Prime 287225754869 := by
  apply nodeValid_prime [2, 13, 283, 19517923] ⟨287225754869, 2, [(2, 2), (13, 1), (283, 1), (19517923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_283
    · exact prime_19517923
  · decide +kernel

theorem prime_330659917157 : Nat.Prime 330659917157 := by
  apply nodeValid_prime [2, 18191, 4544279] ⟨330659917157, 2, [(2, 2), (18191, 1), (4544279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18191
    · exact prime_4544279
  · decide +kernel

theorem prime_332873315773 : Nat.Prime 332873315773 := by
  apply nodeValid_prime [2, 3, 27739442981] ⟨332873315773, 2, [(2, 2), (3, 1), (27739442981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27739442981
  · decide +kernel

theorem prime_334651230169 : Nat.Prime 334651230169 := by
  apply nodeValid_prime [2, 3, 29, 71, 6772123] ⟨334651230169, 23, [(2, 3), (3, 1), (29, 1), (71, 1), (6772123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_71
    · exact prime_6772123
  · decide +kernel

theorem prime_398915800139 : Nat.Prime 398915800139 := by
  apply nodeValid_prime [2, 1153, 172990373] ⟨398915800139, 2, [(2, 1), (1153, 1), (172990373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1153
    · exact prime_172990373
  · decide +kernel

theorem prime_574451509739 : Nat.Prime 574451509739 := by
  apply nodeValid_prime [2, 287225754869] ⟨574451509739, 2, [(2, 1), (287225754869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_287225754869
  · decide +kernel

theorem prime_667967531423 : Nat.Prime 667967531423 := by
  apply nodeValid_prime [2, 1289, 3863, 67073] ⟨667967531423, 5, [(2, 1), (1289, 1), (3863, 1), (67073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1289
    · exact prime_3863
    · exact prime_67073
  · decide +kernel

theorem prime_795705771607 : Nat.Prime 795705771607 := by
  apply nodeValid_prime [2, 3, 139, 954083659] ⟨795705771607, 6, [(2, 1), (3, 1), (139, 1), (954083659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_954083659
  · decide +kernel

theorem prime_1333268774213 : Nat.Prime 1333268774213 := by
  apply nodeValid_prime [2, 19, 6317, 2777111] ⟨1333268774213, 2, [(2, 2), (19, 1), (6317, 1), (2777111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_6317
    · exact prime_2777111
  · decide +kernel

theorem prime_1334157127733 : Nat.Prime 1334157127733 := by
  apply nodeValid_prime [2, 11, 13, 79, 191, 154579] ⟨1334157127733, 2, [(2, 2), (11, 1), (13, 1), (79, 1), (191, 1), (154579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_79
    · exact prime_191
    · exact prime_154579
  · decide +kernel

theorem prime_1338604920677 : Nat.Prime 1338604920677 := by
  apply nodeValid_prime [2, 334651230169] ⟨1338604920677, 2, [(2, 2), (334651230169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_334651230169
  · decide +kernel

theorem prime_1995909163363 : Nat.Prime 1995909163363 := by
  apply nodeValid_prime [2, 3, 9787, 3776569] ⟨1995909163363, 2, [(2, 1), (3, 3), (9787, 1), (3776569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9787
    · exact prime_3776569
  · decide +kernel

theorem prime_3965269562489 : Nat.Prime 3965269562489 := by
  apply nodeValid_prime [2, 13, 23, 41, 1757923] ⟨3965269562489, 3, [(2, 3), (13, 1), (23, 2), (41, 1), (1757923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_41
    · exact prime_1757923
  · decide +kernel

theorem prime_4013143657793 : Nat.Prime 4013143657793 := by
  apply nodeValid_prime [2, 12049, 5204197] ⟨4013143657793, 3, [(2, 6), (12049, 1), (5204197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_12049
    · exact prime_5204197
  · decide +kernel

theorem prime_7925242519829 : Nat.Prime 7925242519829 := by
  apply nodeValid_prime [2, 113, 17533722389] ⟨7925242519829, 2, [(2, 2), (113, 1), (17533722389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_17533722389
  · decide +kernel

theorem prime_7925242519969 : Nat.Prime 7925242519969 := by
  apply nodeValid_prime [2, 3, 41, 2013527063] ⟨7925242519969, 13, [(2, 5), (3, 1), (41, 1), (2013527063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2013527063
  · decide +kernel

theorem prime_7925242556993 : Nat.Prime 7925242556993 := by
  apply nodeValid_prime [2, 1613, 76771181] ⟨7925242556993, 3, [(2, 6), (1613, 1), (76771181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1613
    · exact prime_76771181
  · decide +kernel

theorem prime_7930539124979 : Nat.Prime 7930539124979 := by
  apply nodeValid_prime [2, 3965269562489] ⟨7930539124979, 2, [(2, 1), (3965269562489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3965269562489
  · decide +kernel

theorem prime_7930539142781 : Nat.Prime 7930539142781 := by
  apply nodeValid_prime [2, 5, 167, 593, 4004069] ⟨7930539142781, 2, [(2, 2), (5, 1), (167, 1), (593, 1), (4004069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_593
    · exact prime_4004069
  · decide +kernel

theorem prime_7935838011769 : Nat.Prime 7935838011769 := by
  apply nodeValid_prime [2, 3, 330659917157] ⟨7935838011769, 7, [(2, 3), (3, 1), (330659917157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_330659917157
  · decide +kernel

theorem prime_7935838013167 : Nat.Prime 7935838013167 := by
  apply nodeValid_prime [2, 3, 7, 230327, 820349] ⟨7935838013167, 3, [(2, 1), (3, 1), (7, 1), (230327, 1), (820349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_230327
    · exact prime_820349
  · decide +kernel

theorem prime_7935838086931 : Nat.Prime 7935838086931 := by
  apply nodeValid_prime [2, 3, 5, 13, 79, 3929, 65557] ⟨7935838086931, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (79, 1), (3929, 1), (65557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_79
    · exact prime_3929
    · exact prime_65557
  · decide +kernel

theorem prime_7941139400669 : Nat.Prime 7941139400669 := by
  apply nodeValid_prime [2, 73, 27195682879] ⟨7941139400669, 2, [(2, 2), (73, 1), (27195682879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_27195682879
  · decide +kernel

theorem prime_7941139400743 : Nat.Prime 7941139400743 := by
  apply nodeValid_prime [2, 3, 30113, 43951889] ⟨7941139400743, 3, [(2, 1), (3, 1), (30113, 1), (43951889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30113
    · exact prime_43951889
  · decide +kernel

theorem prime_7941139441087 : Nat.Prime 7941139441087 := by
  apply nodeValid_prime [2, 3, 11117, 119053993] ⟨7941139441087, 3, [(2, 1), (3, 1), (11117, 1), (119053993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11117
    · exact prime_119053993
  · decide +kernel

theorem prime_7946443174727 : Nat.Prime 7946443174727 := by
  apply nodeValid_prime [2, 7, 32621, 17399929] ⟨7946443174727, 5, [(2, 1), (7, 1), (32621, 1), (17399929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_32621
    · exact prime_17399929
  · decide +kernel

theorem prime_7946443176839 : Nat.Prime 7946443176839 := by
  apply nodeValid_prime [2, 277, 11113, 1290719] ⟨7946443176839, 13, [(2, 1), (277, 1), (11113, 1), (1290719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_11113
    · exact prime_1290719
  · decide +kernel

theorem prime_7946443190993 : Nat.Prime 7946443190993 := by
  apply nodeValid_prime [2, 29, 7121, 2404993] ⟨7946443190993, 3, [(2, 4), (29, 1), (7121, 1), (2404993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_7121
    · exact prime_2404993
  · decide +kernel

theorem prime_7951749311879 : Nat.Prime 7951749311879 := by
  apply nodeValid_prime [2, 1151, 3454278589] ⟨7951749311879, 7, [(2, 1), (1151, 1), (3454278589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1151
    · exact prime_3454278589
  · decide +kernel

theorem prime_7951749312511 : Nat.Prime 7951749312511 := by
  apply nodeValid_prime [2, 3, 5, 461, 853, 224683] ⟨7951749312511, 15, [(2, 1), (3, 2), (5, 1), (461, 1), (853, 1), (224683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_461
    · exact prime_853
    · exact prime_224683
  · decide +kernel

theorem prime_7951749340687 : Nat.Prime 7951749340687 := by
  apply nodeValid_prime [2, 3, 19, 59, 1182240461] ⟨7951749340687, 5, [(2, 1), (3, 1), (19, 1), (59, 1), (1182240461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
    · exact prime_1182240461
  · decide +kernel

theorem prime_7957057716071 : Nat.Prime 7957057716071 := by
  apply nodeValid_prime [2, 5, 795705771607] ⟨7957057716071, 17, [(2, 1), (5, 1), (795705771607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_795705771607
  · decide +kernel

theorem prime_7957057716511 : Nat.Prime 7957057716511 := by
  apply nodeValid_prime [2, 3, 5, 7, 337, 557, 28837] ⟨7957057716511, 3, [(2, 1), (3, 1), (5, 1), (7, 2), (337, 1), (557, 1), (28837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_337
    · exact prime_557
    · exact prime_28837
  · decide +kernel

theorem prime_7957057891499 : Nat.Prime 7957057891499 := by
  apply nodeValid_prime [2, 271, 14680918619] ⟨7957057891499, 2, [(2, 1), (271, 1), (14680918619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_14680918619
  · decide +kernel

theorem prime_7962368830531 : Nat.Prime 7962368830531 := by
  apply nodeValid_prime [2, 3, 5, 17, 98347, 158749] ⟨7962368830531, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (98347, 1), (158749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_98347
    · exact prime_158749
  · decide +kernel

theorem prime_7962368845141 : Nat.Prime 7962368845141 := by
  apply nodeValid_prime [2, 3, 5, 109, 556693] ⟨7962368845141, 6, [(2, 2), (3, 8), (5, 1), (109, 1), (556693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_556693
  · decide +kernel

theorem prime_7962368847613 : Nat.Prime 7962368847613 := by
  apply nodeValid_prime [2, 3, 643, 1327, 777641] ⟨7962368847613, 2, [(2, 2), (3, 1), (643, 1), (1327, 1), (777641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_643
    · exact prime_1327
    · exact prime_777641
  · decide +kernel

theorem prime_7967682093383 : Nat.Prime 7967682093383 := by
  apply nodeValid_prime [2, 11, 32924306171] ⟨7967682093383, 5, [(2, 1), (11, 2), (32924306171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_32924306171
  · decide +kernel

theorem prime_7967682093601 : Nat.Prime 7967682093601 := by
  apply nodeValid_prime [2, 3, 5, 29, 41, 34471] ⟨7967682093601, 11, [(2, 5), (3, 5), (5, 2), (29, 1), (41, 1), (34471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_41
    · exact prime_34471
  · decide +kernel

theorem prime_7967682162163 : Nat.Prime 7967682162163 := by
  apply nodeValid_prime [2, 3, 67, 6606701627] ⟨7967682162163, 11, [(2, 1), (3, 2), (67, 1), (6606701627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_6606701627
  · decide +kernel

theorem prime_7972997896447 : Nat.Prime 7972997896447 := by
  apply nodeValid_prime [2, 3, 11, 19, 6358052549] ⟨7972997896447, 5, [(2, 1), (3, 1), (11, 1), (19, 1), (6358052549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_6358052549
  · decide +kernel

theorem prime_7972997896627 : Nat.Prime 7972997896627 := by
  apply nodeValid_prime [2, 3, 7, 23, 83, 2203, 45139] ⟨7972997896627, 5, [(2, 1), (3, 1), (7, 1), (23, 1), (83, 1), (2203, 1), (45139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_83
    · exact prime_2203
    · exact prime_45139
  · decide +kernel

theorem prime_7972997900767 : Nat.Prime 7972997900767 := by
  apply nodeValid_prime [2, 3, 23, 57775347107] ⟨7972997900767, 6, [(2, 1), (3, 1), (23, 1), (57775347107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_57775347107
  · decide +kernel

theorem prime_7978316002781 : Nat.Prime 7978316002781 := by
  apply nodeValid_prime [2, 5, 398915800139] ⟨7978316002781, 3, [(2, 2), (5, 1), (398915800139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_398915800139
  · decide +kernel

theorem prime_7978316003639 : Nat.Prime 7978316003639 := by
  apply nodeValid_prime [2, 23, 173441652253] ⟨7978316003639, 7, [(2, 1), (23, 1), (173441652253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_173441652253
  · decide +kernel

theorem prime_7978316049673 : Nat.Prime 7978316049673 := by
  apply nodeValid_prime [2, 3, 233, 1426737491] ⟨7978316049673, 5, [(2, 3), (3, 1), (233, 1), (1426737491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_1426737491
  · decide +kernel

theorem prime_7983636595691 : Nat.Prime 7983636595691 := by
  apply nodeValid_prime [2, 5, 7, 114051951367] ⟨7983636595691, 7, [(2, 1), (5, 1), (7, 1), (114051951367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_114051951367
  · decide +kernel

theorem prime_7983636653453 : Nat.Prime 7983636653453 := by
  apply nodeValid_prime [2, 1995909163363] ⟨7983636653453, 2, [(2, 2), (1995909163363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1995909163363
  · decide +kernel

theorem prime_7988959537331 : Nat.Prime 7988959537331 := by
  apply nodeValid_prime [2, 5, 53, 25471, 591791] ⟨7988959537331, 2, [(2, 1), (5, 1), (53, 1), (25471, 1), (591791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_25471
    · exact prime_591791
  · decide +kernel

theorem prime_7988959578541 : Nat.Prime 7988959578541 := by
  apply nodeValid_prime [2, 3, 5, 2887, 46120307] ⟨7988959578541, 2, [(2, 2), (3, 1), (5, 1), (2887, 1), (46120307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2887
    · exact prime_46120307
  · decide +kernel

theorem prime_7988959578553 : Nat.Prime 7988959578553 := by
  apply nodeValid_prime [2, 3, 332873315773] ⟨7988959578553, 5, [(2, 3), (3, 1), (332873315773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_332873315773
  · decide +kernel

theorem prime_7994284872461 : Nat.Prime 7994284872461 := by
  apply nodeValid_prime [2, 5, 127, 599, 5254351] ⟨7994284872461, 2, [(2, 2), (5, 1), (127, 1), (599, 1), (5254351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_599
    · exact prime_5254351
  · decide +kernel

theorem prime_7994284953637 : Nat.Prime 7994284953637 := by
  apply nodeValid_prime [2, 3, 2273, 2819, 103969] ⟨7994284953637, 2, [(2, 2), (3, 1), (2273, 1), (2819, 1), (103969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2273
    · exact prime_2819
    · exact prime_103969
  · decide +kernel

theorem prime_7994284953899 : Nat.Prime 7994284953899 := by
  apply nodeValid_prime [2, 492083, 8122903] ⟨7994284953899, 2, [(2, 1), (492083, 1), (8122903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_492083
    · exact prime_8122903
  · decide +kernel

theorem prime_7999612616953 : Nat.Prime 7999612616953 := by
  apply nodeValid_prime [2, 3, 11, 17, 1553, 42509] ⟨7999612616953, 5, [(2, 3), (3, 4), (11, 1), (17, 1), (1553, 1), (42509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_1553
    · exact prime_42509
  · decide +kernel

theorem prime_7999612644739 : Nat.Prime 7999612644739 := by
  apply nodeValid_prime [2, 3, 11, 13, 31, 43, 6994417] ⟨7999612644739, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (31, 1), (43, 1), (6994417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_43
    · exact prime_6994417
  · decide +kernel

theorem prime_7999612645279 : Nat.Prime 7999612645279 := by
  apply nodeValid_prime [2, 3, 1333268774213] ⟨7999612645279, 3, [(2, 1), (3, 1), (1333268774213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1333268774213
  · decide +kernel

theorem prime_8004942764281 : Nat.Prime 8004942764281 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 37, 867203] ⟨8004942764281, 19, [(2, 3), (3, 4), (5, 1), (7, 1), (11, 1), (37, 1), (867203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_37
    · exact prime_867203
  · decide +kernel

theorem prime_8004942766399 : Nat.Prime 8004942766399 := by
  apply nodeValid_prime [2, 3, 1334157127733] ⟨8004942766399, 6, [(2, 1), (3, 1), (1334157127733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1334157127733
  · decide +kernel

theorem prime_8004942768727 : Nat.Prime 8004942768727 := by
  apply nodeValid_prime [2, 3, 407633, 1090979] ⟨8004942768727, 5, [(2, 1), (3, 2), (407633, 1), (1090979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_407633
    · exact prime_1090979
  · decide +kernel

theorem prime_8010275321969 : Nat.Prime 8010275321969 := by
  apply nodeValid_prime [2, 31, 313, 51596641] ⟨8010275321969, 3, [(2, 4), (31, 1), (313, 1), (51596641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_313
    · exact prime_51596641
  · decide +kernel

theorem prime_8010275322131 : Nat.Prime 8010275322131 := by
  apply nodeValid_prime [2, 5, 643, 9137, 136343] ⟨8010275322131, 2, [(2, 1), (5, 1), (643, 1), (9137, 1), (136343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_643
    · exact prime_9137
    · exact prime_136343
  · decide +kernel

theorem prime_8010275322341 : Nat.Prime 8010275322341 := by
  apply nodeValid_prime [2, 5, 17, 31, 759988171] ⟨8010275322341, 2, [(2, 2), (5, 1), (17, 1), (31, 1), (759988171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_759988171
  · decide +kernel

theorem prime_8015610282821 : Nat.Prime 8015610282821 := by
  apply nodeValid_prime [2, 5, 7, 29, 1447, 1364401] ⟨8015610282821, 2, [(2, 2), (5, 1), (7, 1), (29, 1), (1447, 1), (1364401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_1447
    · exact prime_1364401
  · decide +kernel

theorem prime_8015610377077 : Nat.Prime 8015610377077 := by
  apply nodeValid_prime [2, 3, 667967531423] ⟨8015610377077, 2, [(2, 2), (3, 1), (667967531423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_667967531423
  · decide +kernel

theorem prime_8015610378163 : Nat.Prime 8015610378163 := by
  apply nodeValid_prime [2, 3, 83, 16095603169] ⟨8015610378163, 2, [(2, 1), (3, 1), (83, 1), (16095603169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_16095603169
  · decide +kernel

theorem prime_8020947645101 : Nat.Prime 8020947645101 := by
  apply nodeValid_prime [2, 5, 13, 37951, 162577] ⟨8020947645101, 2, [(2, 2), (5, 2), (13, 1), (37951, 1), (162577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_37951
    · exact prime_162577
  · decide +kernel

theorem prime_8020947649279 : Nat.Prime 8020947649279 := by
  apply nodeValid_prime [2, 3, 59, 60589, 373963] ⟨8020947649279, 3, [(2, 1), (3, 1), (59, 1), (60589, 1), (373963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_60589
    · exact prime_373963
  · decide +kernel

theorem prime_8020947650497 : Nat.Prime 8020947650497 := by
  apply nodeValid_prime [2, 3, 11, 7853, 483611] ⟨8020947650497, 5, [(2, 6), (3, 1), (11, 1), (7853, 1), (483611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_7853
    · exact prime_483611
  · decide +kernel

theorem prime_8026287314789 : Nat.Prime 8026287314789 := by
  apply nodeValid_prime [2, 2999, 669080303] ⟨8026287314789, 2, [(2, 2), (2999, 1), (669080303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2999
    · exact prime_669080303
  · decide +kernel

theorem prime_8026287315587 : Nat.Prime 8026287315587 := by
  apply nodeValid_prime [2, 4013143657793] ⟨8026287315587, 2, [(2, 1), (4013143657793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4013143657793
  · decide +kernel

theorem prime_8026287416281 : Nat.Prime 8026287416281 := by
  apply nodeValid_prime [2, 3, 5, 7, 15913, 200153] ⟨8026287416281, 11, [(2, 3), (3, 2), (5, 1), (7, 1), (15913, 1), (200153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_15913
    · exact prime_200153
  · decide +kernel

theorem prime_8031629524063 : Nat.Prime 8031629524063 := by
  apply nodeValid_prime [2, 3, 1338604920677] ⟨8031629524063, 3, [(2, 1), (3, 1), (1338604920677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1338604920677
  · decide +kernel

theorem prime_8031629524147 : Nat.Prime 8031629524147 := by
  apply nodeValid_prime [2, 3, 17, 78741465923] ⟨8031629524147, 2, [(2, 1), (3, 1), (17, 1), (78741465923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_78741465923
  · decide +kernel

theorem prime_8031629585747 : Nat.Prime 8031629585747 := by
  apply nodeValid_prime [2, 13, 251, 3209, 383519] ⟨8031629585747, 2, [(2, 1), (13, 1), (251, 1), (3209, 1), (383519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_251
    · exact prime_3209
    · exact prime_383519
  · decide +kernel

theorem prime_8036974142221 : Nat.Prime 8036974142221 := by
  apply nodeValid_prime [2, 3, 5, 133949569037] ⟨8036974142221, 6, [(2, 2), (3, 1), (5, 1), (133949569037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_133949569037
  · decide +kernel

theorem prime_8036974144723 : Nat.Prime 8036974144723 := by
  apply nodeValid_prime [2, 3, 59, 19037, 1192589] ⟨8036974144723, 2, [(2, 1), (3, 1), (59, 1), (19037, 1), (1192589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_19037
    · exact prime_1192589
  · decide +kernel

theorem prime_8036974155281 : Nat.Prime 8036974155281 := by
  apply nodeValid_prime [2, 5, 7, 659, 3111151] ⟨8036974155281, 3, [(2, 4), (5, 1), (7, 2), (659, 1), (3111151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_659
    · exact prime_3111151
  · decide +kernel

theorem prime_8042321136347 : Nat.Prime 8042321136347 := by
  apply nodeValid_prime [2, 7, 574451509739] ⟨8042321136347, 2, [(2, 1), (7, 1), (574451509739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_574451509739
  · decide +kernel

theorem prime_8042321165231 : Nat.Prime 8042321165231 := by
  apply nodeValid_prime [2, 5, 11, 101, 421, 1719433] ⟨8042321165231, 11, [(2, 1), (5, 1), (11, 1), (101, 1), (421, 1), (1719433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_101
    · exact prime_421
    · exact prime_1719433
  · decide +kernel

theorem prime_8042321165261 : Nat.Prime 8042321165261 := by
  apply nodeValid_prime [2, 5, 23, 17483306881] ⟨8042321165261, 2, [(2, 2), (5, 1), (23, 1), (17483306881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_17483306881
  · decide +kernel

theorem prime_8047670525747 : Nat.Prime 8047670525747 := by
  apply nodeValid_prime [2, 239, 16836130807] ⟨8047670525747, 2, [(2, 1), (239, 1), (16836130807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_16836130807
  · decide +kernel

theorem prime_8047670528939 : Nat.Prime 8047670528939 := by
  apply nodeValid_prime [2, 32309, 124542241] ⟨8047670528939, 2, [(2, 1), (32309, 1), (124542241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32309
    · exact prime_124542241
  · decide +kernel

theorem prime_8047670530937 : Nat.Prime 8047670530937 := by
  apply nodeValid_prime [2, 41, 24535580887] ⟨8047670530937, 3, [(2, 3), (41, 1), (24535580887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_24535580887
  · decide +kernel

theorem prime_8053022317763 : Nat.Prime 8053022317763 := by
  apply nodeValid_prime [2, 41, 139, 389, 1816271] ⟨8053022317763, 2, [(2, 1), (41, 1), (139, 1), (389, 1), (1816271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_139
    · exact prime_389
    · exact prime_1816271
  · decide +kernel

theorem prime_8053022395013 : Nat.Prime 8053022395013 := by
  apply nodeValid_prime [2, 7, 19, 15137260141] ⟨8053022395013, 2, [(2, 2), (7, 1), (19, 1), (15137260141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_15137260141
  · decide +kernel

theorem prime_8053022395351 : Nat.Prime 8053022395351 := by
  apply nodeValid_prime [2, 3, 5, 103, 173743741] ⟨8053022395351, 3, [(2, 1), (3, 2), (5, 2), (103, 1), (173743741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_173743741
  · decide +kernel

end Sude.Lucas.Generated
