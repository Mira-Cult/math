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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2213 : Nat.Prime 2213 := by
  apply nodeValid_prime [2, 7, 79] ⟨2213, 2, [(2, 2), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_2297 : Nat.Prime 2297 := by
  apply nodeValid_prime [2, 7, 41] ⟨2297, 5, [(2, 3), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_2687 : Nat.Prime 2687 := by
  apply nodeValid_prime [2, 17, 79] ⟨2687, 5, [(2, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_3271 : Nat.Prime 3271 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨3271, 3, [(2, 1), (3, 1), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_3343 : Nat.Prime 3343 := by
  apply nodeValid_prime [2, 3, 557] ⟨3343, 5, [(2, 1), (3, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
  · decide +kernel

theorem prime_3511 : Nat.Prime 3511 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨3511, 7, [(2, 1), (3, 3), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_4241 : Nat.Prime 4241 := by
  apply nodeValid_prime [2, 5, 53] ⟨4241, 3, [(2, 4), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_4243 : Nat.Prime 4243 := by
  apply nodeValid_prime [2, 3, 7, 101] ⟨4243, 2, [(2, 1), (3, 1), (7, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
  · decide +kernel

theorem prime_4909 : Nat.Prime 4909 := by
  apply nodeValid_prime [2, 3, 409] ⟨4909, 6, [(2, 2), (3, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_409
  · decide +kernel

theorem prime_6563 : Nat.Prime 6563 := by
  apply nodeValid_prime [2, 17, 193] ⟨6563, 5, [(2, 1), (17, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_193
  · decide +kernel

theorem prime_6659 : Nat.Prime 6659 := by
  apply nodeValid_prime [2, 3329] ⟨6659, 2, [(2, 1), (3329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3329
  · decide +kernel

theorem prime_6959 : Nat.Prime 6959 := by
  apply nodeValid_prime [2, 7, 71] ⟨6959, 7, [(2, 1), (7, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_7001 : Nat.Prime 7001 := by
  apply nodeValid_prime [2, 5, 7] ⟨7001, 3, [(2, 3), (5, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_7121 : Nat.Prime 7121 := by
  apply nodeValid_prime [2, 5, 89] ⟨7121, 3, [(2, 4), (5, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_7321 : Nat.Prime 7321 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨7321, 7, [(2, 3), (3, 1), (5, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_7561 : Nat.Prime 7561 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨7561, 13, [(2, 3), (3, 3), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_10529 : Nat.Prime 10529 := by
  apply nodeValid_prime [2, 7, 47] ⟨10529, 3, [(2, 5), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_11173 : Nat.Prime 11173 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨11173, 5, [(2, 2), (3, 1), (7, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_11491 : Nat.Prime 11491 := by
  apply nodeValid_prime [2, 3, 5, 383] ⟨11491, 3, [(2, 1), (3, 1), (5, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
  · decide +kernel

theorem prime_12253 : Nat.Prime 12253 := by
  apply nodeValid_prime [2, 3, 1021] ⟨12253, 2, [(2, 2), (3, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
  · decide +kernel

theorem prime_13313 : Nat.Prime 13313 := by
  apply nodeValid_prime [2, 13] ⟨13313, 3, [(2, 10), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13
  · decide +kernel

theorem prime_13883 : Nat.Prime 13883 := by
  apply nodeValid_prime [2, 11, 631] ⟨13883, 2, [(2, 1), (11, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_631
  · decide +kernel

theorem prime_14447 : Nat.Prime 14447 := by
  apply nodeValid_prime [2, 31, 233] ⟨14447, 5, [(2, 1), (31, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_233
  · decide +kernel

theorem prime_14503 : Nat.Prime 14503 := by
  apply nodeValid_prime [2, 3, 2417] ⟨14503, 3, [(2, 1), (3, 1), (2417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2417
  · decide +kernel

theorem prime_15817 : Nat.Prime 15817 := by
  apply nodeValid_prime [2, 3, 659] ⟨15817, 5, [(2, 3), (3, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_659
  · decide +kernel

theorem prime_15971 : Nat.Prime 15971 := by
  apply nodeValid_prime [2, 5, 1597] ⟨15971, 2, [(2, 1), (5, 1), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1597
  · decide +kernel

theorem prime_16111 : Nat.Prime 16111 := by
  apply nodeValid_prime [2, 3, 5, 179] ⟨16111, 7, [(2, 1), (3, 2), (5, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
  · decide +kernel

theorem prime_17443 : Nat.Prime 17443 := by
  apply nodeValid_prime [2, 3, 17, 19] ⟨17443, 2, [(2, 1), (3, 3), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_17551 : Nat.Prime 17551 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨17551, 3, [(2, 1), (3, 3), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_19583 : Nat.Prime 19583 := by
  apply nodeValid_prime [2, 9791] ⟨19583, 5, [(2, 1), (9791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9791
  · decide +kernel

theorem prime_22013 : Nat.Prime 22013 := by
  apply nodeValid_prime [2, 5503] ⟨22013, 2, [(2, 2), (5503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5503
  · decide +kernel

theorem prime_22877 : Nat.Prime 22877 := by
  apply nodeValid_prime [2, 7, 19, 43] ⟨22877, 2, [(2, 2), (7, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_24907 : Nat.Prime 24907 := by
  apply nodeValid_prime [2, 3, 7, 593] ⟨24907, 2, [(2, 1), (3, 1), (7, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_593
  · decide +kernel

theorem prime_26627 : Nat.Prime 26627 := by
  apply nodeValid_prime [2, 13313] ⟨26627, 2, [(2, 1), (13313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13313
  · decide +kernel

theorem prime_30817 : Nat.Prime 30817 := by
  apply nodeValid_prime [2, 3, 107] ⟨30817, 5, [(2, 5), (3, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
  · decide +kernel

theorem prime_30983 : Nat.Prime 30983 := by
  apply nodeValid_prime [2, 7, 2213] ⟨30983, 5, [(2, 1), (7, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2213
  · decide +kernel

theorem prime_36587 : Nat.Prime 36587 := by
  apply nodeValid_prime [2, 11, 1663] ⟨36587, 2, [(2, 1), (11, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1663
  · decide +kernel

theorem prime_43237 : Nat.Prime 43237 := by
  apply nodeValid_prime [2, 3, 1201] ⟨43237, 2, [(2, 2), (3, 2), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1201
  · decide +kernel

theorem prime_44027 : Nat.Prime 44027 := by
  apply nodeValid_prime [2, 22013] ⟨44027, 2, [(2, 1), (22013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22013
  · decide +kernel

theorem prime_44449 : Nat.Prime 44449 := by
  apply nodeValid_prime [2, 3, 463] ⟨44449, 13, [(2, 5), (3, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
  · decide +kernel

theorem prime_50383 : Nat.Prime 50383 := by
  apply nodeValid_prime [2, 3, 311] ⟨50383, 3, [(2, 1), (3, 4), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
  · decide +kernel

theorem prime_57203 : Nat.Prime 57203 := by
  apply nodeValid_prime [2, 37, 773] ⟨57203, 2, [(2, 1), (37, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_773
  · decide +kernel

theorem prime_61979 : Nat.Prime 61979 := by
  apply nodeValid_prime [2, 7, 19, 233] ⟨61979, 2, [(2, 1), (7, 1), (19, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_233
  · decide +kernel

theorem prime_65129 : Nat.Prime 65129 := by
  apply nodeValid_prime [2, 7, 1163] ⟨65129, 3, [(2, 3), (7, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1163
  · decide +kernel

theorem prime_81701 : Nat.Prime 81701 := by
  apply nodeValid_prime [2, 5, 19, 43] ⟨81701, 2, [(2, 2), (5, 2), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_90373 : Nat.Prime 90373 := by
  apply nodeValid_prime [2, 3, 17, 443] ⟨90373, 5, [(2, 2), (3, 1), (17, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_443
  · decide +kernel

theorem prime_119689 : Nat.Prime 119689 := by
  apply nodeValid_prime [2, 3, 4987] ⟨119689, 7, [(2, 3), (3, 1), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4987
  · decide +kernel

theorem prime_130259 : Nat.Prime 130259 := by
  apply nodeValid_prime [2, 65129] ⟨130259, 2, [(2, 1), (65129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_65129
  · decide +kernel

theorem prime_132527 : Nat.Prime 132527 := by
  apply nodeValid_prime [2, 23, 43, 67] ⟨132527, 5, [(2, 1), (23, 1), (43, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
    · exact prime_67
  · decide +kernel

theorem prime_152533 : Nat.Prime 152533 := by
  apply nodeValid_prime [2, 3, 19, 223] ⟨152533, 2, [(2, 2), (3, 2), (19, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_223
  · decide +kernel

theorem prime_159763 : Nat.Prime 159763 := by
  apply nodeValid_prime [2, 3, 26627] ⟨159763, 2, [(2, 1), (3, 1), (26627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26627
  · decide +kernel

theorem prime_177797 : Nat.Prime 177797 := by
  apply nodeValid_prime [2, 44449] ⟨177797, 2, [(2, 2), (44449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44449
  · decide +kernel

theorem prime_184057 : Nat.Prime 184057 := by
  apply nodeValid_prime [2, 3, 7669] ⟨184057, 5, [(2, 3), (3, 1), (7669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7669
  · decide +kernel

theorem prime_188711 : Nat.Prime 188711 := by
  apply nodeValid_prime [2, 5, 113, 167] ⟨188711, 17, [(2, 1), (5, 1), (113, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
    · exact prime_167
  · decide +kernel

theorem prime_195817 : Nat.Prime 195817 := by
  apply nodeValid_prime [2, 3, 41, 199] ⟨195817, 5, [(2, 3), (3, 1), (41, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_199
  · decide +kernel

theorem prime_196477 : Nat.Prime 196477 := by
  apply nodeValid_prime [2, 3, 7, 2339] ⟨196477, 2, [(2, 2), (3, 1), (7, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2339
  · decide +kernel

theorem prime_199399 : Nat.Prime 199399 := by
  apply nodeValid_prime [2, 3, 167, 199] ⟨199399, 7, [(2, 1), (3, 1), (167, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_199
  · decide +kernel

theorem prime_225931 : Nat.Prime 225931 := by
  apply nodeValid_prime [2, 3, 5, 17, 443] ⟨225931, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_443
  · decide +kernel

theorem prime_229529 : Nat.Prime 229529 := by
  apply nodeValid_prime [2, 13, 2207] ⟨229529, 3, [(2, 3), (13, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2207
  · decide +kernel

theorem prime_249677 : Nat.Prime 249677 := by
  apply nodeValid_prime [2, 7, 37, 241] ⟨249677, 2, [(2, 2), (7, 1), (37, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_241
  · decide +kernel

theorem prime_303097 : Nat.Prime 303097 := by
  apply nodeValid_prime [2, 3, 73, 173] ⟨303097, 5, [(2, 3), (3, 1), (73, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_173
  · decide +kernel

theorem prime_303371 : Nat.Prime 303371 := by
  apply nodeValid_prime [2, 5, 23, 1319] ⟨303371, 2, [(2, 1), (5, 1), (23, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1319
  · decide +kernel

theorem prime_304411 : Nat.Prime 304411 := by
  apply nodeValid_prime [2, 3, 5, 73, 139] ⟨304411, 2, [(2, 1), (3, 1), (5, 1), (73, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_139
  · decide +kernel

theorem prime_312931 : Nat.Prime 312931 := by
  apply nodeValid_prime [2, 3, 5, 19, 61] ⟨312931, 3, [(2, 1), (3, 3), (5, 1), (19, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_332951 : Nat.Prime 332951 := by
  apply nodeValid_prime [2, 5, 6659] ⟨332951, 11, [(2, 1), (5, 2), (6659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6659
  · decide +kernel

theorem prime_337529 : Nat.Prime 337529 := by
  apply nodeValid_prime [2, 31, 1361] ⟨337529, 3, [(2, 3), (31, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1361
  · decide +kernel

theorem prime_350437 : Nat.Prime 350437 := by
  apply nodeValid_prime [2, 3, 19, 29, 53] ⟨350437, 6, [(2, 2), (3, 1), (19, 1), (29, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_53
  · decide +kernel

theorem prime_352217 : Nat.Prime 352217 := by
  apply nodeValid_prime [2, 44027] ⟨352217, 3, [(2, 3), (44027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44027
  · decide +kernel

theorem prime_354743 : Nat.Prime 354743 := by
  apply nodeValid_prime [2, 83, 2137] ⟨354743, 5, [(2, 1), (83, 1), (2137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_2137
  · decide +kernel

theorem prime_416491 : Nat.Prime 416491 := by
  apply nodeValid_prime [2, 3, 5, 13883] ⟨416491, 2, [(2, 1), (3, 1), (5, 1), (13883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13883
  · decide +kernel

theorem prime_533857 : Nat.Prime 533857 := by
  apply nodeValid_prime [2, 3, 67, 83] ⟨533857, 5, [(2, 5), (3, 1), (67, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_83
  · decide +kernel

theorem prime_639053 : Nat.Prime 639053 := by
  apply nodeValid_prime [2, 159763] ⟨639053, 2, [(2, 2), (159763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_159763
  · decide +kernel

theorem prime_679897 : Nat.Prime 679897 := by
  apply nodeValid_prime [2, 3, 7, 19, 71] ⟨679897, 10, [(2, 3), (3, 2), (7, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_858397 : Nat.Prime 858397 := by
  apply nodeValid_prime [2, 3, 7, 11, 929] ⟨858397, 6, [(2, 2), (3, 1), (7, 1), (11, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_929
  · decide +kernel

theorem prime_1084477 : Nat.Prime 1084477 := by
  apply nodeValid_prime [2, 3, 90373] ⟨1084477, 2, [(2, 2), (3, 1), (90373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_90373
  · decide +kernel

theorem prime_1099391 : Nat.Prime 1099391 := by
  apply nodeValid_prime [2, 5, 17, 29, 223] ⟨1099391, 13, [(2, 1), (5, 1), (17, 1), (29, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_29
    · exact prime_223
  · decide +kernel

theorem prime_1248209 : Nat.Prime 1248209 := by
  apply nodeValid_prime [2, 13, 17, 353] ⟨1248209, 3, [(2, 4), (13, 1), (17, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_353
  · decide +kernel

theorem prime_1277651 : Nat.Prime 1277651 := by
  apply nodeValid_prime [2, 5, 11, 23, 101] ⟨1277651, 6, [(2, 1), (5, 2), (11, 1), (23, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_101
  · decide +kernel

theorem prime_1278107 : Nat.Prime 1278107 := by
  apply nodeValid_prime [2, 639053] ⟨1278107, 2, [(2, 1), (639053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_639053
  · decide +kernel

theorem prime_1409977 : Nat.Prime 1409977 := by
  apply nodeValid_prime [2, 3, 19583] ⟨1409977, 11, [(2, 3), (3, 2), (19583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19583
  · decide +kernel

theorem prime_1665091 : Nat.Prime 1665091 := by
  apply nodeValid_prime [2, 3, 5, 7, 881] ⟨1665091, 2, [(2, 1), (3, 3), (5, 1), (7, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_881
  · decide +kernel

theorem prime_1887181 : Nat.Prime 1887181 := by
  apply nodeValid_prime [2, 3, 5, 71, 443] ⟨1887181, 2, [(2, 2), (3, 1), (5, 1), (71, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_443
  · decide +kernel

theorem prime_2102623 : Nat.Prime 2102623 := by
  apply nodeValid_prime [2, 3, 350437] ⟨2102623, 3, [(2, 1), (3, 1), (350437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_350437
  · decide +kernel

theorem prime_2555303 : Nat.Prime 2555303 := by
  apply nodeValid_prime [2, 1277651] ⟨2555303, 5, [(2, 1), (1277651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1277651
  · decide +kernel

theorem prime_3091763 : Nat.Prime 3091763 := by
  apply nodeValid_prime [2, 673, 2297] ⟨3091763, 2, [(2, 1), (673, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_673
    · exact prime_2297
  · decide +kernel

theorem prime_3384319 : Nat.Prime 3384319 := by
  apply nodeValid_prime [2, 3, 7, 19, 4241] ⟨3384319, 7, [(2, 1), (3, 1), (7, 1), (19, 1), (4241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_4241
  · decide +kernel

theorem prime_6011627 : Nat.Prime 6011627 := by
  apply nodeValid_prime [2, 1061, 2833] ⟨6011627, 2, [(2, 1), (1061, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1061
    · exact prime_2833
  · decide +kernel

theorem prime_6136997 : Nat.Prime 6136997 := by
  apply nodeValid_prime [2, 97, 15817] ⟨6136997, 2, [(2, 2), (97, 1), (15817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_15817
  · decide +kernel

theorem prime_8267003 : Nat.Prime 8267003 := by
  apply nodeValid_prime [2, 311, 13291] ⟨8267003, 2, [(2, 1), (311, 1), (13291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_13291
  · decide +kernel

theorem prime_12195793 : Nat.Prime 12195793 := by
  apply nodeValid_prime [2, 3, 7, 37, 109] ⟨12195793, 31, [(2, 4), (3, 3), (7, 1), (37, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_109
  · decide +kernel

theorem prime_12679813 : Nat.Prime 12679813 := by
  apply nodeValid_prime [2, 3, 352217] ⟨12679813, 2, [(2, 2), (3, 2), (352217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_352217
  · decide +kernel

theorem prime_12741583 : Nat.Prime 12741583 := by
  apply nodeValid_prime [2, 3, 7, 303371] ⟨12741583, 3, [(2, 1), (3, 1), (7, 1), (303371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_303371
  · decide +kernel

theorem prime_12832349 : Nat.Prime 12832349 := by
  apply nodeValid_prime [2, 17, 188711] ⟨12832349, 2, [(2, 2), (17, 1), (188711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_188711
  · decide +kernel

theorem prime_13328261 : Nat.Prime 13328261 := by
  apply nodeValid_prime [2, 5, 11, 47, 1289] ⟨13328261, 2, [(2, 2), (5, 1), (11, 1), (47, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
    · exact prime_1289
  · decide +kernel

theorem prime_16433089 : Nat.Prime 16433089 := by
  apply nodeValid_prime [2, 3, 7, 12227] ⟨16433089, 11, [(2, 6), (3, 1), (7, 1), (12227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12227
  · decide +kernel

theorem prime_22264381 : Nat.Prime 22264381 := by
  apply nodeValid_prime [2, 3, 5, 37, 3343] ⟨22264381, 2, [(2, 2), (3, 2), (5, 1), (37, 1), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_3343
  · decide +kernel

theorem prime_28091927 : Nat.Prime 28091927 := by
  apply nodeValid_prime [2, 79, 177797] ⟨28091927, 5, [(2, 1), (79, 1), (177797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_177797
  · decide +kernel

theorem prime_30804373 : Nat.Prime 30804373 := by
  apply nodeValid_prime [2, 3, 59, 14503] ⟨30804373, 2, [(2, 2), (3, 2), (59, 1), (14503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_14503
  · decide +kernel

theorem prime_33641969 : Nat.Prime 33641969 := by
  apply nodeValid_prime [2, 2102623] ⟨33641969, 3, [(2, 4), (2102623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2102623
  · decide +kernel

theorem prime_35345473 : Nat.Prime 35345473 := by
  apply nodeValid_prime [2, 3, 19, 9689] ⟨35345473, 5, [(2, 6), (3, 1), (19, 1), (9689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_9689
  · decide +kernel

theorem prime_59046343 : Nat.Prime 59046343 := by
  apply nodeValid_prime [2, 3, 73, 113, 1193] ⟨59046343, 3, [(2, 1), (3, 1), (73, 1), (113, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_113
    · exact prime_1193
  · decide +kernel

theorem prime_62496877 : Nat.Prime 62496877 := by
  apply nodeValid_prime [2, 3, 13, 30817] ⟨62496877, 5, [(2, 2), (3, 1), (13, 2), (30817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_30817
  · decide +kernel

theorem prime_87061951 : Nat.Prime 87061951 := by
  apply nodeValid_prime [2, 3, 5, 31, 79] ⟨87061951, 3, [(2, 1), (3, 2), (5, 2), (31, 1), (79, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_79
  · decide +kernel

theorem prime_88075879 : Nat.Prime 88075879 := by
  apply nodeValid_prime [2, 3, 11, 17, 23, 3413] ⟨88075879, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (23, 1), (3413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_23
    · exact prime_3413
  · decide +kernel

theorem prime_95086793 : Nat.Prime 95086793 := by
  apply nodeValid_prime [2, 19, 83, 7537] ⟨95086793, 3, [(2, 3), (19, 1), (83, 1), (7537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_83
    · exact prime_7537
  · decide +kernel

theorem prime_121957931 : Nat.Prime 121957931 := by
  apply nodeValid_prime [2, 5, 12195793] ⟨121957931, 2, [(2, 1), (5, 1), (12195793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12195793
  · decide +kernel

theorem prime_153988189 : Nat.Prime 153988189 := by
  apply nodeValid_prime [2, 3, 12832349] ⟨153988189, 2, [(2, 2), (3, 1), (12832349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12832349
  · decide +kernel

theorem prime_274657883 : Nat.Prime 274657883 := by
  apply nodeValid_prime [2, 17, 19, 37, 11491] ⟨274657883, 2, [(2, 1), (17, 1), (19, 1), (37, 1), (11491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_37
    · exact prime_11491
  · decide +kernel

theorem prime_460126493 : Nat.Prime 460126493 := by
  apply nodeValid_prime [2, 7, 16433089] ⟨460126493, 2, [(2, 2), (7, 1), (16433089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_16433089
  · decide +kernel

theorem prime_479817397 : Nat.Prime 479817397 := by
  apply nodeValid_prime [2, 3, 13328261] ⟨479817397, 7, [(2, 2), (3, 2), (13328261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13328261
  · decide +kernel

theorem prime_618995369 : Nat.Prime 618995369 := by
  apply nodeValid_prime [2, 41, 1887181] ⟨618995369, 3, [(2, 3), (41, 1), (1887181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1887181
  · decide +kernel

theorem prime_685325479 : Nat.Prime 685325479 := by
  apply nodeValid_prime [2, 3, 19, 6011627] ⟨685325479, 3, [(2, 1), (3, 1), (19, 1), (6011627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_6011627
  · decide +kernel

theorem prime_896601023 : Nat.Prime 896601023 := by
  apply nodeValid_prime [2, 12253, 36587] ⟨896601023, 5, [(2, 1), (12253, 1), (36587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_12253
    · exact prime_36587
  · decide +kernel

theorem prime_920252987 : Nat.Prime 920252987 := by
  apply nodeValid_prime [2, 460126493] ⟨920252987, 2, [(2, 1), (460126493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_460126493
  · decide +kernel

theorem prime_944741489 : Nat.Prime 944741489 := by
  apply nodeValid_prime [2, 59046343] ⟨944741489, 3, [(2, 4), (59046343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59046343
  · decide +kernel

theorem prime_1112394961 : Nat.Prime 1112394961 := by
  apply nodeValid_prime [2, 3, 5, 1039, 1487] ⟨1112394961, 11, [(2, 4), (3, 2), (5, 1), (1039, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1039
    · exact prime_1487
  · decide +kernel

theorem prime_1237990739 : Nat.Prime 1237990739 := by
  apply nodeValid_prime [2, 618995369] ⟨1237990739, 2, [(2, 1), (618995369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_618995369
  · decide +kernel

theorem prime_1452043097 : Nat.Prime 1452043097 := by
  apply nodeValid_prime [2, 7, 37, 487, 1439] ⟨1452043097, 3, [(2, 3), (7, 1), (37, 1), (487, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_487
    · exact prime_1439
  · decide +kernel

theorem prime_1473776383 : Nat.Prime 1473776383 := by
  apply nodeValid_prime [2, 3, 13, 19, 23, 43237] ⟨1473776383, 7, [(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (43237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_23
    · exact prime_43237
  · decide +kernel

theorem prime_3691809479 : Nat.Prime 3691809479 := by
  apply nodeValid_prime [2, 7, 19, 59, 67, 3511] ⟨3691809479, 7, [(2, 1), (7, 1), (19, 1), (59, 1), (67, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_59
    · exact prime_67
    · exact prime_3511
  · decide +kernel

theorem prime_3820086043 : Nat.Prime 3820086043 := by
  apply nodeValid_prime [2, 3, 31, 103, 199399] ⟨3820086043, 2, [(2, 1), (3, 1), (31, 1), (103, 1), (199399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_103
    · exact prime_199399
  · decide +kernel

theorem prime_4942099619 : Nat.Prime 4942099619 := by
  apply nodeValid_prime [2, 7321, 337529] ⟨4942099619, 2, [(2, 1), (7321, 1), (337529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7321
    · exact prime_337529
  · decide +kernel

theorem prime_7472452583 : Nat.Prime 7472452583 := by
  apply nodeValid_prime [2, 7, 19, 28091927] ⟨7472452583, 10, [(2, 1), (7, 1), (19, 1), (28091927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_28091927
  · decide +kernel

theorem prime_8842658299 : Nat.Prime 8842658299 := by
  apply nodeValid_prime [2, 3, 1473776383] ⟨8842658299, 3, [(2, 1), (3, 1), (1473776383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1473776383
  · decide +kernel

theorem prime_8931314963 : Nat.Prime 8931314963 := by
  apply nodeValid_prime [2, 29, 153988189] ⟨8931314963, 2, [(2, 1), (29, 1), (153988189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_153988189
  · decide +kernel

theorem prime_14855888869 : Nat.Prime 14855888869 := by
  apply nodeValid_prime [2, 3, 1237990739] ⟨14855888869, 2, [(2, 2), (3, 1), (1237990739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1237990739
  · decide +kernel

theorem prime_16513805071 : Nat.Prime 16513805071 := by
  apply nodeValid_prime [2, 3, 5, 7, 1248209] ⟨16513805071, 6, [(2, 1), (3, 3), (5, 1), (7, 2), (1248209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1248209
  · decide +kernel

theorem prime_33292682263 : Nat.Prime 33292682263 := by
  apply nodeValid_prime [2, 3, 7, 88075879] ⟨33292682263, 3, [(2, 1), (3, 3), (7, 1), (88075879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_88075879
  · decide +kernel

theorem prime_43948766161 : Nat.Prime 43948766161 := by
  apply nodeValid_prime [2, 3, 5, 13, 23, 7561] ⟨43948766161, 7, [(2, 4), (3, 5), (5, 1), (13, 1), (23, 1), (7561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_7561
  · decide +kernel

theorem prime_130007149313 : Nat.Prime 130007149313 := by
  apply nodeValid_prime [2, 4243, 119689] ⟨130007149313, 3, [(2, 8), (4243, 1), (119689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4243
    · exact prime_119689
  · decide +kernel

theorem prime_133170729053 : Nat.Prime 133170729053 := by
  apply nodeValid_prime [2, 33292682263] ⟨133170729053, 2, [(2, 2), (33292682263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33292682263
  · decide +kernel

theorem prime_258969737839 : Nat.Prime 258969737839 := by
  apply nodeValid_prime [2, 3, 7, 19, 127, 2555303] ⟨258969737839, 6, [(2, 1), (3, 1), (7, 1), (19, 1), (127, 1), (2555303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_127
    · exact prime_2555303
  · decide +kernel

theorem prime_258969738103 : Nat.Prime 258969738103 := by
  apply nodeValid_prime [2, 3, 17, 223, 1019, 11173] ⟨258969738103, 3, [(2, 1), (3, 1), (17, 1), (223, 1), (1019, 1), (11173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_223
    · exact prime_1019
    · exact prime_11173
  · decide +kernel

theorem prime_258969795247 : Nat.Prime 258969795247 := by
  apply nodeValid_prime [2, 3, 79, 131, 1907] ⟨258969795247, 7, [(2, 1), (3, 8), (79, 1), (131, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_131
    · exact prime_1907
  · decide +kernel

theorem prime_259491666557 : Nat.Prime 259491666557 := by
  apply nodeValid_prime [2, 23, 7951, 354743] ⟨259491666557, 2, [(2, 2), (23, 1), (7951, 1), (354743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_7951
    · exact prime_354743
  · decide +kernel

theorem prime_259491668591 : Nat.Prime 259491668591 := by
  apply nodeValid_prime [2, 5, 7, 11, 109, 3091763] ⟨259491668591, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (109, 1), (3091763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_109
    · exact prime_3091763
  · decide +kernel

theorem prime_259491696307 : Nat.Prime 259491696307 := by
  apply nodeValid_prime [2, 3, 50383, 858397] ⟨259491696307, 3, [(2, 1), (3, 1), (50383, 1), (858397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50383
    · exact prime_858397
  · decide +kernel

theorem prime_260014296671 : Nat.Prime 260014296671 := by
  apply nodeValid_prime [2, 5, 29, 896601023] ⟨260014296671, 17, [(2, 1), (5, 1), (29, 1), (896601023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_896601023
  · decide +kernel

theorem prime_260014298627 : Nat.Prime 260014298627 := by
  apply nodeValid_prime [2, 130007149313] ⟨260014298627, 2, [(2, 1), (130007149313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_130007149313
  · decide +kernel

theorem prime_260014308893 : Nat.Prime 260014308893 := by
  apply nodeValid_prime [2, 13, 41, 121957931] ⟨260014308893, 2, [(2, 2), (13, 1), (41, 1), (121957931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_121957931
  · decide +kernel

theorem prime_260537636347 : Nat.Prime 260537636347 := by
  apply nodeValid_prime [2, 3, 13, 67, 7001, 7121] ⟨260537636347, 2, [(2, 1), (3, 1), (13, 1), (67, 1), (7001, 1), (7121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
    · exact prime_7001
    · exact prime_7121
  · decide +kernel

theorem prime_260537651443 : Nat.Prime 260537651443 := by
  apply nodeValid_prime [2, 3, 47, 673, 152533] ⟨260537651443, 2, [(2, 1), (3, 3), (47, 1), (673, 1), (152533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_673
    · exact prime_152533
  · decide +kernel

theorem prime_260537651573 : Nat.Prime 260537651573 := by
  apply nodeValid_prime [2, 11, 2749, 195817] ⟨260537651573, 2, [(2, 2), (11, 2), (2749, 1), (195817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2749
    · exact prime_195817
  · decide +kernel

theorem prime_261061663319 : Nat.Prime 261061663319 := by
  apply nodeValid_prime [2, 31, 22877, 184057] ⟨261061663319, 7, [(2, 1), (31, 1), (22877, 1), (184057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_22877
    · exact prime_184057
  · decide +kernel

theorem prime_261061663579 : Nat.Prime 261061663579 := by
  apply nodeValid_prime [2, 3, 1231, 35345473] ⟨261061663579, 2, [(2, 1), (3, 1), (1231, 1), (35345473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1231
    · exact prime_35345473
  · decide +kernel

theorem prime_261061679441 : Nat.Prime 261061679441 := by
  apply nodeValid_prime [2, 5, 97, 33641969] ⟨261061679441, 3, [(2, 4), (5, 1), (97, 1), (33641969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_33641969
  · decide +kernel

theorem prime_261586436201 : Nat.Prime 261586436201 := by
  apply nodeValid_prime [2, 5, 677, 719, 2687] ⟨261586436201, 3, [(2, 3), (5, 2), (677, 1), (719, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_677
    · exact prime_719
    · exact prime_2687
  · decide +kernel

theorem prime_261586485583 : Nat.Prime 261586485583 := by
  apply nodeValid_prime [2, 3, 47, 241, 15971] ⟨261586485583, 3, [(2, 1), (3, 1), (47, 1), (241, 2), (15971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_241
    · exact prime_15971
  · decide +kernel

theorem prime_261586485679 : Nat.Prime 261586485679 := by
  apply nodeValid_prime [2, 3, 7, 17, 877, 417751] ⟨261586485679, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (877, 1), (417751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_877
    · exact prime_417751
  · decide +kernel

theorem prime_262111902139 : Nat.Prime 262111902139 := by
  apply nodeValid_prime [2, 3, 233, 62496877] ⟨262111902139, 2, [(2, 1), (3, 2), (233, 1), (62496877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_62496877
  · decide +kernel

theorem prime_262111902841 : Nat.Prime 262111902841 := by
  apply nodeValid_prime [2, 3, 5, 41, 61, 89, 3271] ⟨262111902841, 21, [(2, 3), (3, 2), (5, 1), (41, 1), (61, 1), (89, 1), (3271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_61
    · exact prime_89
    · exact prime_3271
  · decide +kernel

theorem prime_262111904347 : Nat.Prime 262111904347 := by
  apply nodeValid_prime [2, 3, 30983, 1409977] ⟨262111904347, 2, [(2, 1), (3, 1), (30983, 1), (1409977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30983
    · exact prime_1409977
  · decide +kernel

theorem prime_262638084199 : Nat.Prime 262638084199 := by
  apply nodeValid_prime [2, 3, 7, 29, 30804373] ⟨262638084199, 3, [(2, 1), (3, 1), (7, 2), (29, 1), (30804373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_30804373
  · decide +kernel

theorem prime_262638133613 : Nat.Prime 262638133613 := by
  apply nodeValid_prime [2, 47, 839, 1665091] ⟨262638133613, 2, [(2, 2), (47, 1), (839, 1), (1665091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_839
    · exact prime_1665091
  · decide +kernel

theorem prime_262638133943 : Nat.Prime 262638133943 := by
  apply nodeValid_prime [2, 139, 944741489] ⟨262638133943, 5, [(2, 1), (139, 1), (944741489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_944741489
  · decide +kernel

theorem prime_263164983421 : Nat.Prime 263164983421 := by
  apply nodeValid_prime [2, 3, 5, 197, 22264381] ⟨263164983421, 2, [(2, 2), (3, 1), (5, 1), (197, 1), (22264381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
    · exact prime_22264381
  · decide +kernel

theorem prime_263164983937 : Nat.Prime 263164983937 := by
  apply nodeValid_prime [2, 3, 685325479] ⟨263164983937, 5, [(2, 7), (3, 1), (685325479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_685325479
  · decide +kernel

theorem prime_263164985359 : Nat.Prime 263164985359 := by
  apply nodeValid_prime [2, 3, 11, 131, 3761, 8093] ⟨263164985359, 3, [(2, 1), (3, 1), (11, 1), (131, 1), (3761, 1), (8093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
    · exact prime_3761
    · exact prime_8093
  · decide +kernel

theorem prime_263692571419 : Nat.Prime 263692571419 := by
  apply nodeValid_prime [2, 3, 16111, 303097] ⟨263692571419, 2, [(2, 1), (3, 3), (16111, 1), (303097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16111
    · exact prime_303097
  · decide +kernel

theorem prime_263692571833 : Nat.Prime 263692571833 := by
  apply nodeValid_prime [2, 3, 53, 6563, 10529] ⟨263692571833, 5, [(2, 3), (3, 2), (53, 1), (6563, 1), (10529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_6563
    · exact prime_10529
  · decide +kernel

theorem prime_263692596967 : Nat.Prime 263692596967 := by
  apply nodeValid_prime [2, 3, 43948766161] ⟨263692596967, 3, [(2, 1), (3, 1), (43948766161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43948766161
  · decide +kernel

theorem prime_264220881137 : Nat.Prime 264220881137 := by
  apply nodeValid_prime [2, 16513805071] ⟨264220881137, 3, [(2, 4), (16513805071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16513805071
  · decide +kernel

theorem prime_264220883447 : Nat.Prime 264220883447 := by
  apply nodeValid_prime [2, 13, 37, 274657883] ⟨264220883447, 5, [(2, 1), (13, 1), (37, 1), (274657883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_274657883
  · decide +kernel

theorem prime_264220928507 : Nat.Prime 264220928507 := by
  apply nodeValid_prime [2, 97, 347, 1753, 2239] ⟨264220928507, 2, [(2, 1), (97, 1), (347, 1), (1753, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_347
    · exact prime_1753
    · exact prime_2239
  · decide +kernel

theorem prime_264749983063 : Nat.Prime 264749983063 := by
  apply nodeValid_prime [2, 3, 132527, 332951] ⟨264749983063, 5, [(2, 1), (3, 1), (132527, 1), (332951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132527
    · exact prime_332951
  · decide +kernel

theorem prime_264750000719 : Nat.Prime 264750000719 := by
  apply nodeValid_prime [2, 7, 17, 1112394961] ⟨264750000719, 7, [(2, 1), (7, 1), (17, 1), (1112394961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1112394961
  · decide +kernel

theorem prime_264750000989 : Nat.Prime 264750000989 := by
  apply nodeValid_prime [2, 11, 14447, 416491] ⟨264750000989, 2, [(2, 2), (11, 1), (14447, 1), (416491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_14447
    · exact prime_416491
  · decide +kernel

theorem prime_265279748413 : Nat.Prime 265279748413 := by
  apply nodeValid_prime [2, 3, 7, 487, 1321, 4909] ⟨265279748413, 2, [(2, 2), (3, 1), (7, 1), (487, 1), (1321, 1), (4909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_487
    · exact prime_1321
    · exact prime_4909
  · decide +kernel

theorem prime_265279748971 : Nat.Prime 265279748971 := by
  apply nodeValid_prime [2, 3, 5, 8842658299] ⟨265279748971, 12, [(2, 1), (3, 1), (5, 1), (8842658299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8842658299
  · decide +kernel

theorem prime_265279758061 : Nat.Prime 265279758061 := by
  apply nodeValid_prime [2, 3, 5, 347, 12741583] ⟨265279758061, 11, [(2, 2), (3, 1), (5, 1), (347, 1), (12741583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_347
    · exact prime_12741583
  · decide +kernel

theorem prime_265810251671 : Nat.Prime 265810251671 := by
  apply nodeValid_prime [2, 5, 41, 79, 101, 193, 421] ⟨265810251671, 19, [(2, 1), (5, 1), (41, 1), (79, 1), (101, 1), (193, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_79
    · exact prime_101
    · exact prime_193
    · exact prime_421
  · decide +kernel

theorem prime_265810281853 : Nat.Prime 265810281853 := by
  apply nodeValid_prime [2, 3, 29, 9349, 81701] ⟨265810281853, 2, [(2, 2), (3, 1), (29, 1), (9349, 1), (81701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_9349
    · exact prime_81701
  · decide +kernel

theorem prime_265810282489 : Nat.Prime 265810282489 := by
  apply nodeValid_prime [2, 3, 3691809479] ⟨265810282489, 7, [(2, 3), (3, 2), (3691809479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3691809479
  · decide +kernel

theorem prime_266341458107 : Nat.Prime 266341458107 := by
  apply nodeValid_prime [2, 133170729053] ⟨266341458107, 2, [(2, 1), (133170729053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_133170729053
  · decide +kernel

theorem prime_266341470463 : Nat.Prime 266341470463 := by
  apply nodeValid_prime [2, 3, 73, 101, 239, 311] ⟨266341470463, 3, [(2, 1), (3, 5), (73, 1), (101, 1), (239, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_101
    · exact prime_239
    · exact prime_311
  · decide +kernel

theorem prime_266341470523 : Nat.Prime 266341470523 := by
  apply nodeValid_prime [2, 3, 196477, 225931] ⟨266341470523, 2, [(2, 1), (3, 1), (196477, 1), (225931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_196477
    · exact prime_225931
  · decide +kernel

theorem prime_266873366231 : Nat.Prime 266873366231 := by
  apply nodeValid_prime [2, 5, 29, 920252987] ⟨266873366231, 17, [(2, 1), (5, 1), (29, 1), (920252987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_920252987
  · decide +kernel

theorem prime_266873368301 : Nat.Prime 266873368301 := by
  apply nodeValid_prime [2, 5, 7, 11, 151, 229529] ⟨266873368301, 2, [(2, 2), (5, 2), (7, 1), (11, 1), (151, 1), (229529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_151
    · exact prime_229529
  · decide +kernel

theorem prime_266873379427 : Nat.Prime 266873379427 := by
  apply nodeValid_prime [2, 3, 4942099619] ⟨266873379427, 3, [(2, 1), (3, 3), (4942099619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4942099619
  · decide +kernel

theorem prime_267405999643 : Nat.Prime 267405999643 := by
  apply nodeValid_prime [2, 3, 14855888869] ⟨267405999643, 5, [(2, 1), (3, 2), (14855888869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14855888869
  · decide +kernel

theorem prime_267406000753 : Nat.Prime 267406000753 := by
  apply nodeValid_prime [2, 3, 11, 467, 1084477] ⟨267406000753, 5, [(2, 4), (3, 1), (11, 1), (467, 1), (1084477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_467
    · exact prime_1084477
  · decide +kernel

theorem prime_267406023011 : Nat.Prime 267406023011 := by
  apply nodeValid_prime [2, 5, 7, 3820086043] ⟨267406023011, 2, [(2, 1), (5, 1), (7, 1), (3820086043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3820086043
  · decide +kernel

theorem prime_267939385741 : Nat.Prime 267939385741 := by
  apply nodeValid_prime [2, 3, 5, 13, 37, 1019, 3037] ⟨267939385741, 6, [(2, 2), (3, 2), (5, 1), (13, 1), (37, 1), (1019, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_1019
    · exact prime_3037
  · decide +kernel

theorem prime_267939448891 : Nat.Prime 267939448891 := by
  apply nodeValid_prime [2, 3, 5, 8931314963] ⟨267939448891, 3, [(2, 1), (3, 1), (5, 1), (8931314963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8931314963
  · decide +kernel

theorem prime_268473471239 : Nat.Prime 268473471239 := by
  apply nodeValid_prime [2, 7, 137, 2447, 57203] ⟨268473471239, 7, [(2, 1), (7, 1), (137, 1), (2447, 1), (57203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_2447
    · exact prime_57203
  · decide +kernel

theorem prime_268473480983 : Nat.Prime 268473480983 := by
  apply nodeValid_prime [2, 7, 17443, 1099391] ⟨268473480983, 5, [(2, 1), (7, 1), (17443, 1), (1099391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17443
    · exact prime_1099391
  · decide +kernel

theorem prime_268473482159 : Nat.Prime 268473482159 := by
  apply nodeValid_prime [2, 7, 17, 2113, 533857] ⟨268473482159, 11, [(2, 1), (7, 1), (17, 1), (2113, 1), (533857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_2113
    · exact prime_533857
  · decide +kernel

theorem prime_269008277621 : Nat.Prime 269008277621 := by
  apply nodeValid_prime [2, 5, 1627, 8267003] ⟨269008277621, 2, [(2, 2), (5, 1), (1627, 1), (8267003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1627
    · exact prime_8267003
  · decide +kernel

theorem prime_269008292719 : Nat.Prime 269008292719 := by
  apply nodeValid_prime [2, 3, 11, 1063, 1278107] ⟨269008292719, 3, [(2, 1), (3, 2), (11, 1), (1063, 1), (1278107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1063
    · exact prime_1278107
  · decide +kernel

theorem prime_269008292989 : Nat.Prime 269008292989 := by
  apply nodeValid_prime [2, 3, 7472452583] ⟨269008292989, 6, [(2, 2), (3, 2), (7472452583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7472452583
  · decide +kernel

theorem prime_269543798891 : Nat.Prime 269543798891 := by
  apply nodeValid_prime [2, 5, 89, 1213, 249677] ⟨269543798891, 2, [(2, 1), (5, 1), (89, 1), (1213, 1), (249677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_1213
    · exact prime_249677
  · decide +kernel

theorem prime_269543800297 : Nat.Prime 269543800297 := by
  apply nodeValid_prime [2, 3, 43, 87061951] ⟨269543800297, 5, [(2, 3), (3, 2), (43, 1), (87061951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_87061951
  · decide +kernel

theorem prime_269543805857 : Nat.Prime 269543805857 := by
  apply nodeValid_prime [2, 13, 953, 679897] ⟨269543805857, 3, [(2, 5), (13, 1), (953, 1), (679897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_953
    · exact prime_679897
  · decide +kernel

theorem prime_270080016043 : Nat.Prime 270080016043 := by
  apply nodeValid_prime [2, 3, 31, 1452043097] ⟨270080016043, 2, [(2, 1), (3, 1), (31, 1), (1452043097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1452043097
  · decide +kernel

theorem prime_270080016901 : Nat.Prime 270080016901 := by
  apply nodeValid_prime [2, 3, 5, 71, 12679813] ⟨270080016901, 11, [(2, 2), (3, 1), (5, 2), (71, 1), (12679813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_12679813
  · decide +kernel

theorem prime_270080052673 : Nat.Prime 270080052673 := by
  apply nodeValid_prime [2, 3, 10799, 130259] ⟨270080052673, 11, [(2, 6), (3, 1), (10799, 1), (130259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10799
    · exact prime_130259
  · decide +kernel

theorem prime_270617011909 : Nat.Prime 270617011909 := by
  apply nodeValid_prime [2, 3, 47, 479817397] ⟨270617011909, 2, [(2, 2), (3, 1), (47, 1), (479817397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_479817397
  · decide +kernel

theorem prime_270617012879 : Nat.Prime 270617012879 := by
  apply nodeValid_prime [2, 1423, 95086793] ⟨270617012879, 11, [(2, 1), (1423, 1), (95086793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1423
    · exact prime_95086793
  · decide +kernel

theorem prime_270617019713 : Nat.Prime 270617019713 := by
  apply nodeValid_prime [2, 13, 53, 6136997] ⟨270617019713, 3, [(2, 6), (13, 1), (53, 1), (6136997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_6136997
  · decide +kernel

theorem prime_271154707073 : Nat.Prime 271154707073 := by
  apply nodeValid_prime [2, 6959, 304411] ⟨271154707073, 3, [(2, 7), (6959, 1), (304411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6959
    · exact prime_304411
  · decide +kernel

theorem prime_271154711501 : Nat.Prime 271154711501 := by
  apply nodeValid_prime [2, 5, 1733, 312931] ⟨271154711501, 2, [(2, 2), (5, 3), (1733, 1), (312931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1733
    · exact prime_312931
  · decide +kernel

theorem prime_271693127729 : Nat.Prime 271693127729 := by
  apply nodeValid_prime [2, 11, 24907, 61979] ⟨271693127729, 3, [(2, 4), (11, 1), (24907, 1), (61979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_24907
    · exact prime_61979
  · decide +kernel

theorem prime_271693129321 : Nat.Prime 271693129321 := by
  apply nodeValid_prime [2, 3, 5, 223, 3384319] ⟨271693129321, 14, [(2, 3), (3, 2), (5, 1), (223, 1), (3384319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
    · exact prime_3384319
  · decide +kernel

theorem prime_271693130609 : Nat.Prime 271693130609 := by
  apply nodeValid_prime [2, 37, 79, 331, 17551] ⟨271693130609, 3, [(2, 4), (37, 1), (79, 1), (331, 1), (17551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_79
    · exact prime_331
    · exact prime_17551
  · decide +kernel

end Sude.Lucas.Generated
