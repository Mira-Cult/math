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
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0094

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9013 : Nat.Prime 9013 := by
  apply nodeValid_prime [2, 3, 751] ⟨9013, 5, [(2, 2), (3, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_751
  · decide +kernel

theorem prime_10069 : Nat.Prime 10069 := by
  apply nodeValid_prime [2, 3, 839] ⟨10069, 2, [(2, 2), (3, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_839
  · decide +kernel

theorem prime_13577 : Nat.Prime 13577 := by
  apply nodeValid_prime [2, 1697] ⟨13577, 3, [(2, 3), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1697
  · decide +kernel

theorem prime_14867 : Nat.Prime 14867 := by
  apply nodeValid_prime [2, 7433] ⟨14867, 2, [(2, 1), (7433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7433
  · decide +kernel

theorem prime_20347 : Nat.Prime 20347 := by
  apply nodeValid_prime [2, 3, 3391] ⟨20347, 3, [(2, 1), (3, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3391
  · decide +kernel

theorem prime_25013 : Nat.Prime 25013 := by
  apply nodeValid_prime [2, 13, 37] ⟨25013, 2, [(2, 2), (13, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_26107 : Nat.Prime 26107 := by
  apply nodeValid_prime [2, 3, 19, 229] ⟨26107, 2, [(2, 1), (3, 1), (19, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_229
  · decide +kernel

theorem prime_26633 : Nat.Prime 26633 := by
  apply nodeValid_prime [2, 3329] ⟨26633, 3, [(2, 3), (3329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3329
  · decide +kernel

theorem prime_31069 : Nat.Prime 31069 := by
  apply nodeValid_prime [2, 3, 863] ⟨31069, 2, [(2, 2), (3, 2), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863
  · decide +kernel

theorem prime_36013 : Nat.Prime 36013 := by
  apply nodeValid_prime [2, 3, 3001] ⟨36013, 2, [(2, 2), (3, 1), (3001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3001
  · decide +kernel

theorem prime_37003 : Nat.Prime 37003 := by
  apply nodeValid_prime [2, 3, 7, 881] ⟨37003, 2, [(2, 1), (3, 1), (7, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_881
  · decide +kernel

theorem prime_38611 : Nat.Prime 38611 := by
  apply nodeValid_prime [2, 3, 5, 11, 13] ⟨38611, 3, [(2, 1), (3, 3), (5, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_43913 : Nat.Prime 43913 := by
  apply nodeValid_prime [2, 11, 499] ⟨43913, 3, [(2, 3), (11, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_499
  · decide +kernel

theorem prime_50021 : Nat.Prime 50021 := by
  apply nodeValid_prime [2, 5, 41, 61] ⟨50021, 2, [(2, 2), (5, 1), (41, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_61
  · decide +kernel

theorem prime_58391 : Nat.Prime 58391 := by
  apply nodeValid_prime [2, 5, 5839] ⟨58391, 11, [(2, 1), (5, 1), (5839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5839
  · decide +kernel

theorem prime_58687 : Nat.Prime 58687 := by
  apply nodeValid_prime [2, 3, 9781] ⟨58687, 6, [(2, 1), (3, 1), (9781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9781
  · decide +kernel

theorem prime_62273 : Nat.Prime 62273 := by
  apply nodeValid_prime [2, 7, 139] ⟨62273, 3, [(2, 6), (7, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_62497 : Nat.Prime 62497 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨62497, 10, [(2, 5), (3, 2), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_68491 : Nat.Prime 68491 := by
  apply nodeValid_prime [2, 3, 5, 761] ⟨68491, 10, [(2, 1), (3, 2), (5, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_761
  · decide +kernel

theorem prime_69779 : Nat.Prime 69779 := by
  apply nodeValid_prime [2, 139, 251] ⟨69779, 2, [(2, 1), (139, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_251
  · decide +kernel

theorem prime_74197 : Nat.Prime 74197 := by
  apply nodeValid_prime [2, 3, 229] ⟨74197, 5, [(2, 2), (3, 4), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
  · decide +kernel

theorem prime_82499 : Nat.Prime 82499 := by
  apply nodeValid_prime [2, 13, 19, 167] ⟨82499, 6, [(2, 1), (13, 1), (19, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_167
  · decide +kernel

theorem prime_97879 : Nat.Prime 97879 := by
  apply nodeValid_prime [2, 3, 11, 1483] ⟨97879, 6, [(2, 1), (3, 1), (11, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1483
  · decide +kernel

theorem prime_109751 : Nat.Prime 109751 := by
  apply nodeValid_prime [2, 5, 439] ⟨109751, 11, [(2, 1), (5, 3), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_134291 : Nat.Prime 134291 := by
  apply nodeValid_prime [2, 5, 13, 1033] ⟨134291, 2, [(2, 1), (5, 1), (13, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1033
  · decide +kernel

theorem prime_150767 : Nat.Prime 150767 := by
  apply nodeValid_prime [2, 7, 11, 89] ⟨150767, 5, [(2, 1), (7, 1), (11, 2), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_159293 : Nat.Prime 159293 := by
  apply nodeValid_prime [2, 7, 5689] ⟨159293, 2, [(2, 2), (7, 1), (5689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5689
  · decide +kernel

theorem prime_161377 : Nat.Prime 161377 := by
  apply nodeValid_prime [2, 3, 41] ⟨161377, 5, [(2, 5), (3, 1), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_164999 : Nat.Prime 164999 := by
  apply nodeValid_prime [2, 82499] ⟨164999, 7, [(2, 1), (82499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82499
  · decide +kernel

theorem prime_204461 : Nat.Prime 204461 := by
  apply nodeValid_prime [2, 5, 10223] ⟨204461, 3, [(2, 2), (5, 1), (10223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10223
  · decide +kernel

theorem prime_211693 : Nat.Prime 211693 := by
  apply nodeValid_prime [2, 3, 13, 23, 59] ⟨211693, 2, [(2, 2), (3, 1), (13, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_219503 : Nat.Prime 219503 := by
  apply nodeValid_prime [2, 109751] ⟨219503, 5, [(2, 1), (109751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_109751
  · decide +kernel

theorem prime_225077 : Nat.Prime 225077 := by
  apply nodeValid_prime [2, 56269] ⟨225077, 2, [(2, 2), (56269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56269
  · decide +kernel

theorem prime_235441 : Nat.Prime 235441 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨235441, 11, [(2, 4), (3, 3), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_266009 : Nat.Prime 266009 := by
  apply nodeValid_prime [2, 41, 811] ⟨266009, 3, [(2, 3), (41, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_811
  · decide +kernel

theorem prime_372829 : Nat.Prime 372829 := by
  apply nodeValid_prime [2, 3, 31069] ⟨372829, 2, [(2, 2), (3, 1), (31069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31069
  · decide +kernel

theorem prime_377183 : Nat.Prime 377183 := by
  apply nodeValid_prime [2, 13, 89, 163] ⟨377183, 5, [(2, 1), (13, 1), (89, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_89
    · exact prime_163
  · decide +kernel

theorem prime_482527 : Nat.Prime 482527 := by
  apply nodeValid_prime [2, 3, 11, 2437] ⟨482527, 3, [(2, 1), (3, 2), (11, 1), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2437
  · decide +kernel

theorem prime_505639 : Nat.Prime 505639 := by
  apply nodeValid_prime [2, 3, 7, 4013] ⟨505639, 6, [(2, 1), (3, 2), (7, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4013
  · decide +kernel

theorem prime_507029 : Nat.Prime 507029 := by
  apply nodeValid_prime [2, 126757] ⟨507029, 2, [(2, 2), (126757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_126757
  · decide +kernel

theorem prime_586871 : Nat.Prime 586871 := by
  apply nodeValid_prime [2, 5, 58687] ⟨586871, 17, [(2, 1), (5, 1), (58687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_58687
  · decide +kernel

theorem prime_593839 : Nat.Prime 593839 := by
  apply nodeValid_prime [2, 3, 7, 1571] ⟨593839, 3, [(2, 1), (3, 3), (7, 1), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1571
  · decide +kernel

theorem prime_754301 : Nat.Prime 754301 := by
  apply nodeValid_prime [2, 5, 19, 397] ⟨754301, 2, [(2, 2), (5, 2), (19, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_397
  · decide +kernel

theorem prime_861221 : Nat.Prime 861221 := by
  apply nodeValid_prime [2, 5, 17, 149] ⟨861221, 2, [(2, 2), (5, 1), (17, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_149
  · decide +kernel

theorem prime_954461 : Nat.Prime 954461 := by
  apply nodeValid_prime [2, 5, 13, 3671] ⟨954461, 2, [(2, 2), (5, 1), (13, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_3671
  · decide +kernel

theorem prime_1064473 : Nat.Prime 1064473 := by
  apply nodeValid_prime [2, 3, 17, 2609] ⟨1064473, 10, [(2, 3), (3, 1), (17, 1), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2609
  · decide +kernel

theorem prime_1071991 : Nat.Prime 1071991 := by
  apply nodeValid_prime [2, 3, 5, 43, 277] ⟨1071991, 3, [(2, 1), (3, 2), (5, 1), (43, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_277
  · decide +kernel

theorem prime_1134667 : Nat.Prime 1134667 := by
  apply nodeValid_prime [2, 3, 13, 373] ⟨1134667, 2, [(2, 1), (3, 2), (13, 2), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_373
  · decide +kernel

theorem prime_1204337 : Nat.Prime 1204337 := by
  apply nodeValid_prime [2, 7, 10753] ⟨1204337, 3, [(2, 4), (7, 1), (10753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10753
  · decide +kernel

theorem prime_1226767 : Nat.Prime 1226767 := by
  apply nodeValid_prime [2, 3, 204461] ⟨1226767, 3, [(2, 1), (3, 1), (204461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_204461
  · decide +kernel

theorem prime_1264177 : Nat.Prime 1264177 := by
  apply nodeValid_prime [2, 3, 8779] ⟨1264177, 7, [(2, 4), (3, 2), (8779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8779
  · decide +kernel

theorem prime_1489769 : Nat.Prime 1489769 := by
  apply nodeValid_prime [2, 7, 37, 719] ⟨1489769, 3, [(2, 3), (7, 1), (37, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_719
  · decide +kernel

theorem prime_1600813 : Nat.Prime 1600813 := by
  apply nodeValid_prime [2, 3, 53, 839] ⟨1600813, 2, [(2, 2), (3, 2), (53, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_839
  · decide +kernel

theorem prime_1722443 : Nat.Prime 1722443 := by
  apply nodeValid_prime [2, 861221] ⟨1722443, 2, [(2, 1), (861221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_861221
  · decide +kernel

theorem prime_1827431 : Nat.Prime 1827431 := by
  apply nodeValid_prime [2, 5, 11, 37, 449] ⟨1827431, 7, [(2, 1), (5, 1), (11, 1), (37, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_449
  · decide +kernel

theorem prime_1915757 : Nat.Prime 1915757 := by
  apply nodeValid_prime [2, 409, 1171] ⟨1915757, 2, [(2, 2), (409, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_1171
  · decide +kernel

theorem prime_2055769 : Nat.Prime 2055769 := by
  apply nodeValid_prime [2, 3, 11, 13, 599] ⟨2055769, 29, [(2, 3), (3, 1), (11, 1), (13, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_599
  · decide +kernel

theorem prime_2069399 : Nat.Prime 2069399 := by
  apply nodeValid_prime [2, 97, 10667] ⟨2069399, 13, [(2, 1), (97, 1), (10667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_10667
  · decide +kernel

theorem prime_2420699 : Nat.Prime 2420699 := by
  apply nodeValid_prime [2, 7, 17, 1453] ⟨2420699, 6, [(2, 1), (7, 2), (17, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1453
  · decide +kernel

theorem prime_2472329 : Nat.Prime 2472329 := by
  apply nodeValid_prime [2, 43, 7187] ⟨2472329, 3, [(2, 3), (43, 1), (7187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_7187
  · decide +kernel

theorem prime_3387089 : Nat.Prime 3387089 := by
  apply nodeValid_prime [2, 211693] ⟨3387089, 3, [(2, 4), (211693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_211693
  · decide +kernel

theorem prime_4052107 : Nat.Prime 4052107 := by
  apply nodeValid_prime [2, 3, 25013] ⟨4052107, 2, [(2, 1), (3, 4), (25013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25013
  · decide +kernel

theorem prime_4240843 : Nat.Prime 4240843 := by
  apply nodeValid_prime [2, 3, 61, 11587] ⟨4240843, 3, [(2, 1), (3, 1), (61, 1), (11587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_11587
  · decide +kernel

theorem prime_4396681 : Nat.Prime 4396681 := by
  apply nodeValid_prime [2, 3, 5, 23, 59] ⟨4396681, 17, [(2, 3), (3, 4), (5, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_4841399 : Nat.Prime 4841399 := by
  apply nodeValid_prime [2, 2420699] ⟨4841399, 17, [(2, 1), (2420699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2420699
  · decide +kernel

theorem prime_4944659 : Nat.Prime 4944659 := by
  apply nodeValid_prime [2, 2472329] ⟨4944659, 2, [(2, 1), (2472329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2472329
  · decide +kernel

theorem prime_5086751 : Nat.Prime 5086751 := by
  apply nodeValid_prime [2, 5, 20347] ⟨5086751, 17, [(2, 1), (5, 3), (20347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20347
  · decide +kernel

theorem prime_5690621 : Nat.Prime 5690621 := by
  apply nodeValid_prime [2, 5, 13, 43, 509] ⟨5690621, 2, [(2, 2), (5, 1), (13, 1), (43, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_509
  · decide +kernel

theorem prime_7578037 : Nat.Prime 7578037 := by
  apply nodeValid_prime [2, 3, 19, 1231] ⟨7578037, 5, [(2, 2), (3, 4), (19, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1231
  · decide +kernel

theorem prime_8223077 : Nat.Prime 8223077 := by
  apply nodeValid_prime [2, 2055769] ⟨8223077, 2, [(2, 2), (2055769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2055769
  · decide +kernel

theorem prime_8472049 : Nat.Prime 8472049 := by
  apply nodeValid_prime [2, 3, 13, 13577] ⟨8472049, 7, [(2, 4), (3, 1), (13, 1), (13577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_13577
  · decide +kernel

theorem prime_9681983 : Nat.Prime 9681983 := by
  apply nodeValid_prime [2, 19, 31, 8219] ⟨9681983, 5, [(2, 1), (19, 1), (31, 1), (8219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_8219
  · decide +kernel

theorem prime_11593033 : Nat.Prime 11593033 := by
  apply nodeValid_prime [2, 3, 11, 43913] ⟨11593033, 35, [(2, 3), (3, 1), (11, 1), (43913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43913
  · decide +kernel

theorem prime_13064459 : Nat.Prime 13064459 := by
  apply nodeValid_prime [2, 11, 593839] ⟨13064459, 6, [(2, 1), (11, 1), (593839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_593839
  · decide +kernel

theorem prime_13162931 : Nat.Prime 13162931 := by
  apply nodeValid_prime [2, 5, 11, 17, 7039] ⟨13162931, 2, [(2, 1), (5, 1), (11, 1), (17, 1), (7039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_7039
  · decide +kernel

theorem prime_19152649 : Nat.Prime 19152649 := by
  apply nodeValid_prime [2, 3, 266009] ⟨19152649, 7, [(2, 3), (3, 2), (266009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_266009
  · decide +kernel

theorem prime_20068141 : Nat.Prime 20068141 := by
  apply nodeValid_prime [2, 3, 5, 193, 1733] ⟨20068141, 13, [(2, 2), (3, 1), (5, 1), (193, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_193
    · exact prime_1733
  · decide +kernel

theorem prime_24048151 : Nat.Prime 24048151 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 619] ⟨24048151, 12, [(2, 1), (3, 1), (5, 2), (7, 1), (37, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_619
  · decide +kernel

theorem prime_25023343 : Nat.Prime 25023343 := by
  apply nodeValid_prime [2, 3, 19, 219503] ⟨25023343, 3, [(2, 1), (3, 1), (19, 1), (219503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_219503
  · decide +kernel

theorem prime_27068683 : Nat.Prime 27068683 := by
  apply nodeValid_prime [2, 3, 37, 121931] ⟨27068683, 2, [(2, 1), (3, 1), (37, 1), (121931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_121931
  · decide +kernel

theorem prime_27317947 : Nat.Prime 27317947 := by
  apply nodeValid_prime [2, 3, 17, 223, 1201] ⟨27317947, 2, [(2, 1), (3, 1), (17, 1), (223, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_223
    · exact prime_1201
  · decide +kernel

theorem prime_30266207 : Nat.Prime 30266207 := by
  apply nodeValid_prime [2, 23, 28607] ⟨30266207, 5, [(2, 1), (23, 2), (28607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_28607
  · decide +kernel

theorem prime_47451779 : Nat.Prime 47451779 := by
  apply nodeValid_prime [2, 11, 19, 61, 1861] ⟨47451779, 2, [(2, 1), (11, 1), (19, 1), (61, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_61
    · exact prime_1861
  · decide +kernel

theorem prime_50890117 : Nat.Prime 50890117 := by
  apply nodeValid_prime [2, 3, 4240843] ⟨50890117, 2, [(2, 2), (3, 1), (4240843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4240843
  · decide +kernel

theorem prime_58835479 : Nat.Prime 58835479 := by
  apply nodeValid_prime [2, 3, 13, 754301] ⟨58835479, 6, [(2, 1), (3, 1), (13, 1), (754301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_754301
  · decide +kernel

theorem prime_59335909 : Nat.Prime 59335909 := by
  apply nodeValid_prime [2, 3, 4944659] ⟨59335909, 2, [(2, 2), (3, 1), (4944659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4944659
  · decide +kernel

theorem prime_75780371 : Nat.Prime 75780371 := by
  apply nodeValid_prime [2, 5, 7578037] ⟨75780371, 6, [(2, 1), (5, 1), (7578037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7578037
  · decide +kernel

theorem prime_97699559 : Nat.Prime 97699559 := by
  apply nodeValid_prime [2, 11, 19, 47, 4973] ⟨97699559, 11, [(2, 1), (11, 1), (19, 1), (47, 1), (4973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_47
    · exact prime_4973
  · decide +kernel

theorem prime_103404071 : Nat.Prime 103404071 := by
  apply nodeValid_prime [2, 5, 7, 11, 134291] ⟨103404071, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (134291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_134291
  · decide +kernel

theorem prime_116693659 : Nat.Prime 116693659 := by
  apply nodeValid_prime [2, 3, 43, 150767] ⟨116693659, 11, [(2, 1), (3, 2), (43, 1), (150767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_150767
  · decide +kernel

theorem prime_129747109 : Nat.Prime 129747109 := by
  apply nodeValid_prime [2, 3, 67, 161377] ⟨129747109, 2, [(2, 2), (3, 1), (67, 1), (161377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_161377
  · decide +kernel

theorem prime_142407943 : Nat.Prime 142407943 := by
  apply nodeValid_prime [2, 3, 149, 159293] ⟨142407943, 3, [(2, 1), (3, 1), (149, 1), (159293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_159293
  · decide +kernel

theorem prime_149031917 : Nat.Prime 149031917 := by
  apply nodeValid_prime [2, 11, 3387089] ⟨149031917, 2, [(2, 2), (11, 1), (3387089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3387089
  · decide +kernel

theorem prime_151274771 : Nat.Prime 151274771 := by
  apply nodeValid_prime [2, 5, 19, 101, 7883] ⟨151274771, 2, [(2, 1), (5, 1), (19, 1), (101, 1), (7883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_101
    · exact prime_7883
  · decide +kernel

theorem prime_166761253 : Nat.Prime 166761253 := by
  apply nodeValid_prime [2, 3, 7, 19, 29, 1201] ⟨166761253, 2, [(2, 2), (3, 2), (7, 1), (19, 1), (29, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_29
    · exact prime_1201
  · decide +kernel

theorem prime_181186097 : Nat.Prime 181186097 := by
  apply nodeValid_prime [2, 7, 13, 107, 1163] ⟨181186097, 3, [(2, 4), (7, 1), (13, 1), (107, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_107
    · exact prime_1163
  · decide +kernel

theorem prime_181597243 : Nat.Prime 181597243 := by
  apply nodeValid_prime [2, 3, 30266207] ⟨181597243, 3, [(2, 1), (3, 1), (30266207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30266207
  · decide +kernel

theorem prime_193296539 : Nat.Prime 193296539 := by
  apply nodeValid_prime [2, 19, 5086751] ⟨193296539, 2, [(2, 1), (19, 1), (5086751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5086751
  · decide +kernel

theorem prime_290690237 : Nat.Prime 290690237 := by
  apply nodeValid_prime [2, 83, 673, 1301] ⟨290690237, 2, [(2, 2), (83, 1), (673, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_673
    · exact prime_1301
  · decide +kernel

theorem prime_310335101 : Nat.Prime 310335101 := by
  apply nodeValid_prime [2, 5, 1231, 2521] ⟨310335101, 7, [(2, 2), (5, 2), (1231, 1), (2521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1231
    · exact prime_2521
  · decide +kernel

theorem prime_475408471 : Nat.Prime 475408471 := by
  apply nodeValid_prime [2, 3, 5, 607, 26107] ⟨475408471, 3, [(2, 1), (3, 1), (5, 1), (607, 1), (26107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_607
    · exact prime_26107
  · decide +kernel

theorem prime_947731033 : Nat.Prime 947731033 := by
  apply nodeValid_prime [2, 3, 13162931] ⟨947731033, 10, [(2, 3), (3, 2), (13162931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13162931
  · decide +kernel

theorem prime_1546372313 : Nat.Prime 1546372313 := by
  apply nodeValid_prime [2, 193296539] ⟨1546372313, 3, [(2, 3), (193296539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193296539
  · decide +kernel

theorem prime_2054659811 : Nat.Prime 2054659811 := by
  apply nodeValid_prime [2, 5, 7, 19, 109, 14173] ⟨2054659811, 6, [(2, 1), (5, 1), (7, 1), (19, 1), (109, 1), (14173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_109
    · exact prime_14173
  · decide +kernel

theorem prime_4109319623 : Nat.Prime 4109319623 := by
  apply nodeValid_prime [2, 2054659811] ⟨4109319623, 5, [(2, 1), (2054659811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2054659811
  · decide +kernel

theorem prime_5108332871 : Nat.Prime 5108332871 := by
  apply nodeValid_prime [2, 5, 4421, 115547] ⟨5108332871, 13, [(2, 1), (5, 1), (4421, 1), (115547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4421
    · exact prime_115547
  · decide +kernel

theorem prime_7121184683 : Nat.Prime 7121184683 := by
  apply nodeValid_prime [2, 433, 8223077] ⟨7121184683, 2, [(2, 1), (433, 1), (8223077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_433
    · exact prime_8223077
  · decide +kernel

theorem prime_9615917503 : Nat.Prime 9615917503 := by
  apply nodeValid_prime [2, 3, 17, 2593, 12119] ⟨9615917503, 5, [(2, 1), (3, 2), (17, 1), (2593, 1), (12119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2593
    · exact prime_12119
  · decide +kernel

theorem prime_9903443401 : Nat.Prime 9903443401 := by
  apply nodeValid_prime [2, 3, 5, 41, 1091] ⟨9903443401, 13, [(2, 3), (3, 3), (5, 2), (41, 2), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_1091
  · decide +kernel

theorem prime_11369597893 : Nat.Prime 11369597893 := by
  apply nodeValid_prime [2, 3, 17, 6379, 8737] ⟨11369597893, 2, [(2, 2), (3, 1), (17, 1), (6379, 1), (8737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_6379
    · exact prime_8737
  · decide +kernel

theorem prime_11940915527 : Nat.Prime 11940915527 := by
  apply nodeValid_prime [2, 457, 13064459] ⟨11940915527, 5, [(2, 1), (457, 1), (13064459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_13064459
  · decide +kernel

theorem prime_16160047069 : Nat.Prime 16160047069 := by
  apply nodeValid_prime [2, 3, 11, 17, 181, 3617] ⟨16160047069, 19, [(2, 2), (3, 1), (11, 2), (17, 1), (181, 1), (3617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_181
    · exact prime_3617
  · decide +kernel

theorem prime_17126618389 : Nat.Prime 17126618389 := by
  apply nodeValid_prime [2, 3, 11, 129747109] ⟨17126618389, 2, [(2, 2), (3, 1), (11, 1), (129747109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_129747109
  · decide +kernel

theorem prime_19930470671 : Nat.Prime 19930470671 := by
  apply nodeValid_prime [2, 5, 11, 181186097] ⟨19930470671, 17, [(2, 1), (5, 1), (11, 1), (181186097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_181186097
  · decide +kernel

theorem prime_20310993817 : Nat.Prime 20310993817 := by
  apply nodeValid_prime [2, 3, 73, 11593033] ⟨20310993817, 5, [(2, 3), (3, 1), (73, 1), (11593033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_11593033
  · decide +kernel

theorem prime_30834710251 : Nat.Prime 30834710251 := by
  apply nodeValid_prime [2, 3, 5, 109, 377183] ⟨30834710251, 3, [(2, 1), (3, 1), (5, 3), (109, 1), (377183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_377183
  · decide +kernel

theorem prime_34137835709 : Nat.Prime 34137835709 := by
  apply nodeValid_prime [2, 43, 157, 1264177] ⟨34137835709, 2, [(2, 2), (43, 1), (157, 1), (1264177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_157
    · exact prime_1264177
  · decide +kernel

theorem prime_45478391573 : Nat.Prime 45478391573 := by
  apply nodeValid_prime [2, 11369597893] ⟨45478391573, 2, [(2, 2), (11369597893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11369597893
  · decide +kernel

theorem prime_54620238577 : Nat.Prime 54620238577 := by
  apply nodeValid_prime [2, 3, 1069, 1064473] ⟨54620238577, 5, [(2, 4), (3, 1), (1069, 1), (1064473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
    · exact prime_1064473
  · decide +kernel

theorem prime_64752891713 : Nat.Prime 64752891713 := by
  apply nodeValid_prime [2, 16189, 62497] ⟨64752891713, 3, [(2, 6), (16189, 1), (62497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16189
    · exact prime_62497
  · decide +kernel

theorem prime_76792070351 : Nat.Prime 76792070351 := by
  apply nodeValid_prime [2, 5, 2617, 586871] ⟨76792070351, 19, [(2, 1), (5, 2), (2617, 1), (586871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2617
    · exact prime_586871
  · decide +kernel

theorem prime_90879877961 : Nat.Prime 90879877961 := by
  apply nodeValid_prime [2, 5, 4481, 507029] ⟨90879877961, 3, [(2, 3), (5, 1), (4481, 1), (507029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4481
    · exact prime_507029
  · decide +kernel

theorem prime_138406349437 : Nat.Prime 138406349437 := by
  apply nodeValid_prime [2, 3, 593, 2039, 9539] ⟨138406349437, 13, [(2, 2), (3, 1), (593, 1), (2039, 1), (9539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_593
    · exact prime_2039
    · exact prime_9539
  · decide +kernel

theorem prime_191818122347 : Nat.Prime 191818122347 := by
  apply nodeValid_prime [2, 31, 1693, 1827431] ⟨191818122347, 2, [(2, 1), (31, 1), (1693, 1), (1827431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1693
    · exact prime_1827431
  · decide +kernel

theorem prime_214936479487 : Nat.Prime 214936479487 := by
  apply nodeValid_prime [2, 3, 11940915527] ⟨214936479487, 3, [(2, 1), (3, 2), (11940915527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11940915527
  · decide +kernel

theorem prime_382988588839 : Nat.Prime 382988588839 := by
  apply nodeValid_prime [2, 3, 547, 116693659] ⟨382988588839, 3, [(2, 1), (3, 1), (547, 1), (116693659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_547
    · exact prime_116693659
  · decide +kernel

theorem prime_642097713847 : Nat.Prime 642097713847 := by
  apply nodeValid_prime [2, 3, 131, 1693, 482527] ⟨642097713847, 5, [(2, 1), (3, 1), (131, 1), (1693, 1), (482527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_1693
    · exact prime_482527
  · decide +kernel

theorem prime_956662592209 : Nat.Prime 956662592209 := by
  apply nodeValid_prime [2, 3, 19930470671] ⟨956662592209, 29, [(2, 4), (3, 1), (19930470671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19930470671
  · decide +kernel

theorem prime_972110599189 : Nat.Prime 972110599189 := by
  apply nodeValid_prime [2, 3, 1069, 75780371] ⟨972110599189, 2, [(2, 2), (3, 1), (1069, 1), (75780371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
    · exact prime_75780371
  · decide +kernel

theorem prime_1918181259569 : Nat.Prime 1918181259569 := by
  apply nodeValid_prime [2, 7, 17126618389] ⟨1918181259569, 3, [(2, 4), (7, 1), (17126618389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17126618389
  · decide +kernel

theorem prime_1923045601553 : Nat.Prime 1923045601553 := by
  apply nodeValid_prime [2, 69779, 1722443] ⟨1923045601553, 3, [(2, 4), (69779, 1), (1722443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_69779
    · exact prime_1722443
  · decide +kernel

theorem prime_1924668960341 : Nat.Prime 1924668960341 := by
  apply nodeValid_prime [2, 5, 7, 58391, 235441] ⟨1924668960341, 2, [(2, 2), (5, 1), (7, 1), (58391, 1), (235441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_58391
    · exact prime_235441
  · decide +kernel

theorem prime_3813726745547 : Nat.Prime 3813726745547 := by
  apply nodeValid_prime [2, 225077, 8472049] ⟨3813726745547, 2, [(2, 1), (225077, 1), (8472049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_225077
    · exact prime_8472049
  · decide +kernel

theorem prime_3813726754363 : Nat.Prime 3813726754363 := by
  apply nodeValid_prime [2, 3, 7, 191, 475408471] ⟨3813726754363, 2, [(2, 1), (3, 1), (7, 1), (191, 1), (475408471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_191
    · exact prime_475408471
  · decide +kernel

theorem prime_3813726756031 : Nat.Prime 3813726756031 := by
  apply nodeValid_prime [2, 3, 5, 853, 149031917] ⟨3813726756031, 6, [(2, 1), (3, 1), (5, 1), (853, 1), (149031917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_853
    · exact prime_149031917
  · decide +kernel

theorem prime_3816954874363 : Nat.Prime 3816954874363 := by
  apply nodeValid_prime [2, 3, 7, 90879877961] ⟨3816954874363, 2, [(2, 1), (3, 1), (7, 1), (90879877961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_90879877961
  · decide +kernel

theorem prime_3816954989831 : Nat.Prime 3816954989831 := by
  apply nodeValid_prime [2, 5, 59, 239, 27068683] ⟨3816954989831, 11, [(2, 1), (5, 1), (59, 1), (239, 1), (27068683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_239
    · exact prime_27068683
  · decide +kernel

theorem prime_3816954990089 : Nat.Prime 3816954990089 := by
  apply nodeValid_prime [2, 67, 7121184683] ⟨3816954990089, 3, [(2, 3), (67, 1), (7121184683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_7121184683
  · decide +kernel

theorem prime_3820184851321 : Nat.Prime 3820184851321 := by
  apply nodeValid_prime [2, 3, 5, 17, 419, 1489769] ⟨3820184851321, 14, [(2, 3), (3, 2), (5, 1), (17, 1), (419, 1), (1489769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_419
    · exact prime_1489769
  · decide +kernel

theorem prime_3820184891921 : Nat.Prime 3820184891921 := by
  apply nodeValid_prime [2, 5, 263, 487, 372829] ⟨3820184891921, 6, [(2, 4), (5, 1), (263, 1), (487, 1), (372829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
    · exact prime_487
    · exact prime_372829
  · decide +kernel

theorem prime_3820184892133 : Nat.Prime 3820184892133 := by
  apply nodeValid_prime [2, 3, 7, 45478391573] ⟨3820184892133, 6, [(2, 2), (3, 1), (7, 1), (45478391573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_45478391573
  · decide +kernel

theorem prime_3823416670343 : Nat.Prime 3823416670343 := by
  apply nodeValid_prime [2, 241, 317, 25023343] ⟨3823416670343, 5, [(2, 1), (241, 1), (317, 1), (25023343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_317
    · exact prime_25023343
  · decide +kernel

theorem prime_3823416700151 : Nat.Prime 3823416700151 := by
  apply nodeValid_prime [2, 5, 71333, 1071991] ⟨3823416700151, 11, [(2, 1), (5, 2), (71333, 1), (1071991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71333
    · exact prime_1071991
  · decide +kernel

theorem prime_3823416700391 : Nat.Prime 3823416700391 := by
  apply nodeValid_prime [2, 5, 7, 54620238577] ⟨3823416700391, 7, [(2, 1), (5, 1), (7, 1), (54620238577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_54620238577
  · decide +kernel

theorem prime_3826650339137 : Nat.Prime 3826650339137 := by
  apply nodeValid_prime [2, 43, 36013, 38611] ⟨3826650339137, 3, [(2, 6), (43, 1), (36013, 1), (38611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_36013
    · exact prime_38611
  · decide +kernel

theorem prime_3826650368837 : Nat.Prime 3826650368837 := by
  apply nodeValid_prime [2, 956662592209] ⟨3826650368837, 2, [(2, 2), (956662592209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_956662592209
  · decide +kernel

theorem prime_3826650369397 : Nat.Prime 3826650369397 := by
  apply nodeValid_prime [2, 3, 71, 45887, 97879] ⟨3826650369397, 2, [(2, 2), (3, 1), (71, 1), (45887, 1), (97879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_45887
    · exact prime_97879
  · decide +kernel

theorem prime_3829885854871 : Nat.Prime 3829885854871 := by
  apply nodeValid_prime [2, 3, 5, 19, 37, 181597243] ⟨3829885854871, 12, [(2, 1), (3, 1), (5, 1), (19, 1), (37, 1), (181597243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_37
    · exact prime_181597243
  · decide +kernel

theorem prime_3829885888391 : Nat.Prime 3829885888391 := by
  apply nodeValid_prime [2, 5, 382988588839] ⟨3829885888391, 23, [(2, 1), (5, 1), (382988588839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_382988588839
  · decide +kernel

theorem prime_3829885888637 : Nat.Prime 3829885888637 := by
  apply nodeValid_prime [2, 233, 4109319623] ⟨3829885888637, 2, [(2, 2), (233, 1), (4109319623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_4109319623
  · decide +kernel

theorem prime_3833123222783 : Nat.Prime 3833123222783 := by
  apply nodeValid_prime [2, 7, 62273, 4396681] ⟨3833123222783, 5, [(2, 1), (7, 1), (62273, 1), (4396681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_62273
    · exact prime_4396681
  · decide +kernel

theorem prime_3833123235881 : Nat.Prime 3833123235881 := by
  apply nodeValid_prime [2, 5, 50021, 1915757] ⟨3833123235881, 15, [(2, 3), (5, 1), (50021, 1), (1915757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_50021
    · exact prime_1915757
  · decide +kernel

theorem prime_3833123236573 : Nat.Prime 3833123236573 := by
  apply nodeValid_prime [2, 3, 7, 15901, 58567] ⟨3833123236573, 13, [(2, 2), (3, 1), (7, 3), (15901, 1), (58567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_15901
    · exact prime_58567
  · decide +kernel

theorem prime_3836362446941 : Nat.Prime 3836362446941 := by
  apply nodeValid_prime [2, 5, 191818122347] ⟨3836362446941, 10, [(2, 2), (5, 1), (191818122347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191818122347
  · decide +kernel

theorem prime_3836362518563 : Nat.Prime 3836362518563 := by
  apply nodeValid_prime [2, 7, 883, 310335101] ⟨3836362518563, 2, [(2, 1), (7, 1), (883, 1), (310335101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_883
    · exact prime_310335101
  · decide +kernel

theorem prime_3836362519139 : Nat.Prime 3836362519139 := by
  apply nodeValid_prime [2, 1918181259569] ⟨3836362519139, 2, [(2, 1), (1918181259569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1918181259569
  · decide +kernel

theorem prime_3839603359541 : Nat.Prime 3839603359541 := by
  apply nodeValid_prime [2, 5, 13, 251, 58835479] ⟨3839603359541, 2, [(2, 2), (5, 1), (13, 1), (251, 1), (58835479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_251
    · exact prime_58835479
  · decide +kernel

theorem prime_3839603362277 : Nat.Prime 3839603362277 := by
  apply nodeValid_prime [2, 11, 9013, 9681983] ⟨3839603362277, 2, [(2, 2), (11, 1), (9013, 1), (9681983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9013
    · exact prime_9681983
  · decide +kernel

theorem prime_3839603517551 : Nat.Prime 3839603517551 := by
  apply nodeValid_prime [2, 5, 76792070351] ⟨3839603517551, 7, [(2, 1), (5, 2), (76792070351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_76792070351
  · decide +kernel

theorem prime_3842846314133 : Nat.Prime 3842846314133 := by
  apply nodeValid_prime [2, 7, 823, 166761253] ⟨3842846314133, 2, [(2, 2), (7, 1), (823, 1), (166761253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_823
    · exact prime_166761253
  · decide +kernel

theorem prime_3842846317139 : Nat.Prime 3842846317139 := by
  apply nodeValid_prime [2, 37, 101, 7507, 68491] ⟨3842846317139, 2, [(2, 1), (37, 1), (101, 1), (7507, 1), (68491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_101
    · exact prime_7507
    · exact prime_68491
  · decide +kernel

theorem prime_3842846433499 : Nat.Prime 3842846433499 := by
  apply nodeValid_prime [2, 3, 26633, 24048151] ⟨3842846433499, 3, [(2, 1), (3, 1), (26633, 1), (24048151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26633
    · exact prime_24048151
  · decide +kernel

theorem prime_3846091199449 : Nat.Prime 3846091199449 := by
  apply nodeValid_prime [2, 3, 130631, 1226767] ⟨3846091199449, 26, [(2, 3), (3, 1), (130631, 1), (1226767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130631
    · exact prime_1226767
  · decide +kernel

theorem prime_3846091202423 : Nat.Prime 3846091202423 := by
  apply nodeValid_prime [2, 7, 17, 16160047069] ⟨3846091202423, 5, [(2, 1), (7, 1), (17, 1), (16160047069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_16160047069
  · decide +kernel

theorem prime_3846091203107 : Nat.Prime 3846091203107 := by
  apply nodeValid_prime [2, 1923045601553] ⟨3846091203107, 2, [(2, 1), (1923045601553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1923045601553
  · decide +kernel

theorem prime_3849337822867 : Nat.Prime 3849337822867 := by
  apply nodeValid_prime [2, 3, 4241, 151274771] ⟨3849337822867, 2, [(2, 1), (3, 1), (4241, 1), (151274771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4241
    · exact prime_151274771
  · decide +kernel

theorem prime_3849337920551 : Nat.Prime 3849337920551 := by
  apply nodeValid_prime [2, 5, 71, 113, 953, 10069] ⟨3849337920551, 7, [(2, 1), (5, 2), (71, 1), (113, 1), (953, 1), (10069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_113
    · exact prime_953
    · exact prime_10069
  · decide +kernel

theorem prime_3849337920683 : Nat.Prime 3849337920683 := by
  apply nodeValid_prime [2, 1924668960341] ⟨3849337920683, 2, [(2, 1), (1924668960341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1924668960341
  · decide +kernel

theorem prime_3852586283083 : Nat.Prime 3852586283083 := by
  apply nodeValid_prime [2, 3, 642097713847] ⟨3852586283083, 2, [(2, 1), (3, 1), (642097713847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_642097713847
  · decide +kernel

theorem prime_3852586283233 : Nat.Prime 3852586283233 := by
  apply nodeValid_prime [2, 3, 521, 6143, 12539] ⟨3852586283233, 5, [(2, 5), (3, 1), (521, 1), (6143, 1), (12539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_6143
    · exact prime_12539
  · decide +kernel

theorem prime_3852586305277 : Nat.Prime 3852586305277 := by
  apply nodeValid_prime [2, 3, 311, 373, 821, 3371] ⟨3852586305277, 5, [(2, 2), (3, 1), (311, 1), (373, 1), (821, 1), (3371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_373
    · exact prime_821
    · exact prime_3371
  · decide +kernel

theorem prime_3855836651963 : Nat.Prime 3855836651963 := by
  apply nodeValid_prime [2, 1204337, 1600813] ⟨3855836651963, 2, [(2, 1), (1204337, 1), (1600813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1204337
    · exact prime_1600813
  · decide +kernel

theorem prime_3855836657983 : Nat.Prime 3855836657983 := by
  apply nodeValid_prime [2, 3, 29, 467, 47451779] ⟨3855836657983, 3, [(2, 1), (3, 1), (29, 1), (467, 1), (47451779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_467
    · exact prime_47451779
  · decide +kernel

theorem prime_3855836658337 : Nat.Prime 3855836658337 := by
  apply nodeValid_prime [2, 3, 13, 1493, 2069399] ⟨3855836658337, 5, [(2, 5), (3, 1), (13, 1), (1493, 1), (2069399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1493
    · exact prime_2069399
  · decide +kernel

theorem prime_3859088825231 : Nat.Prime 3859088825231 := by
  apply nodeValid_prime [2, 5, 19, 20310993817] ⟨3859088825231, 19, [(2, 1), (5, 1), (19, 1), (20310993817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_20310993817
  · decide +kernel

theorem prime_3859088825699 : Nat.Prime 3859088825699 := by
  apply nodeValid_prime [2, 113, 3527, 4841399] ⟨3859088825699, 2, [(2, 1), (113, 1), (3527, 1), (4841399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_3527
    · exact prime_4841399
  · decide +kernel

theorem prime_3859088849543 : Nat.Prime 3859088849543 := by
  apply nodeValid_prime [2, 31, 1049, 59335909] ⟨3859088849543, 5, [(2, 1), (31, 1), (1049, 1), (59335909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1049
    · exact prime_59335909
  · decide +kernel

theorem prime_3862342909837 : Nat.Prime 3862342909837 := by
  apply nodeValid_prime [2, 3, 557, 4637, 41539] ⟨3862342909837, 5, [(2, 2), (3, 2), (557, 1), (4637, 1), (41539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
    · exact prime_4637
    · exact prime_41539
  · decide +kernel

theorem prime_3862342926391 : Nat.Prime 3862342926391 := by
  apply nodeValid_prime [2, 3, 5, 13, 9903443401] ⟨3862342926391, 23, [(2, 1), (3, 1), (5, 1), (13, 1), (9903443401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_9903443401
  · decide +kernel

theorem prime_3862342926649 : Nat.Prime 3862342926649 := by
  apply nodeValid_prime [2, 3, 17, 103, 1134667] ⟨3862342926649, 41, [(2, 3), (3, 5), (17, 1), (103, 1), (1134667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_103
    · exact prime_1134667
  · decide +kernel

theorem prime_3865598771627 : Nat.Prime 3865598771627 := by
  apply nodeValid_prime [2, 61, 109, 290690237] ⟨3865598771627, 2, [(2, 1), (61, 1), (109, 1), (290690237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_109
    · exact prime_290690237
  · decide +kernel

theorem prime_3865598772289 : Nat.Prime 3865598772289 := by
  apply nodeValid_prime [2, 3, 11, 67, 27317947] ⟨3865598772289, 17, [(2, 6), (3, 1), (11, 1), (67, 1), (27317947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67
    · exact prime_27317947
  · decide +kernel

theorem prime_3865598836207 : Nat.Prime 3865598836207 := by
  apply nodeValid_prime [2, 3, 67, 9615917503] ⟨3865598836207, 3, [(2, 1), (3, 1), (67, 1), (9615917503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_9615917503
  · decide +kernel

theorem prime_3868856623427 : Nat.Prime 3868856623427 := by
  apply nodeValid_prime [2, 17, 983, 5261, 22003] ⟨3868856623427, 2, [(2, 1), (17, 1), (983, 1), (5261, 1), (22003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_983
    · exact prime_5261
    · exact prime_22003
  · decide +kernel

theorem prime_3868856630767 : Nat.Prime 3868856630767 := by
  apply nodeValid_prime [2, 3, 214936479487] ⟨3868856630767, 5, [(2, 1), (3, 2), (214936479487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_214936479487
  · decide +kernel

theorem prime_3868856630827 : Nat.Prime 3868856630827 := by
  apply nodeValid_prime [2, 3, 11, 23, 127, 20068141] ⟨3868856630827, 2, [(2, 1), (3, 1), (11, 1), (23, 1), (127, 1), (20068141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_127
    · exact prime_20068141
  · decide +kernel

theorem prime_3872116271753 : Nat.Prime 3872116271753 := by
  apply nodeValid_prime [2, 313, 1546372313] ⟨3872116271753, 3, [(2, 3), (313, 1), (1546372313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_1546372313
  · decide +kernel

theorem prime_3872116316219 : Nat.Prime 3872116316219 := by
  apply nodeValid_prime [2, 379, 5108332871] ⟨3872116316219, 2, [(2, 1), (379, 1), (5108332871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_5108332871
  · decide +kernel

theorem prime_3872116316303 : Nat.Prime 3872116316303 := by
  apply nodeValid_prime [2, 13, 907, 2213, 74197] ⟨3872116316303, 5, [(2, 1), (13, 1), (907, 1), (2213, 1), (74197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_907
    · exact prime_2213
    · exact prime_74197
  · decide +kernel

theorem prime_3875377772527 : Nat.Prime 3875377772527 := by
  apply nodeValid_prime [2, 3, 13, 23, 29, 37, 41, 49103] ⟨3875377772527, 3, [(2, 1), (3, 1), (13, 1), (23, 1), (29, 1), (37, 1), (41, 1), (49103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_29
    · exact prime_37
    · exact prime_41
    · exact prime_49103
  · decide +kernel

theorem prime_3875377772939 : Nat.Prime 3875377772939 := by
  apply nodeValid_prime [2, 7, 2677, 103404071] ⟨3875377772939, 2, [(2, 1), (7, 1), (2677, 1), (103404071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2677
    · exact prime_103404071
  · decide +kernel

theorem prime_3875377784237 : Nat.Prime 3875377784237 := by
  apply nodeValid_prime [2, 7, 138406349437] ⟨3875377784237, 2, [(2, 2), (7, 1), (138406349437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_138406349437
  · decide +kernel

theorem prime_3878641157273 : Nat.Prime 3878641157273 := by
  apply nodeValid_prime [2, 7, 1361, 50890117] ⟨3878641157273, 6, [(2, 3), (7, 1), (1361, 1), (50890117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1361
    · exact prime_50890117
  · decide +kernel

theorem prime_3878641254289 : Nat.Prime 3878641254289 := by
  apply nodeValid_prime [2, 3, 4219, 19152649] ⟨3878641254289, 11, [(2, 4), (3, 1), (4219, 1), (19152649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4219
    · exact prime_19152649
  · decide +kernel

theorem prime_3878641256779 : Nat.Prime 3878641256779 := by
  apply nodeValid_prime [2, 3, 61, 3701, 954461] ⟨3878641256779, 2, [(2, 1), (3, 2), (61, 1), (3701, 1), (954461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_3701
    · exact prime_954461
  · decide +kernel

theorem prime_3881906311169 : Nat.Prime 3881906311169 := by
  apply nodeValid_prime [2, 947731033] ⟨3881906311169, 3, [(2, 12), (947731033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_947731033
  · decide +kernel

theorem prime_3881906393153 : Nat.Prime 3881906393153 := by
  apply nodeValid_prime [2, 43, 83, 103, 164999] ⟨3881906393153, 3, [(2, 6), (43, 1), (83, 1), (103, 1), (164999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_83
    · exact prime_103
    · exact prime_164999
  · decide +kernel

theorem prime_3885173491627 : Nat.Prime 3885173491627 := by
  apply nodeValid_prime [2, 3, 7, 30834710251] ⟨3885173491627, 2, [(2, 1), (3, 2), (7, 1), (30834710251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_30834710251
  · decide +kernel

theorem prime_3885173500927 : Nat.Prime 3885173500927 := by
  apply nodeValid_prime [2, 3, 4547, 142407943] ⟨3885173500927, 3, [(2, 1), (3, 1), (4547, 1), (142407943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4547
    · exact prime_142407943
  · decide +kernel

theorem prime_3885173502781 : Nat.Prime 3885173502781 := by
  apply nodeValid_prime [2, 3, 5, 64752891713] ⟨3885173502781, 2, [(2, 2), (3, 1), (5, 1), (64752891713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_64752891713
  · decide +kernel

theorem prime_3888442396757 : Nat.Prime 3888442396757 := by
  apply nodeValid_prime [2, 972110599189] ⟨3888442396757, 2, [(2, 2), (972110599189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_972110599189
  · decide +kernel

theorem prime_3888442398271 : Nat.Prime 3888442398271 := by
  apply nodeValid_prime [2, 3, 5, 29, 1103, 4052107] ⟨3888442398271, 3, [(2, 1), (3, 1), (5, 1), (29, 1), (1103, 1), (4052107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1103
    · exact prime_4052107
  · decide +kernel

theorem prime_3888442448201 : Nat.Prime 3888442448201 := by
  apply nodeValid_prime [2, 5, 199, 97699559] ⟨3888442448201, 3, [(2, 3), (5, 2), (199, 1), (97699559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_97699559
  · decide +kernel

theorem prime_3891713262737 : Nat.Prime 3891713262737 := by
  apply nodeValid_prime [2, 13, 37003, 505639] ⟨3891713262737, 3, [(2, 4), (13, 1), (37003, 1), (505639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37003
    · exact prime_505639
  · decide +kernel

theorem prime_3891713270723 : Nat.Prime 3891713270723 := by
  apply nodeValid_prime [2, 23, 14867, 5690621] ⟨3891713270723, 2, [(2, 1), (23, 1), (14867, 1), (5690621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_14867
    · exact prime_5690621
  · decide +kernel

theorem prime_3891713270827 : Nat.Prime 3891713270827 := by
  apply nodeValid_prime [2, 3, 19, 34137835709] ⟨3891713270827, 3, [(2, 1), (3, 1), (19, 1), (34137835709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_34137835709
  · decide +kernel

end Sude.Lucas.Generated
