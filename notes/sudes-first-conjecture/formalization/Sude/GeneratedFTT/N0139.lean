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
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0126
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0135

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10333 : Nat.Prime 10333 := by
  apply nodeValid_prime [2, 3, 7, 41] ⟨10333, 5, [(2, 2), (3, 2), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_11783 : Nat.Prime 11783 := by
  apply nodeValid_prime [2, 43, 137] ⟨11783, 5, [(2, 1), (43, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_137
  · decide +kernel

theorem prime_17291 : Nat.Prime 17291 := by
  apply nodeValid_prime [2, 5, 7, 13, 19] ⟨17291, 6, [(2, 1), (5, 1), (7, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_17333 : Nat.Prime 17333 := by
  apply nodeValid_prime [2, 7, 619] ⟨17333, 2, [(2, 2), (7, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_619
  · decide +kernel

theorem prime_18089 : Nat.Prime 18089 := by
  apply nodeValid_prime [2, 7, 17, 19] ⟨18089, 3, [(2, 3), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_19427 : Nat.Prime 19427 := by
  apply nodeValid_prime [2, 11, 883] ⟨19427, 2, [(2, 1), (11, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_883
  · decide +kernel

theorem prime_19447 : Nat.Prime 19447 := by
  apply nodeValid_prime [2, 3, 7, 463] ⟨19447, 3, [(2, 1), (3, 1), (7, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_463
  · decide +kernel

theorem prime_22669 : Nat.Prime 22669 := by
  apply nodeValid_prime [2, 3, 1889] ⟨22669, 2, [(2, 2), (3, 1), (1889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1889
  · decide +kernel

theorem prime_23993 : Nat.Prime 23993 := by
  apply nodeValid_prime [2, 2999] ⟨23993, 3, [(2, 3), (2999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2999
  · decide +kernel

theorem prime_29863 : Nat.Prime 29863 := by
  apply nodeValid_prime [2, 3, 7, 79] ⟨29863, 10, [(2, 1), (3, 3), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_41333 : Nat.Prime 41333 := by
  apply nodeValid_prime [2, 10333] ⟨41333, 2, [(2, 2), (10333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10333
  · decide +kernel

theorem prime_43003 : Nat.Prime 43003 := by
  apply nodeValid_prime [2, 3, 2389] ⟨43003, 5, [(2, 1), (3, 2), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2389
  · decide +kernel

theorem prime_44953 : Nat.Prime 44953 := by
  apply nodeValid_prime [2, 3, 1873] ⟨44953, 5, [(2, 3), (3, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1873
  · decide +kernel

theorem prime_51199 : Nat.Prime 51199 := by
  apply nodeValid_prime [2, 3, 7, 23, 53] ⟨51199, 12, [(2, 1), (3, 1), (7, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_53831 : Nat.Prime 53831 := by
  apply nodeValid_prime [2, 5, 7, 769] ⟨53831, 7, [(2, 1), (5, 1), (7, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_769
  · decide +kernel

theorem prime_59107 : Nat.Prime 59107 := by
  apply nodeValid_prime [2, 3, 9851] ⟨59107, 2, [(2, 1), (3, 1), (9851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9851
  · decide +kernel

theorem prime_67057 : Nat.Prime 67057 := by
  apply nodeValid_prime [2, 3, 11, 127] ⟨67057, 5, [(2, 4), (3, 1), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_76963 : Nat.Prime 76963 := by
  apply nodeValid_prime [2, 3, 101, 127] ⟨76963, 3, [(2, 1), (3, 1), (101, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_127
  · decide +kernel

theorem prime_87959 : Nat.Prime 87959 := by
  apply nodeValid_prime [2, 13, 17, 199] ⟨87959, 7, [(2, 1), (13, 1), (17, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_199
  · decide +kernel

theorem prime_94349 : Nat.Prime 94349 := by
  apply nodeValid_prime [2, 103, 229] ⟨94349, 2, [(2, 2), (103, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_229
  · decide +kernel

theorem prime_103969 : Nat.Prime 103969 := by
  apply nodeValid_prime [2, 3, 19] ⟨103969, 7, [(2, 5), (3, 2), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_131231 : Nat.Prime 131231 := by
  apply nodeValid_prime [2, 5, 11, 1193] ⟨131231, 7, [(2, 1), (5, 1), (11, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1193
  · decide +kernel

theorem prime_143197 : Nat.Prime 143197 := by
  apply nodeValid_prime [2, 3, 11933] ⟨143197, 2, [(2, 2), (3, 1), (11933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11933
  · decide +kernel

theorem prime_147709 : Nat.Prime 147709 := by
  apply nodeValid_prime [2, 3, 11, 373] ⟨147709, 2, [(2, 2), (3, 2), (11, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_373
  · decide +kernel

theorem prime_157037 : Nat.Prime 157037 := by
  apply nodeValid_prime [2, 11, 43, 83] ⟨157037, 2, [(2, 2), (11, 1), (43, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_83
  · decide +kernel

theorem prime_179813 : Nat.Prime 179813 := by
  apply nodeValid_prime [2, 44953] ⟨179813, 2, [(2, 2), (44953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44953
  · decide +kernel

theorem prime_183307 : Nat.Prime 183307 := by
  apply nodeValid_prime [2, 3, 137, 223] ⟨183307, 2, [(2, 1), (3, 1), (137, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_223
  · decide +kernel

theorem prime_224303 : Nat.Prime 224303 := by
  apply nodeValid_prime [2, 13, 8627] ⟨224303, 5, [(2, 1), (13, 1), (8627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8627
  · decide +kernel

theorem prime_309493 : Nat.Prime 309493 := by
  apply nodeValid_prime [2, 3, 8597] ⟨309493, 2, [(2, 2), (3, 2), (8597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8597
  · decide +kernel

theorem prime_327823 : Nat.Prime 327823 := by
  apply nodeValid_prime [2, 3, 11, 4967] ⟨327823, 11, [(2, 1), (3, 1), (11, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4967
  · decide +kernel

theorem prime_335719 : Nat.Prime 335719 := by
  apply nodeValid_prime [2, 3, 6217] ⟨335719, 3, [(2, 1), (3, 3), (6217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6217
  · decide +kernel

theorem prime_353333 : Nat.Prime 353333 := by
  apply nodeValid_prime [2, 7, 12619] ⟨353333, 2, [(2, 2), (7, 1), (12619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12619
  · decide +kernel

theorem prime_417311 : Nat.Prime 417311 := by
  apply nodeValid_prime [2, 5, 29, 1439] ⟨417311, 11, [(2, 1), (5, 1), (29, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_1439
  · decide +kernel

theorem prime_430649 : Nat.Prime 430649 := by
  apply nodeValid_prime [2, 53831] ⟨430649, 3, [(2, 3), (53831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53831
  · decide +kernel

theorem prime_451069 : Nat.Prime 451069 := by
  apply nodeValid_prime [2, 3, 37589] ⟨451069, 2, [(2, 2), (3, 1), (37589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37589
  · decide +kernel

theorem prime_575717 : Nat.Prime 575717 := by
  apply nodeValid_prime [2, 163, 883] ⟨575717, 2, [(2, 2), (163, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_883
  · decide +kernel

theorem prime_712321 : Nat.Prime 712321 := by
  apply nodeValid_prime [2, 3, 5, 7, 53] ⟨712321, 59, [(2, 7), (3, 1), (5, 1), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_791411 : Nat.Prime 791411 := by
  apply nodeValid_prime [2, 5, 29, 2729] ⟨791411, 2, [(2, 1), (5, 1), (29, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_2729
  · decide +kernel

theorem prime_861299 : Nat.Prime 861299 := by
  apply nodeValid_prime [2, 430649] ⟨861299, 2, [(2, 1), (430649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_430649
  · decide +kernel

theorem prime_893653 : Nat.Prime 893653 := by
  apply nodeValid_prime [2, 3, 74471] ⟨893653, 2, [(2, 2), (3, 1), (74471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74471
  · decide +kernel

theorem prime_972427 : Nat.Prime 972427 := by
  apply nodeValid_prime [2, 3, 7, 13, 137] ⟨972427, 3, [(2, 1), (3, 1), (7, 1), (13, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_137
  · decide +kernel

theorem prime_1136557 : Nat.Prime 1136557 := by
  apply nodeValid_prime [2, 3, 131, 241] ⟨1136557, 2, [(2, 2), (3, 2), (131, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_241
  · decide +kernel

theorem prime_1291909 : Nat.Prime 1291909 := by
  apply nodeValid_prime [2, 3, 199, 541] ⟨1291909, 2, [(2, 2), (3, 1), (199, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_541
  · decide +kernel

theorem prime_1320799 : Nat.Prime 1320799 := by
  apply nodeValid_prime [2, 3, 17, 23, 563] ⟨1320799, 3, [(2, 1), (3, 1), (17, 1), (23, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_563
  · decide +kernel

theorem prime_1359209 : Nat.Prime 1359209 := by
  apply nodeValid_prime [2, 23, 83, 89] ⟨1359209, 3, [(2, 3), (23, 1), (83, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_83
    · exact prime_89
  · decide +kernel

theorem prime_1535971 : Nat.Prime 1535971 := by
  apply nodeValid_prime [2, 3, 5, 51199] ⟨1535971, 10, [(2, 1), (3, 1), (5, 1), (51199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_51199
  · decide +kernel

theorem prime_1579421 : Nat.Prime 1579421 := by
  apply nodeValid_prime [2, 5, 157, 503] ⟨1579421, 2, [(2, 2), (5, 1), (157, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_503
  · decide +kernel

theorem prime_1722599 : Nat.Prime 1722599 := by
  apply nodeValid_prime [2, 861299] ⟨1722599, 7, [(2, 1), (861299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_861299
  · decide +kernel

theorem prime_2362229 : Nat.Prime 2362229 := by
  apply nodeValid_prime [2, 11, 37, 1451] ⟨2362229, 2, [(2, 2), (11, 1), (37, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_1451
  · decide +kernel

theorem prime_2369467 : Nat.Prime 2369467 := by
  apply nodeValid_prime [2, 3, 11, 3989] ⟨2369467, 2, [(2, 1), (3, 3), (11, 1), (3989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3989
  · decide +kernel

theorem prime_3227743 : Nat.Prime 3227743 := by
  apply nodeValid_prime [2, 3, 7, 8539] ⟨3227743, 3, [(2, 1), (3, 3), (7, 1), (8539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8539
  · decide +kernel

theorem prime_3454303 : Nat.Prime 3454303 := by
  apply nodeValid_prime [2, 3, 575717] ⟨3454303, 3, [(2, 1), (3, 1), (575717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_575717
  · decide +kernel

theorem prime_4239997 : Nat.Prime 4239997 := by
  apply nodeValid_prime [2, 3, 353333] ⟨4239997, 5, [(2, 2), (3, 1), (353333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353333
  · decide +kernel

theorem prime_4546229 : Nat.Prime 4546229 := by
  apply nodeValid_prime [2, 1136557] ⟨4546229, 2, [(2, 2), (1136557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1136557
  · decide +kernel

theorem prime_4876429 : Nat.Prime 4876429 := by
  apply nodeValid_prime [2, 3, 251, 1619] ⟨4876429, 2, [(2, 2), (3, 1), (251, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_1619
  · decide +kernel

theorem prime_5433157 : Nat.Prime 5433157 := by
  apply nodeValid_prime [2, 3, 41, 409] ⟨5433157, 2, [(2, 2), (3, 4), (41, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_409
  · decide +kernel

theorem prime_5614327 : Nat.Prime 5614327 := by
  apply nodeValid_prime [2, 3, 103969] ⟨5614327, 3, [(2, 1), (3, 3), (103969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103969
  · decide +kernel

theorem prime_6321013 : Nat.Prime 6321013 := by
  apply nodeValid_prime [2, 3, 131, 4021] ⟨6321013, 2, [(2, 2), (3, 1), (131, 1), (4021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_4021
  · decide +kernel

theorem prime_9658133 : Nat.Prime 9658133 := by
  apply nodeValid_prime [2, 11, 219503] ⟨9658133, 2, [(2, 2), (11, 1), (219503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_219503
  · decide +kernel

theorem prime_9744599 : Nat.Prime 9744599 := by
  apply nodeValid_prime [2, 977, 4987] ⟨9744599, 7, [(2, 1), (977, 1), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_977
    · exact prime_4987
  · decide +kernel

theorem prime_11636117 : Nat.Prime 11636117 := by
  apply nodeValid_prime [2, 61, 103, 463] ⟨11636117, 2, [(2, 2), (61, 1), (103, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_103
    · exact prime_463
  · decide +kernel

theorem prime_12047753 : Nat.Prime 12047753 := by
  apply nodeValid_prime [2, 89, 16921] ⟨12047753, 3, [(2, 3), (89, 1), (16921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_16921
  · decide +kernel

theorem prime_12926077 : Nat.Prime 12926077 := by
  apply nodeValid_prime [2, 3, 239, 4507] ⟨12926077, 2, [(2, 2), (3, 1), (239, 1), (4507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_4507
  · decide +kernel

theorem prime_18897833 : Nat.Prime 18897833 := by
  apply nodeValid_prime [2, 2362229] ⟨18897833, 3, [(2, 3), (2362229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2362229
  · decide +kernel

theorem prime_19028927 : Nat.Prime 19028927 := by
  apply nodeValid_prime [2, 7, 1359209] ⟨19028927, 7, [(2, 1), (7, 1), (1359209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1359209
  · decide +kernel

theorem prime_21999727 : Nat.Prime 21999727 := by
  apply nodeValid_prime [2, 3, 7, 24943] ⟨21999727, 3, [(2, 1), (3, 2), (7, 2), (24943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_24943
  · decide +kernel

theorem prime_23039449 : Nat.Prime 23039449 := by
  apply nodeValid_prime [2, 3, 31, 173, 179] ⟨23039449, 14, [(2, 3), (3, 1), (31, 1), (173, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_173
    · exact prime_179
  · decide +kernel

theorem prime_24029141 : Nat.Prime 24029141 := by
  apply nodeValid_prime [2, 5, 53, 22669] ⟨24029141, 2, [(2, 2), (5, 1), (53, 1), (22669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_22669
  · decide +kernel

theorem prime_24544189 : Nat.Prime 24544189 := by
  apply nodeValid_prime [2, 3, 31, 7331] ⟨24544189, 2, [(2, 2), (3, 3), (31, 1), (7331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_7331
  · decide +kernel

theorem prime_25284053 : Nat.Prime 25284053 := by
  apply nodeValid_prime [2, 6321013] ⟨25284053, 2, [(2, 2), (6321013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6321013
  · decide +kernel

theorem prime_28421999 : Nat.Prime 28421999 := by
  apply nodeValid_prime [2, 11, 1291909] ⟨28421999, 7, [(2, 1), (11, 1), (1291909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1291909
  · decide +kernel

theorem prime_38772439 : Nat.Prime 38772439 := by
  apply nodeValid_prime [2, 3, 2281, 2833] ⟨38772439, 3, [(2, 1), (3, 1), (2281, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2281
    · exact prime_2833
  · decide +kernel

theorem prime_44233817 : Nat.Prime 44233817 := by
  apply nodeValid_prime [2, 11, 29, 17333] ⟨44233817, 3, [(2, 3), (11, 1), (29, 1), (17333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_17333
  · decide +kernel

theorem prime_44544931 : Nat.Prime 44544931 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 4597] ⟨44544931, 13, [(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (4597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_4597
  · decide +kernel

theorem prime_50568107 : Nat.Prime 50568107 := by
  apply nodeValid_prime [2, 25284053] ⟨50568107, 2, [(2, 1), (25284053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25284053
  · decide +kernel

theorem prime_61384121 : Nat.Prime 61384121 := by
  apply nodeValid_prime [2, 5, 7, 211, 1039] ⟨61384121, 3, [(2, 3), (5, 1), (7, 1), (211, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_211
    · exact prime_1039
  · decide +kernel

theorem prime_68374771 : Nat.Prime 68374771 := by
  apply nodeValid_prime [2, 3, 5, 53, 43003] ⟨68374771, 2, [(2, 1), (3, 1), (5, 1), (53, 1), (43003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_43003
  · decide +kernel

theorem prime_75516293 : Nat.Prime 75516293 := by
  apply nodeValid_prime [2, 61, 309493] ⟨75516293, 2, [(2, 2), (61, 1), (309493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_309493
  · decide +kernel

theorem prime_87998909 : Nat.Prime 87998909 := by
  apply nodeValid_prime [2, 21999727] ⟨87998909, 2, [(2, 2), (21999727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21999727
  · decide +kernel

theorem prime_100976933 : Nat.Prime 100976933 := by
  apply nodeValid_prime [2, 7, 41, 87959] ⟨100976933, 2, [(2, 2), (7, 1), (41, 1), (87959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_87959
  · decide +kernel

theorem prime_104764801 : Nat.Prime 104764801 := by
  apply nodeValid_prime [2, 3, 5, 7, 1559] ⟨104764801, 26, [(2, 7), (3, 1), (5, 2), (7, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1559
  · decide +kernel

theorem prime_120293689 : Nat.Prime 120293689 := by
  apply nodeValid_prime [2, 3, 1249, 4013] ⟨120293689, 7, [(2, 3), (3, 1), (1249, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1249
    · exact prime_4013
  · decide +kernel

theorem prime_154175207 : Nat.Prime 154175207 := by
  apply nodeValid_prime [2, 127, 179, 3391] ⟨154175207, 5, [(2, 1), (127, 1), (179, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_179
    · exact prime_3391
  · decide +kernel

theorem prime_201953867 : Nat.Prime 201953867 := by
  apply nodeValid_prime [2, 100976933] ⟨201953867, 2, [(2, 1), (100976933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_100976933
  · decide +kernel

theorem prime_310887271 : Nat.Prime 310887271 := by
  apply nodeValid_prime [2, 3, 5, 3454303] ⟨310887271, 13, [(2, 1), (3, 2), (5, 1), (3454303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3454303
  · decide +kernel

theorem prime_472846043 : Nat.Prime 472846043 := by
  apply nodeValid_prime [2, 179, 1320799] ⟨472846043, 2, [(2, 1), (179, 1), (1320799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_1320799
  · decide +kernel

theorem prime_729735023 : Nat.Prime 729735023 := by
  apply nodeValid_prime [2, 6173, 59107] ⟨729735023, 5, [(2, 1), (6173, 1), (59107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6173
    · exact prime_59107
  · decide +kernel

theorem prime_906195517 : Nat.Prime 906195517 := by
  apply nodeValid_prime [2, 3, 75516293] ⟨906195517, 5, [(2, 2), (3, 1), (75516293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75516293
  · decide +kernel

theorem prime_1257177613 : Nat.Prime 1257177613 := by
  apply nodeValid_prime [2, 3, 104764801] ⟨1257177613, 2, [(2, 2), (3, 1), (104764801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_104764801
  · decide +kernel

theorem prime_1790563079 : Nat.Prime 1790563079 := by
  apply nodeValid_prime [2, 19, 2423, 19447] ⟨1790563079, 7, [(2, 1), (19, 1), (2423, 1), (19447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2423
    · exact prime_19447
  · decide +kernel

theorem prime_1865323627 : Nat.Prime 1865323627 := by
  apply nodeValid_prime [2, 3, 310887271] ⟨1865323627, 2, [(2, 1), (3, 1), (310887271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_310887271
  · decide +kernel

theorem prime_1985906749 : Nat.Prime 1985906749 := by
  apply nodeValid_prime [2, 3, 7, 17, 31, 113, 397] ⟨1985906749, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (31, 1), (113, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_113
    · exact prime_397
  · decide +kernel

theorem prime_2332596599 : Nat.Prime 2332596599 := by
  apply nodeValid_prime [2, 19, 61384121] ⟨2332596599, 7, [(2, 1), (19, 1), (61384121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61384121
  · decide +kernel

theorem prime_2635461827 : Nat.Prime 2635461827 := by
  apply nodeValid_prime [2, 29, 37, 857, 1433] ⟨2635461827, 2, [(2, 1), (29, 1), (37, 1), (857, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_857
    · exact prime_1433
  · decide +kernel

theorem prime_3523615549 : Nat.Prime 3523615549 := by
  apply nodeValid_prime [2, 3, 23, 71, 179813] ⟨3523615549, 6, [(2, 2), (3, 1), (23, 1), (71, 1), (179813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_71
    · exact prime_179813
  · decide +kernel

theorem prime_3624782069 : Nat.Prime 3624782069 := by
  apply nodeValid_prime [2, 906195517] ⟨3624782069, 2, [(2, 2), (906195517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_906195517
  · decide +kernel

theorem prime_4784924783 : Nat.Prime 4784924783 := by
  apply nodeValid_prime [2, 11, 14293, 15217] ⟨4784924783, 5, [(2, 1), (11, 1), (14293, 1), (15217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_14293
    · exact prime_15217
  · decide +kernel

theorem prime_5919356171 : Nat.Prime 5919356171 := by
  apply nodeValid_prime [2, 5, 7, 13, 29, 224303] ⟨5919356171, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (29, 1), (224303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_224303
  · decide +kernel

theorem prime_7364870767 : Nat.Prime 7364870767 := by
  apply nodeValid_prime [2, 3, 11, 47, 791411] ⟨7364870767, 3, [(2, 1), (3, 2), (11, 1), (47, 1), (791411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_791411
  · decide +kernel

theorem prime_17513640553 : Nat.Prime 17513640553 := by
  apply nodeValid_prime [2, 3, 729735023] ⟨17513640553, 7, [(2, 3), (3, 1), (729735023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_729735023
  · decide +kernel

theorem prime_18592694893 : Nat.Prime 18592694893 := by
  apply nodeValid_prime [2, 3, 53, 9744599] ⟨18592694893, 5, [(2, 2), (3, 2), (53, 1), (9744599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_9744599
  · decide +kernel

theorem prime_19338081491 : Nat.Prime 19338081491 := by
  apply nodeValid_prime [2, 5, 7, 13, 1229, 17291] ⟨19338081491, 6, [(2, 1), (5, 1), (7, 1), (13, 1), (1229, 1), (17291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_1229
    · exact prime_17291
  · decide +kernel

theorem prime_37376413183 : Nat.Prime 37376413183 := by
  apply nodeValid_prime [2, 3, 127, 157, 223, 467] ⟨37376413183, 3, [(2, 1), (3, 2), (127, 1), (157, 1), (223, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_157
    · exact prime_223
    · exact prime_467
  · decide +kernel

theorem prime_41821238581 : Nat.Prime 41821238581 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 139, 23993] ⟨41821238581, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (139, 1), (23993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_139
    · exact prime_23993
  · decide +kernel

theorem prime_64955583559 : Nat.Prime 64955583559 := by
  apply nodeValid_prime [2, 3, 3583, 335719] ⟨64955583559, 6, [(2, 1), (3, 3), (3583, 1), (335719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3583
    · exact prime_335719
  · decide +kernel

theorem prime_124576268603 : Nat.Prime 124576268603 := by
  apply nodeValid_prime [2, 53, 101, 11636117] ⟨124576268603, 2, [(2, 1), (53, 1), (101, 1), (11636117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_101
    · exact prime_11636117
  · decide +kernel

theorem prime_288860311237 : Nat.Prime 288860311237 := by
  apply nodeValid_prime [2, 3, 7, 31, 751, 147709] ⟨288860311237, 5, [(2, 2), (3, 1), (7, 1), (31, 1), (751, 1), (147709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_751
    · exact prime_147709
  · decide +kernel

theorem prime_434198004703 : Nat.Prime 434198004703 := by
  apply nodeValid_prime [2, 3, 7, 11, 2083, 41017] ⟨434198004703, 11, [(2, 1), (3, 1), (7, 1), (11, 2), (2083, 1), (41017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_2083
    · exact prime_41017
  · decide +kernel

theorem prime_498999298907 : Nat.Prime 498999298907 := by
  apply nodeValid_prime [2, 37, 947, 1097, 6491] ⟨498999298907, 2, [(2, 1), (37, 1), (947, 1), (1097, 1), (6491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_947
    · exact prime_1097
    · exact prime_6491
  · decide +kernel

theorem prime_576512289271 : Nat.Prime 576512289271 := by
  apply nodeValid_prime [2, 3, 5, 131, 5433157] ⟨576512289271, 3, [(2, 1), (3, 4), (5, 1), (131, 1), (5433157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_5433157
  · decide +kernel

theorem prime_1733161879123 : Nat.Prime 1733161879123 := by
  apply nodeValid_prime [2, 3, 2969, 5273, 18451] ⟨1733161879123, 2, [(2, 1), (3, 1), (2969, 1), (5273, 1), (18451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2969
    · exact prime_5273
    · exact prime_18451
  · decide +kernel

theorem prime_1734371358199 : Nat.Prime 1734371358199 := by
  apply nodeValid_prime [2, 3, 107, 3023, 893653] ⟨1734371358199, 3, [(2, 1), (3, 1), (107, 1), (3023, 1), (893653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_3023
    · exact prime_893653
  · decide +kernel

theorem prime_1738003218673 : Nat.Prime 1738003218673 := by
  apply nodeValid_prime [2, 3, 7, 43, 120293689] ⟨1738003218673, 5, [(2, 4), (3, 1), (7, 1), (43, 1), (120293689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_120293689
  · decide +kernel

theorem prime_3500293137221 : Nat.Prime 3500293137221 := by
  apply nodeValid_prime [2, 5, 11, 23, 53, 97, 239, 563] ⟨3500293137221, 7, [(2, 2), (5, 1), (11, 1), (23, 1), (53, 1), (97, 1), (239, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_53
    · exact prime_97
    · exact prime_239
    · exact prime_563
  · decide +kernel

theorem prime_6913318654691 : Nat.Prime 6913318654691 := by
  apply nodeValid_prime [2, 5, 7, 47, 281, 631, 1693] ⟨6913318654691, 2, [(2, 1), (5, 1), (7, 2), (47, 1), (281, 1), (631, 1), (1693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_281
    · exact prime_631
    · exact prime_1693
  · decide +kernel

theorem prime_6913318655059 : Nat.Prime 6913318655059 := by
  apply nodeValid_prime [2, 3, 19, 3209, 18897833] ⟨6913318655059, 2, [(2, 1), (3, 1), (19, 1), (3209, 1), (18897833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3209
    · exact prime_18897833
  · decide +kernel

theorem prime_6913318743553 : Nat.Prime 6913318743553 := by
  apply nodeValid_prime [2, 3, 13, 11783, 29383] ⟨6913318743553, 5, [(2, 9), (3, 1), (13, 1), (11783, 1), (29383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_11783
    · exact prime_29383
  · decide +kernel

theorem prime_6918147471013 : Nat.Prime 6918147471013 := by
  apply nodeValid_prime [2, 3, 17, 31, 37, 193, 307, 499] ⟨6918147471013, 2, [(2, 2), (3, 1), (17, 1), (31, 1), (37, 1), (193, 1), (307, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_37
    · exact prime_193
    · exact prime_307
    · exact prime_499
  · decide +kernel

theorem prime_6918147471253 : Nat.Prime 6918147471253 := by
  apply nodeValid_prime [2, 3, 576512289271] ⟨6918147471253, 2, [(2, 2), (3, 1), (576512289271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_576512289271
  · decide +kernel

theorem prime_6918147509027 : Nat.Prime 6918147509027 := by
  apply nodeValid_prime [2, 13, 11549, 23039449] ⟨6918147509027, 2, [(2, 1), (13, 1), (11549, 1), (23039449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_11549
    · exact prime_23039449
  · decide +kernel

theorem prime_6922978519421 : Nat.Prime 6922978519421 := by
  apply nodeValid_prime [2, 5, 41, 547, 757, 20389] ⟨6922978519421, 2, [(2, 2), (5, 1), (41, 1), (547, 1), (757, 1), (20389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_547
    · exact prime_757
    · exact prime_20389
  · decide +kernel

theorem prime_6922978520981 : Nat.Prime 6922978520981 := by
  apply nodeValid_prime [2, 5, 47, 7364870767] ⟨6922978520981, 2, [(2, 2), (5, 1), (47, 1), (7364870767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_7364870767
  · decide +kernel

theorem prime_6922978560761 : Nat.Prime 6922978560761 := by
  apply nodeValid_prime [2, 5, 857, 201953867] ⟨6922978560761, 11, [(2, 3), (5, 1), (857, 1), (201953867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_857
    · exact prime_201953867
  · decide +kernel

theorem prime_6927811899031 : Nat.Prime 6927811899031 := by
  apply nodeValid_prime [2, 3, 5, 11, 2332596599] ⟨6927811899031, 6, [(2, 1), (3, 3), (5, 1), (11, 1), (2332596599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2332596599
  · decide +kernel

theorem prime_6927811950679 : Nat.Prime 6927811950679 := by
  apply nodeValid_prime [2, 3, 619, 1865323627] ⟨6927811950679, 3, [(2, 1), (3, 1), (619, 1), (1865323627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
    · exact prime_1865323627
  · decide +kernel

theorem prime_6927811950907 : Nat.Prime 6927811950907 := by
  apply nodeValid_prime [2, 3, 7, 11, 113, 44233817] ⟨6927811950907, 11, [(2, 1), (3, 2), (7, 1), (11, 1), (113, 1), (44233817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_113
    · exact prime_44233817
  · decide +kernel

theorem prime_6932647469689 : Nat.Prime 6932647469689 := by
  apply nodeValid_prime [2, 3, 288860311237] ⟨6932647469689, 13, [(2, 3), (3, 1), (288860311237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_288860311237
  · decide +kernel

theorem prime_6932647469911 : Nat.Prime 6932647469911 := by
  apply nodeValid_prime [2, 3, 5, 59, 163, 24029141] ⟨6932647469911, 3, [(2, 1), (3, 1), (5, 1), (59, 1), (163, 1), (24029141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_163
    · exact prime_24029141
  · decide +kernel

theorem prime_6932647516493 : Nat.Prime 6932647516493 := by
  apply nodeValid_prime [2, 1733161879123] ⟨6932647516493, 2, [(2, 2), (1733161879123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1733161879123
  · decide +kernel

theorem prime_6937485424763 : Nat.Prime 6937485424763 := by
  apply nodeValid_prime [2, 229, 33581, 451069] ⟨6937485424763, 2, [(2, 1), (229, 1), (33581, 1), (451069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_33581
    · exact prime_451069
  · decide +kernel

theorem prime_6937485432413 : Nat.Prime 6937485432413 := by
  apply nodeValid_prime [2, 293, 5919356171] ⟨6937485432413, 2, [(2, 2), (293, 1), (5919356171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_5919356171
  · decide +kernel

theorem prime_6937485432797 : Nat.Prime 6937485432797 := by
  apply nodeValid_prime [2, 1734371358199] ⟨6937485432797, 2, [(2, 2), (1734371358199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1734371358199
  · decide +kernel

theorem prime_6942325603327 : Nat.Prime 6942325603327 := by
  apply nodeValid_prime [2, 3, 2447, 472846043] ⟨6942325603327, 3, [(2, 1), (3, 1), (2447, 1), (472846043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2447
    · exact prime_472846043
  · decide +kernel

theorem prime_6942325604447 : Nat.Prime 6942325604447 := by
  apply nodeValid_prime [2, 83, 41821238581] ⟨6942325604447, 5, [(2, 1), (83, 1), (41821238581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_41821238581
  · decide +kernel

theorem prime_6942325615993 : Nat.Prime 6942325615993 := by
  apply nodeValid_prime [2, 3, 13, 73, 647, 157037] ⟨6942325615993, 5, [(2, 3), (3, 2), (13, 1), (73, 1), (647, 1), (157037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_647
    · exact prime_157037
  · decide +kernel

theorem prime_6947168075143 : Nat.Prime 6947168075143 := by
  apply nodeValid_prime [2, 3, 29863, 38772439] ⟨6947168075143, 5, [(2, 1), (3, 1), (29863, 1), (38772439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29863
    · exact prime_38772439
  · decide +kernel

theorem prime_6947168075249 : Nat.Prime 6947168075249 := by
  apply nodeValid_prime [2, 434198004703] ⟨6947168075249, 3, [(2, 4), (434198004703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_434198004703
  · decide +kernel

theorem prime_6947168091191 : Nat.Prime 6947168091191 := by
  apply nodeValid_prime [2, 5, 31, 53, 131, 3227743] ⟨6947168091191, 11, [(2, 1), (5, 1), (31, 1), (53, 1), (131, 1), (3227743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_53
    · exact prime_131
    · exact prime_3227743
  · decide +kernel

theorem prime_6952012852039 : Nat.Prime 6952012852039 := by
  apply nodeValid_prime [2, 3, 31, 37376413183] ⟨6952012852039, 3, [(2, 1), (3, 1), (31, 1), (37376413183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_37376413183
  · decide +kernel

theorem prime_6952012873073 : Nat.Prime 6952012873073 := by
  apply nodeValid_prime [2, 23, 19427, 972427] ⟨6952012873073, 3, [(2, 4), (23, 1), (19427, 1), (972427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_19427
    · exact prime_972427
  · decide +kernel

theorem prime_6952012874693 : Nat.Prime 6952012874693 := by
  apply nodeValid_prime [2, 1738003218673] ⟨6952012874693, 2, [(2, 2), (1738003218673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1738003218673
  · decide +kernel

theorem prime_6956859877691 : Nat.Prime 6956859877691 := by
  apply nodeValid_prime [2, 5, 47, 3491, 4239997] ⟨6956859877691, 2, [(2, 1), (5, 1), (47, 1), (3491, 1), (4239997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_3491
    · exact prime_4239997
  · decide +kernel

theorem prime_6956859880331 : Nat.Prime 6956859880331 := by
  apply nodeValid_prime [2, 5, 23, 2003, 2677, 5641] ⟨6956859880331, 6, [(2, 1), (5, 1), (23, 1), (2003, 1), (2677, 1), (5641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_2003
    · exact prime_2677
    · exact prime_5641
  · decide +kernel

theorem prime_6956859904271 : Nat.Prime 6956859904271 := by
  apply nodeValid_prime [2, 5, 179, 797, 4876429] ⟨6956859904271, 7, [(2, 1), (5, 1), (179, 1), (797, 1), (4876429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_797
    · exact prime_4876429
  · decide +kernel

theorem prime_6961709251153 : Nat.Prime 6961709251153 := by
  apply nodeValid_prime [2, 3, 1790563079] ⟨6961709251153, 5, [(2, 4), (3, 5), (1790563079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1790563079
  · decide +kernel

theorem prime_6961709336731 : Nat.Prime 6961709336731 := by
  apply nodeValid_prime [2, 3, 5, 41333, 5614327] ⟨6961709336731, 17, [(2, 1), (3, 1), (5, 1), (41333, 1), (5614327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41333
    · exact prime_5614327
  · decide +kernel

theorem prime_6961709336761 : Nat.Prime 6961709336761 := by
  apply nodeValid_prime [2, 3, 5, 19338081491] ⟨6961709336761, 31, [(2, 3), (3, 2), (5, 1), (19338081491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19338081491
  · decide +kernel

theorem prime_6966560875493 : Nat.Prime 6966560875493 := by
  apply nodeValid_prime [2, 877, 1985906749] ⟨6966560875493, 2, [(2, 2), (877, 1), (1985906749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_877
    · exact prime_1985906749
  · decide +kernel

theorem prime_6966560903459 : Nat.Prime 6966560903459 := by
  apply nodeValid_prime [2, 13, 19, 1091, 12926077] ⟨6966560903459, 2, [(2, 1), (13, 1), (19, 1), (1091, 1), (12926077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_1091
    · exact prime_12926077
  · decide +kernel

theorem prime_6966560903503 : Nat.Prime 6966560903503 := by
  apply nodeValid_prime [2, 3, 17, 443, 154175207] ⟨6966560903503, 3, [(2, 1), (3, 1), (17, 1), (443, 1), (154175207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_443
    · exact prime_154175207
  · decide +kernel

theorem prime_6971414776549 : Nat.Prime 6971414776549 := by
  apply nodeValid_prime [2, 3, 43, 94349, 143197] ⟨6971414776549, 2, [(2, 2), (3, 1), (43, 1), (94349, 1), (143197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_94349
    · exact prime_143197
  · decide +kernel

theorem prime_6971414858593 : Nat.Prime 6971414858593 := by
  apply nodeValid_prime [2, 3, 17, 43, 757, 131231] ⟨6971414858593, 5, [(2, 5), (3, 1), (17, 1), (43, 1), (757, 1), (131231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_757
    · exact prime_131231
  · decide +kernel

theorem prime_6971414860051 : Nat.Prime 6971414860051 := by
  apply nodeValid_prime [2, 3, 5, 10223, 4546229] ⟨6971414860051, 2, [(2, 1), (3, 1), (5, 2), (10223, 1), (4546229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10223
    · exact prime_4546229
  · decide +kernel

theorem prime_6976270968581 : Nat.Prime 6976270968581 := by
  apply nodeValid_prime [2, 5, 269, 821, 1579421] ⟨6976270968581, 2, [(2, 2), (5, 1), (269, 1), (821, 1), (1579421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_821
    · exact prime_1579421
  · decide +kernel

theorem prime_6976271041769 : Nat.Prime 6976271041769 := by
  apply nodeValid_prime [2, 7, 124576268603] ⟨6976271041769, 3, [(2, 3), (7, 1), (124576268603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_124576268603
  · decide +kernel

theorem prime_6976271043179 : Nat.Prime 6976271043179 := by
  apply nodeValid_prime [2, 183307, 19028927] ⟨6976271043179, 2, [(2, 1), (183307, 1), (19028927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_183307
    · exact prime_19028927
  · decide +kernel

theorem prime_6981129443779 : Nat.Prime 6981129443779 := by
  apply nodeValid_prime [2, 3, 7, 19, 173, 50568107] ⟨6981129443779, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (173, 1), (50568107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_173
    · exact prime_50568107
  · decide +kernel

theorem prime_6981129444061 : Nat.Prime 6981129444061 := by
  apply nodeValid_prime [2, 3, 5, 17, 79, 1583, 2027] ⟨6981129444061, 2, [(2, 2), (3, 4), (5, 1), (17, 1), (79, 1), (1583, 1), (2027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_79
    · exact prime_1583
    · exact prime_2027
  · decide +kernel

theorem prime_6981129448789 : Nat.Prime 6981129448789 := by
  apply nodeValid_prime [2, 3, 11, 601, 87998909] ⟨6981129448789, 2, [(2, 2), (3, 1), (11, 1), (601, 1), (87998909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_601
    · exact prime_87998909
  · decide +kernel

theorem prime_6985990183181 : Nat.Prime 6985990183181 := by
  apply nodeValid_prime [2, 5, 73, 4784924783] ⟨6985990183181, 3, [(2, 2), (5, 1), (73, 1), (4784924783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_4784924783
  · decide +kernel

theorem prime_6985990184699 : Nat.Prime 6985990184699 := by
  apply nodeValid_prime [2, 7, 498999298907] ⟨6985990184699, 6, [(2, 1), (7, 1), (498999298907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_498999298907
  · decide +kernel

theorem prime_6985990222177 : Nat.Prime 6985990222177 := by
  apply nodeValid_prime [2, 3, 7, 19, 23, 31, 15661] ⟨6985990222177, 10, [(2, 5), (3, 1), (7, 3), (19, 1), (23, 1), (31, 1), (15661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_31
    · exact prime_15661
  · decide +kernel

theorem prime_6990853249217 : Nat.Prime 6990853249217 := by
  apply nodeValid_prime [2, 31, 3523615549] ⟨6990853249217, 3, [(2, 6), (31, 1), (3523615549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3523615549
  · decide +kernel

theorem prime_6990853251287 : Nat.Prime 6990853251287 := by
  apply nodeValid_prime [2, 47, 6173, 12047753] ⟨6990853251287, 5, [(2, 1), (47, 1), (6173, 1), (12047753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_6173
    · exact prime_12047753
  · decide +kernel

theorem prime_6990853279769 : Nat.Prime 6990853279769 := by
  apply nodeValid_prime [2, 47, 18592694893] ⟨6990853279769, 3, [(2, 3), (47, 1), (18592694893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_18592694893
  · decide +kernel

theorem prime_6995718627349 : Nat.Prime 6995718627349 := by
  apply nodeValid_prime [2, 3, 11, 22367, 2369467] ⟨6995718627349, 10, [(2, 2), (3, 1), (11, 1), (22367, 1), (2369467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_22367
    · exact prime_2369467
  · decide +kernel

theorem prime_6995718976067 : Nat.Prime 6995718976067 := by
  apply nodeValid_prime [2, 337, 397, 1741, 15017] ⟨6995718976067, 2, [(2, 1), (337, 1), (397, 1), (1741, 1), (15017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_397
    · exact prime_1741
    · exact prime_15017
  · decide +kernel

theorem prime_6995718976423 : Nat.Prime 6995718976423 := by
  apply nodeValid_prime [2, 3, 11, 17, 67, 223, 417311] ⟨6995718976423, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (67, 1), (223, 1), (417311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_67
    · exact prime_223
    · exact prime_417311
  · decide +kernel

theorem prime_7000586242123 : Nat.Prime 7000586242123 := by
  apply nodeValid_prime [2, 3, 11, 107, 14783, 67057] ⟨7000586242123, 2, [(2, 1), (3, 1), (11, 1), (107, 1), (14783, 1), (67057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_107
    · exact prime_14783
    · exact prime_67057
  · decide +kernel

theorem prime_7000586274443 : Nat.Prime 7000586274443 := by
  apply nodeValid_prime [2, 3500293137221] ⟨7000586274443, 2, [(2, 1), (3500293137221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3500293137221
  · decide +kernel

theorem prime_7005456213031 : Nat.Prime 7005456213031 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 271, 1535971] ⟨7005456213031, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (17, 1), (271, 1), (1535971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_271
    · exact prime_1535971
  · decide +kernel

theorem prime_7005456215491 : Nat.Prime 7005456215491 := by
  apply nodeValid_prime [2, 3, 5, 327823, 712321] ⟨7005456215491, 2, [(2, 1), (3, 1), (5, 1), (327823, 1), (712321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_327823
    · exact prime_712321
  · decide +kernel

theorem prime_7005456221201 : Nat.Prime 7005456221201 := by
  apply nodeValid_prime [2, 5, 17513640553] ⟨7005456221201, 3, [(2, 4), (5, 2), (17513640553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17513640553
  · decide +kernel

theorem prime_7010328459821 : Nat.Prime 7010328459821 := by
  apply nodeValid_prime [2, 5, 7, 19, 2635461827] ⟨7010328459821, 2, [(2, 2), (5, 1), (7, 1), (19, 1), (2635461827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_2635461827
  · decide +kernel

theorem prime_7010328521089 : Nat.Prime 7010328521089 := by
  apply nodeValid_prime [2, 3, 89, 68374771] ⟨7010328521089, 7, [(2, 7), (3, 2), (89, 1), (68374771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_68374771
  · decide +kernel

theorem prime_7010328521447 : Nat.Prime 7010328521447 := by
  apply nodeValid_prime [2, 967, 3624782069] ⟨7010328521447, 5, [(2, 1), (967, 1), (3624782069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_967
    · exact prime_3624782069
  · decide +kernel

theorem prime_7015203003467 : Nat.Prime 7015203003467 := by
  apply nodeValid_prime [2, 7, 1607, 44544931] ⟨7015203003467, 2, [(2, 1), (7, 2), (1607, 1), (44544931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1607
    · exact prime_44544931
  · decide +kernel

theorem prime_7015203024373 : Nat.Prime 7015203024373 := by
  apply nodeValid_prime [2, 3, 64955583559] ⟨7015203024373, 2, [(2, 2), (3, 3), (64955583559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_64955583559
  · decide +kernel

theorem prime_7015203024721 : Nat.Prime 7015203024721 := by
  apply nodeValid_prime [2, 3, 5, 11, 673, 1549, 2549] ⟨7015203024721, 7, [(2, 4), (3, 1), (5, 1), (11, 1), (673, 1), (1549, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_673
    · exact prime_1549
    · exact prime_2549
  · decide +kernel

theorem prime_7020079790993 : Nat.Prime 7020079790993 := by
  apply nodeValid_prime [2, 349, 1257177613] ⟨7020079790993, 3, [(2, 4), (349, 1), (1257177613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_349
    · exact prime_1257177613
  · decide +kernel

theorem prime_7020079791113 : Nat.Prime 7020079791113 := by
  apply nodeValid_prime [2, 131, 347, 547, 35291] ⟨7020079791113, 3, [(2, 3), (131, 1), (347, 1), (547, 1), (35291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_347
    · exact prime_547
    · exact prime_35291
  · decide +kernel

theorem prime_7020079849403 : Nat.Prime 7020079849403 := by
  apply nodeValid_prime [2, 83, 1723, 24544189] ⟨7020079849403, 2, [(2, 1), (83, 1), (1723, 1), (24544189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_1723
    · exact prime_24544189
  · decide +kernel

theorem prime_7024958935147 : Nat.Prime 7024958935147 := by
  apply nodeValid_prime [2, 3, 17, 2377, 9658133] ⟨7024958935147, 2, [(2, 1), (3, 2), (17, 1), (2377, 1), (9658133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2377
    · exact prime_9658133
  · decide +kernel

theorem prime_7024958935619 : Nat.Prime 7024958935619 := by
  apply nodeValid_prime [2, 13, 19, 877, 3617, 4483] ⟨7024958935619, 2, [(2, 1), (13, 1), (19, 1), (877, 1), (3617, 1), (4483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_877
    · exact prime_3617
    · exact prime_4483
  · decide +kernel

theorem prime_7024958985523 : Nat.Prime 7024958985523 := by
  apply nodeValid_prime [2, 3, 29, 18089, 76963] ⟨7024958985523, 2, [(2, 1), (3, 1), (29, 2), (18089, 1), (76963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_18089
    · exact prime_76963
  · decide +kernel

theorem prime_7029840388663 : Nat.Prime 7029840388663 := by
  apply nodeValid_prime [2, 3, 7, 13, 151, 28421999] ⟨7029840388663, 3, [(2, 1), (3, 2), (7, 1), (13, 1), (151, 1), (28421999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_151
    · exact prime_28421999
  · decide +kernel

theorem prime_7029840389051 : Nat.Prime 7029840389051 := by
  apply nodeValid_prime [2, 5, 81619, 1722599] ⟨7029840389051, 2, [(2, 1), (5, 2), (81619, 1), (1722599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_81619
    · exact prime_1722599
  · decide +kernel

theorem prime_7029840409817 : Nat.Prime 7029840409817 := by
  apply nodeValid_prime [2, 7, 311, 947, 426233] ⟨7029840409817, 3, [(2, 3), (7, 1), (311, 1), (947, 1), (426233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_311
    · exact prime_947
    · exact prime_426233
  · decide +kernel

end Sude.Lucas.Generated
