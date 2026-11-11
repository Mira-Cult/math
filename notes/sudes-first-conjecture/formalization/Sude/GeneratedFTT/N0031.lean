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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
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

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2731 : Nat.Prime 2731 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨2731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_3931 : Nat.Prime 3931 := by
  apply nodeValid_prime [2, 3, 5, 131] ⟨3931, 2, [(2, 1), (3, 1), (5, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
  · decide +kernel

theorem prime_4139 : Nat.Prime 4139 := by
  apply nodeValid_prime [2, 2069] ⟨4139, 2, [(2, 1), (2069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2069
  · decide +kernel

theorem prime_4621 : Nat.Prime 4621 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨4621, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_4813 : Nat.Prime 4813 := by
  apply nodeValid_prime [2, 3, 401] ⟨4813, 2, [(2, 2), (3, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
  · decide +kernel

theorem prime_5189 : Nat.Prime 5189 := by
  apply nodeValid_prime [2, 1297] ⟨5189, 2, [(2, 2), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1297
  · decide +kernel

theorem prime_5281 : Nat.Prime 5281 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨5281, 7, [(2, 5), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_5419 : Nat.Prime 5419 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨5419, 3, [(2, 1), (3, 2), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_5653 : Nat.Prime 5653 := by
  apply nodeValid_prime [2, 3, 157] ⟨5653, 5, [(2, 2), (3, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
  · decide +kernel

theorem prime_7841 : Nat.Prime 7841 := by
  apply nodeValid_prime [2, 5, 7] ⟨7841, 12, [(2, 5), (5, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_8423 : Nat.Prime 8423 := by
  apply nodeValid_prime [2, 4211] ⟨8423, 5, [(2, 1), (4211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4211
  · decide +kernel

theorem prime_10597 : Nat.Prime 10597 := by
  apply nodeValid_prime [2, 3, 883] ⟨10597, 5, [(2, 2), (3, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_883
  · decide +kernel

theorem prime_13229 : Nat.Prime 13229 := by
  apply nodeValid_prime [2, 3307] ⟨13229, 2, [(2, 2), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3307
  · decide +kernel

theorem prime_15319 : Nat.Prime 15319 := by
  apply nodeValid_prime [2, 3, 23, 37] ⟨15319, 3, [(2, 1), (3, 2), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_15683 : Nat.Prime 15683 := by
  apply nodeValid_prime [2, 7841] ⟨15683, 2, [(2, 1), (7841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7841
  · decide +kernel

theorem prime_16811 : Nat.Prime 16811 := by
  apply nodeValid_prime [2, 5, 41] ⟨16811, 7, [(2, 1), (5, 1), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_17669 : Nat.Prime 17669 := by
  apply nodeValid_prime [2, 7, 631] ⟨17669, 2, [(2, 2), (7, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_631
  · decide +kernel

theorem prime_18223 : Nat.Prime 18223 := by
  apply nodeValid_prime [2, 3, 3037] ⟨18223, 3, [(2, 1), (3, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3037
  · decide +kernel

theorem prime_22129 : Nat.Prime 22129 := by
  apply nodeValid_prime [2, 3, 461] ⟨22129, 19, [(2, 4), (3, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
  · decide +kernel

theorem prime_23687 : Nat.Prime 23687 := by
  apply nodeValid_prime [2, 13, 911] ⟨23687, 5, [(2, 1), (13, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_911
  · decide +kernel

theorem prime_26459 : Nat.Prime 26459 := by
  apply nodeValid_prime [2, 13229] ⟨26459, 2, [(2, 1), (13229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13229
  · decide +kernel

theorem prime_28547 : Nat.Prime 28547 := by
  apply nodeValid_prime [2, 7, 2039] ⟨28547, 2, [(2, 1), (7, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2039
  · decide +kernel

theorem prime_28879 : Nat.Prime 28879 := by
  apply nodeValid_prime [2, 3, 4813] ⟨28879, 3, [(2, 1), (3, 1), (4813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4813
  · decide +kernel

theorem prime_31223 : Nat.Prime 31223 := by
  apply nodeValid_prime [2, 67, 233] ⟨31223, 5, [(2, 1), (67, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_233
  · decide +kernel

theorem prime_31231 : Nat.Prime 31231 := by
  apply nodeValid_prime [2, 3, 5, 347] ⟨31231, 6, [(2, 1), (3, 2), (5, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_347
  · decide +kernel

theorem prime_31957 : Nat.Prime 31957 := by
  apply nodeValid_prime [2, 3, 2663] ⟨31957, 2, [(2, 2), (3, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2663
  · decide +kernel

theorem prime_31981 : Nat.Prime 31981 := by
  apply nodeValid_prime [2, 3, 5, 13, 41] ⟨31981, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_33937 : Nat.Prime 33937 := by
  apply nodeValid_prime [2, 3, 7, 101] ⟨33937, 5, [(2, 4), (3, 1), (7, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
  · decide +kernel

theorem prime_39631 : Nat.Prime 39631 := by
  apply nodeValid_prime [2, 3, 5, 1321] ⟨39631, 3, [(2, 1), (3, 1), (5, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1321
  · decide +kernel

theorem prime_40283 : Nat.Prime 40283 := by
  apply nodeValid_prime [2, 11, 1831] ⟨40283, 2, [(2, 1), (11, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1831
  · decide +kernel

theorem prime_42611 : Nat.Prime 42611 := by
  apply nodeValid_prime [2, 5, 4261] ⟨42611, 2, [(2, 1), (5, 1), (4261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4261
  · decide +kernel

theorem prime_44279 : Nat.Prime 44279 := by
  apply nodeValid_prime [2, 13, 131] ⟨44279, 7, [(2, 1), (13, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_131
  · decide +kernel

theorem prime_44729 : Nat.Prime 44729 := by
  apply nodeValid_prime [2, 5591] ⟨44729, 3, [(2, 3), (5591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5591
  · decide +kernel

theorem prime_49523 : Nat.Prime 49523 := by
  apply nodeValid_prime [2, 11, 2251] ⟨49523, 2, [(2, 1), (11, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2251
  · decide +kernel

theorem prime_52237 : Nat.Prime 52237 := by
  apply nodeValid_prime [2, 3, 1451] ⟨52237, 6, [(2, 2), (3, 2), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
  · decide +kernel

theorem prime_53897 : Nat.Prime 53897 := by
  apply nodeValid_prime [2, 6737] ⟨53897, 3, [(2, 3), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6737
  · decide +kernel

theorem prime_70921 : Nat.Prime 70921 := by
  apply nodeValid_prime [2, 3, 5, 197] ⟨70921, 13, [(2, 3), (3, 2), (5, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
  · decide +kernel

theorem prime_82217 : Nat.Prime 82217 := by
  apply nodeValid_prime [2, 43, 239] ⟨82217, 3, [(2, 3), (43, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_239
  · decide +kernel

theorem prime_107867 : Nat.Prime 107867 := by
  apply nodeValid_prime [2, 11, 4903] ⟨107867, 2, [(2, 1), (11, 1), (4903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4903
  · decide +kernel

theorem prime_118219 : Nat.Prime 118219 := by
  apply nodeValid_prime [2, 3, 17, 19, 61] ⟨118219, 2, [(2, 1), (3, 1), (17, 1), (19, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_134489 : Nat.Prime 134489 := by
  apply nodeValid_prime [2, 16811] ⟨134489, 3, [(2, 3), (16811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16811
  · decide +kernel

theorem prime_137201 : Nat.Prime 137201 := by
  apply nodeValid_prime [2, 5, 7] ⟨137201, 3, [(2, 4), (5, 2), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_143461 : Nat.Prime 143461 := by
  apply nodeValid_prime [2, 3, 5, 797] ⟨143461, 10, [(2, 2), (3, 2), (5, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_797
  · decide +kernel

theorem prime_182617 : Nat.Prime 182617 := by
  apply nodeValid_prime [2, 3, 7, 1087] ⟨182617, 5, [(2, 3), (3, 1), (7, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1087
  · decide +kernel

theorem prime_189467 : Nat.Prime 189467 := by
  apply nodeValid_prime [2, 61, 1553] ⟨189467, 2, [(2, 1), (61, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_1553
  · decide +kernel

theorem prime_210923 : Nat.Prime 210923 := by
  apply nodeValid_prime [2, 163, 647] ⟨210923, 2, [(2, 1), (163, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_647
  · decide +kernel

theorem prime_213019 : Nat.Prime 213019 := by
  apply nodeValid_prime [2, 3, 13, 2731] ⟨213019, 2, [(2, 1), (3, 1), (13, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2731
  · decide +kernel

theorem prime_240257 : Nat.Prime 240257 := by
  apply nodeValid_prime [2, 1877] ⟨240257, 3, [(2, 7), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1877
  · decide +kernel

theorem prime_268979 : Nat.Prime 268979 := by
  apply nodeValid_prime [2, 134489] ⟨268979, 2, [(2, 1), (134489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_134489
  · decide +kernel

theorem prime_273311 : Nat.Prime 273311 := by
  apply nodeValid_prime [2, 5, 151, 181] ⟨273311, 11, [(2, 1), (5, 1), (151, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_181
  · decide +kernel

theorem prime_274403 : Nat.Prime 274403 := by
  apply nodeValid_prime [2, 137201] ⟨274403, 2, [(2, 1), (137201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_137201
  · decide +kernel

theorem prime_294641 : Nat.Prime 294641 := by
  apply nodeValid_prime [2, 5, 29, 127] ⟨294641, 3, [(2, 4), (5, 1), (29, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_127
  · decide +kernel

theorem prime_301219 : Nat.Prime 301219 := by
  apply nodeValid_prime [2, 3, 61, 823] ⟨301219, 2, [(2, 1), (3, 1), (61, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_823
  · decide +kernel

theorem prime_388133 : Nat.Prime 388133 := by
  apply nodeValid_prime [2, 19, 5107] ⟨388133, 2, [(2, 2), (19, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5107
  · decide +kernel

theorem prime_395803 : Nat.Prime 395803 := by
  apply nodeValid_prime [2, 3, 11, 1999] ⟨395803, 3, [(2, 1), (3, 2), (11, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1999
  · decide +kernel

theorem prime_397493 : Nat.Prime 397493 := by
  apply nodeValid_prime [2, 43, 2311] ⟨397493, 2, [(2, 2), (43, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2311
  · decide +kernel

theorem prime_470213 : Nat.Prime 470213 := by
  apply nodeValid_prime [2, 19, 23, 269] ⟨470213, 2, [(2, 2), (19, 1), (23, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_269
  · decide +kernel

theorem prime_518299 : Nat.Prime 518299 := by
  apply nodeValid_prime [2, 3, 11, 7853] ⟨518299, 2, [(2, 1), (3, 1), (11, 1), (7853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_7853
  · decide +kernel

theorem prime_730469 : Nat.Prime 730469 := by
  apply nodeValid_prime [2, 182617] ⟨730469, 2, [(2, 2), (182617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_182617
  · decide +kernel

theorem prime_844771 : Nat.Prime 844771 := by
  apply nodeValid_prime [2, 3, 5, 29, 971] ⟨844771, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_971
  · decide +kernel

theorem prime_986563 : Nat.Prime 986563 := by
  apply nodeValid_prime [2, 3, 23, 2383] ⟨986563, 2, [(2, 1), (3, 2), (23, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2383
  · decide +kernel

theorem prime_1259249 : Nat.Prime 1259249 := by
  apply nodeValid_prime [2, 211, 373] ⟨1259249, 3, [(2, 4), (211, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_373
  · decide +kernel

theorem prime_1386193 : Nat.Prime 1386193 := by
  apply nodeValid_prime [2, 3, 28879] ⟨1386193, 10, [(2, 4), (3, 1), (28879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28879
  · decide +kernel

theorem prime_1748489 : Nat.Prime 1748489 := by
  apply nodeValid_prime [2, 7, 31223] ⟨1748489, 3, [(2, 3), (7, 1), (31223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31223
  · decide +kernel

theorem prime_1781581 : Nat.Prime 1781581 := by
  apply nodeValid_prime [2, 3, 5, 23, 1291] ⟨1781581, 2, [(2, 2), (3, 1), (5, 1), (23, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1291
  · decide +kernel

theorem prime_2104391 : Nat.Prime 2104391 := by
  apply nodeValid_prime [2, 5, 127, 1657] ⟨2104391, 7, [(2, 1), (5, 1), (127, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_1657
  · decide +kernel

theorem prime_2522087 : Nat.Prime 2522087 := by
  apply nodeValid_prime [2, 7, 17, 10597] ⟨2522087, 5, [(2, 1), (7, 1), (17, 1), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_10597
  · decide +kernel

theorem prime_3496979 : Nat.Prime 3496979 := by
  apply nodeValid_prime [2, 1748489] ⟨3496979, 2, [(2, 1), (1748489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1748489
  · decide +kernel

theorem prime_3817691 : Nat.Prime 3817691 := by
  apply nodeValid_prime [2, 5, 17, 1321] ⟨3817691, 2, [(2, 1), (5, 1), (17, 2), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1321
  · decide +kernel

theorem prime_3974309 : Nat.Prime 3974309 := by
  apply nodeValid_prime [2, 13, 23, 3323] ⟨3974309, 2, [(2, 2), (13, 1), (23, 1), (3323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_3323
  · decide +kernel

theorem prime_4268603 : Nat.Prime 4268603 := by
  apply nodeValid_prime [2, 13, 73, 173] ⟨4268603, 5, [(2, 1), (13, 2), (73, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_173
  · decide +kernel

theorem prime_7066777 : Nat.Prime 7066777 := by
  apply nodeValid_prime [2, 3, 523, 563] ⟨7066777, 5, [(2, 3), (3, 1), (523, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_563
  · decide +kernel

theorem prime_8107369 : Nat.Prime 8107369 := by
  apply nodeValid_prime [2, 3, 17, 31, 641] ⟨8107369, 22, [(2, 3), (3, 1), (17, 1), (31, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_641
  · decide +kernel

theorem prime_8122249 : Nat.Prime 8122249 := by
  apply nodeValid_prime [2, 3, 31, 1213] ⟨8122249, 17, [(2, 3), (3, 3), (31, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1213
  · decide +kernel

theorem prime_9473351 : Nat.Prime 9473351 := by
  apply nodeValid_prime [2, 5, 189467] ⟨9473351, 29, [(2, 1), (5, 2), (189467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_189467
  · decide +kernel

theorem prime_10517527 : Nat.Prime 10517527 := by
  apply nodeValid_prime [2, 3, 17, 19, 67] ⟨10517527, 5, [(2, 1), (3, 5), (17, 1), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_11031611 : Nat.Prime 11031611 := by
  apply nodeValid_prime [2, 5, 641, 1721] ⟨11031611, 2, [(2, 1), (5, 1), (641, 1), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
    · exact prime_1721
  · decide +kernel

theorem prime_11124731 : Nat.Prime 11124731 := by
  apply nodeValid_prime [2, 5, 283, 3931] ⟨11124731, 6, [(2, 1), (5, 1), (283, 1), (3931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_283
    · exact prime_3931
  · decide +kernel

theorem prime_11175943 : Nat.Prime 11175943 := by
  apply nodeValid_prime [2, 3, 47, 39631] ⟨11175943, 3, [(2, 1), (3, 1), (47, 1), (39631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_39631
  · decide +kernel

theorem prime_11373781 : Nat.Prime 11373781 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 907] ⟨11373781, 10, [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_907
  · decide +kernel

theorem prime_13398001 : Nat.Prime 13398001 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 29] ⟨13398001, 34, [(2, 4), (3, 1), (5, 3), (7, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_14609381 : Nat.Prime 14609381 := by
  apply nodeValid_prime [2, 5, 730469] ⟨14609381, 10, [(2, 2), (5, 1), (730469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_730469
  · decide +kernel

theorem prime_18042067 : Nat.Prime 18042067 := by
  apply nodeValid_prime [2, 3, 7, 17, 8423] ⟨18042067, 5, [(2, 1), (3, 2), (7, 1), (17, 1), (8423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_8423
  · decide +kernel

theorem prime_19624949 : Nat.Prime 19624949 := by
  apply nodeValid_prime [2, 7, 19, 37, 997] ⟨19624949, 3, [(2, 2), (7, 1), (19, 1), (37, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_37
    · exact prime_997
  · decide +kernel

theorem prime_26187617 : Nat.Prime 26187617 := by
  apply nodeValid_prime [2, 7, 13, 17, 23] ⟨26187617, 3, [(2, 5), (7, 1), (13, 1), (17, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_33238423 : Nat.Prime 33238423 := by
  apply nodeValid_prime [2, 3, 7, 151, 1747] ⟨33238423, 3, [(2, 1), (3, 2), (7, 1), (151, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
    · exact prime_1747
  · decide +kernel

theorem prime_88252889 : Nat.Prime 88252889 := by
  apply nodeValid_prime [2, 11031611] ⟨88252889, 3, [(2, 3), (11031611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11031611
  · decide +kernel

theorem prime_89945281 : Nat.Prime 89945281 := by
  apply nodeValid_prime [2, 3, 5, 31231] ⟨89945281, 7, [(2, 6), (3, 2), (5, 1), (31231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31231
  · decide +kernel

theorem prime_209205167 : Nat.Prime 209205167 := by
  apply nodeValid_prime [2, 131, 479, 1667] ⟨209205167, 5, [(2, 1), (131, 1), (479, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_479
    · exact prime_1667
  · decide +kernel

theorem prime_209500937 : Nat.Prime 209500937 := by
  apply nodeValid_prime [2, 26187617] ⟨209500937, 3, [(2, 3), (26187617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26187617
  · decide +kernel

theorem prime_281752321 : Nat.Prime 281752321 := by
  apply nodeValid_prime [2, 3, 5, 239, 307] ⟨281752321, 23, [(2, 8), (3, 1), (5, 1), (239, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239
    · exact prime_307
  · decide +kernel

theorem prime_294555083 : Nat.Prime 294555083 := by
  apply nodeValid_prime [2, 613, 240257] ⟨294555083, 2, [(2, 1), (613, 1), (240257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_240257
  · decide +kernel

theorem prime_333741931 : Nat.Prime 333741931 := by
  apply nodeValid_prime [2, 3, 5, 11124731] ⟨333741931, 14, [(2, 1), (3, 1), (5, 1), (11124731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11124731
  · decide +kernel

theorem prime_333841957 : Nat.Prime 333841957 := by
  apply nodeValid_prime [2, 3, 7, 3974309] ⟨333841957, 2, [(2, 2), (3, 1), (7, 1), (3974309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3974309
  · decide +kernel

theorem prime_386287597 : Nat.Prime 386287597 := by
  apply nodeValid_prime [2, 3, 151, 23687] ⟨386287597, 5, [(2, 2), (3, 3), (151, 1), (23687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_23687
  · decide +kernel

theorem prime_401940031 : Nat.Prime 401940031 := by
  apply nodeValid_prime [2, 3, 5, 13398001] ⟨401940031, 3, [(2, 1), (3, 1), (5, 1), (13398001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13398001
  · decide +kernel

theorem prime_505177877 : Nat.Prime 505177877 := by
  apply nodeValid_prime [2, 7, 18042067] ⟨505177877, 2, [(2, 2), (7, 1), (18042067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_18042067
  · decide +kernel

theorem prime_530540833 : Nat.Prime 530540833 := by
  apply nodeValid_prime [2, 3, 421, 13127] ⟨530540833, 5, [(2, 5), (3, 1), (421, 1), (13127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
    · exact prime_13127
  · decide +kernel

theorem prime_557382887 : Nat.Prime 557382887 := by
  apply nodeValid_prime [2, 73, 3817691] ⟨557382887, 5, [(2, 1), (73, 1), (3817691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_3817691
  · decide +kernel

theorem prime_565852673 : Nat.Prime 565852673 := by
  apply nodeValid_prime [2, 7, 11, 31, 463] ⟨565852673, 3, [(2, 9), (7, 1), (11, 1), (31, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_463
  · decide +kernel

theorem prime_856314649 : Nat.Prime 856314649 := by
  apply nodeValid_prime [2, 3, 7, 19, 223, 401] ⟨856314649, 13, [(2, 3), (3, 2), (7, 1), (19, 1), (223, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_223
    · exact prime_401
  · decide +kernel

theorem prime_1105873583 : Nat.Prime 1105873583 := by
  apply nodeValid_prime [2, 11, 127, 395803] ⟨1105873583, 5, [(2, 1), (11, 1), (127, 1), (395803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_395803
  · decide +kernel

theorem prime_1570564033 : Nat.Prime 1570564033 := by
  apply nodeValid_prime [2, 3, 47, 269, 647] ⟨1570564033, 5, [(2, 6), (3, 1), (47, 1), (269, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_269
    · exact prime_647
  · decide +kernel

theorem prime_1574017943 : Nat.Prime 1574017943 := by
  apply nodeValid_prime [2, 7, 2791, 40283] ⟨1574017943, 5, [(2, 1), (7, 1), (2791, 1), (40283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2791
    · exact prime_40283
  · decide +kernel

theorem prime_1673641337 : Nat.Prime 1673641337 := by
  apply nodeValid_prime [2, 209205167] ⟨1673641337, 3, [(2, 3), (209205167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_209205167
  · decide +kernel

theorem prime_1694459401 : Nat.Prime 1694459401 := by
  apply nodeValid_prime [2, 3, 5, 37, 127, 601] ⟨1694459401, 7, [(2, 3), (3, 1), (5, 2), (37, 1), (127, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_127
    · exact prime_601
  · decide +kernel

theorem prime_1788697927 : Nat.Prime 1788697927 := by
  apply nodeValid_prime [2, 3, 59, 28547] ⟨1788697927, 3, [(2, 1), (3, 2), (59, 2), (28547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_28547
  · decide +kernel

theorem prime_1973961767 : Nat.Prime 1973961767 := by
  apply nodeValid_prime [2, 7, 17, 31, 37, 1033] ⟨1973961767, 5, [(2, 1), (7, 2), (17, 1), (31, 1), (37, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_37
    · exact prime_1033
  · decide +kernel

theorem prime_4132991441 : Nat.Prime 4132991441 := by
  apply nodeValid_prime [2, 5, 23, 43, 52237] ⟨4132991441, 7, [(2, 4), (5, 1), (23, 1), (43, 1), (52237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_43
    · exact prime_52237
  · decide +kernel

theorem prime_4664973307 : Nat.Prime 4664973307 := by
  apply nodeValid_prime [2, 3, 7, 9941, 11173] ⟨4664973307, 2, [(2, 1), (3, 1), (7, 1), (9941, 1), (11173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9941
    · exact prime_11173
  · decide +kernel

theorem prime_6198551063 : Nat.Prime 6198551063 := by
  apply nodeValid_prime [2, 11, 281752321] ⟨6198551063, 5, [(2, 1), (11, 1), (281752321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_281752321
  · decide +kernel

theorem prime_6462142507 : Nat.Prime 6462142507 := by
  apply nodeValid_prime [2, 3, 6661, 53897] ⟨6462142507, 2, [(2, 1), (3, 2), (6661, 1), (53897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6661
    · exact prime_53897
  · decide +kernel

theorem prime_6530962591 : Nat.Prime 6530962591 := by
  apply nodeValid_prime [2, 3, 5, 17, 4268603] ⟨6530962591, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (4268603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_4268603
  · decide +kernel

theorem prime_12697077587 : Nat.Prime 12697077587 := by
  apply nodeValid_prime [2, 191, 33238423] ⟨12697077587, 2, [(2, 1), (191, 1), (33238423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_33238423
  · decide +kernel

theorem prime_13921051927 : Nat.Prime 13921051927 := by
  apply nodeValid_prime [2, 3, 61, 859, 44279] ⟨13921051927, 21, [(2, 1), (3, 1), (61, 1), (859, 1), (44279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_859
    · exact prime_44279
  · decide +kernel

theorem prime_16069793849 : Nat.Prime 16069793849 := by
  apply nodeValid_prime [2, 43, 79, 103, 5741] ⟨16069793849, 3, [(2, 3), (43, 1), (79, 1), (103, 1), (5741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_79
    · exact prime_103
    · exact prime_5741
  · decide +kernel

theorem prime_32654813053 : Nat.Prime 32654813053 := by
  apply nodeValid_prime [2, 3, 17, 5009, 31957] ⟨32654813053, 2, [(2, 2), (3, 1), (17, 1), (5009, 1), (31957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_5009
    · exact prime_31957
  · decide +kernel

theorem prime_64393125373 : Nat.Prime 64393125373 := by
  apply nodeValid_prime [2, 3, 1788697927] ⟨64393125373, 2, [(2, 2), (3, 2), (1788697927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1788697927
  · decide +kernel

theorem prime_189779452913 : Nat.Prime 189779452913 := by
  apply nodeValid_prime [2, 7, 1694459401] ⟨189779452913, 3, [(2, 4), (7, 1), (1694459401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1694459401
  · decide +kernel

theorem prime_193864280699 : Nat.Prime 193864280699 := by
  apply nodeValid_prime [2, 11, 37, 677, 31981] ⟨193864280699, 2, [(2, 1), (11, 2), (37, 1), (677, 1), (31981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_677
    · exact prime_31981
  · decide +kernel

theorem prime_378208726573 : Nat.Prime 378208726573 := by
  apply nodeValid_prime [2, 3, 107, 294555083] ⟨378208726573, 6, [(2, 2), (3, 1), (107, 1), (294555083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_294555083
  · decide +kernel

theorem prime_378208763851 : Nat.Prime 378208763851 := by
  apply nodeValid_prime [2, 3, 5, 311, 8107369] ⟨378208763851, 2, [(2, 1), (3, 1), (5, 2), (311, 1), (8107369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_311
    · exact prime_8107369
  · decide +kernel

theorem prime_378208765387 : Nat.Prime 378208765387 := by
  apply nodeValid_prime [2, 3, 19, 1105873583] ⟨378208765387, 2, [(2, 1), (3, 2), (19, 1), (1105873583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1105873583
  · decide +kernel

theorem prime_378883392649 : Nat.Prime 378883392649 := by
  apply nodeValid_prime [2, 3, 19, 79, 10517527] ⟨378883392649, 7, [(2, 3), (3, 1), (19, 1), (79, 1), (10517527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_79
    · exact prime_10517527
  · decide +kernel

theorem prime_378883392673 : Nat.Prime 378883392673 := by
  apply nodeValid_prime [2, 3, 347, 11373781] ⟨378883392673, 13, [(2, 5), (3, 1), (347, 1), (11373781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
    · exact prime_11373781
  · decide +kernel

theorem prime_378883407751 : Nat.Prime 378883407751 := by
  apply nodeValid_prime [2, 3, 5, 505177877] ⟨378883407751, 19, [(2, 1), (3, 1), (5, 3), (505177877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_505177877
  · decide +kernel

theorem prime_379558891351 : Nat.Prime 379558891351 := by
  apply nodeValid_prime [2, 3, 5, 10259, 82217] ⟨379558891351, 12, [(2, 1), (3, 2), (5, 2), (10259, 1), (82217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10259
    · exact prime_82217
  · decide +kernel

theorem prime_379558891423 : Nat.Prime 379558891423 := by
  apply nodeValid_prime [2, 3, 257, 389, 210923] ⟨379558891423, 3, [(2, 1), (3, 2), (257, 1), (389, 1), (210923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_389
    · exact prime_210923
  · decide +kernel

theorem prime_379558905827 : Nat.Prime 379558905827 := by
  apply nodeValid_prime [2, 189779452913] ⟨379558905827, 2, [(2, 1), (189779452913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_189779452913
  · decide +kernel

theorem prime_380235212573 : Nat.Prime 380235212573 := by
  apply nodeValid_prime [2, 23, 4132991441] ⟨380235212573, 2, [(2, 2), (23, 1), (4132991441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4132991441
  · decide +kernel

theorem prime_380235269327 : Nat.Prime 380235269327 := by
  apply nodeValid_prime [2, 11, 43, 401940031] ⟨380235269327, 5, [(2, 1), (11, 1), (43, 1), (401940031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_401940031
  · decide +kernel

theorem prime_380235269717 : Nat.Prime 380235269717 := by
  apply nodeValid_prime [2, 53, 4621, 388133] ⟨380235269717, 2, [(2, 2), (53, 1), (4621, 1), (388133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_4621
    · exact prime_388133
  · decide +kernel

theorem prime_380912327611 : Nat.Prime 380912327611 := by
  apply nodeValid_prime [2, 3, 5, 12697077587] ⟨380912327611, 2, [(2, 1), (3, 1), (5, 1), (12697077587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12697077587
  · decide +kernel

theorem prime_380912342207 : Nat.Prime 380912342207 := by
  apply nodeValid_prime [2, 11, 1574017943] ⟨380912342207, 10, [(2, 1), (11, 2), (1574017943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1574017943
  · decide +kernel

theorem prime_381590224471 : Nat.Prime 381590224471 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 37, 1259249] ⟨381590224471, 11, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (37, 1), (1259249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_1259249
  · decide +kernel

theorem prime_381590224837 : Nat.Prime 381590224837 := by
  apply nodeValid_prime [2, 3, 19, 1673641337] ⟨381590224837, 5, [(2, 2), (3, 1), (19, 1), (1673641337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1673641337
  · decide +kernel

theorem prime_381590258737 : Nat.Prime 381590258737 := by
  apply nodeValid_prime [2, 3, 17, 29, 59, 273311] ⟨381590258737, 5, [(2, 4), (3, 1), (17, 1), (29, 1), (59, 1), (273311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_59
    · exact prime_273311
  · decide +kernel

theorem prime_382269014753 : Nat.Prime 382269014753 := by
  apply nodeValid_prime [2, 79, 179, 844771] ⟨382269014753, 3, [(2, 5), (79, 1), (179, 1), (844771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_179
    · exact prime_844771
  · decide +kernel

theorem prime_382269062611 : Nat.Prime 382269062611 := by
  apply nodeValid_prime [2, 3, 5, 3011, 470213] ⟨382269062611, 3, [(2, 1), (3, 3), (5, 1), (3011, 1), (470213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3011
    · exact prime_470213
  · decide +kernel

theorem prime_382269063247 : Nat.Prime 382269063247 := by
  apply nodeValid_prime [2, 3, 7, 89, 14609381] ⟨382269063247, 5, [(2, 1), (3, 1), (7, 2), (89, 1), (14609381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_14609381
  · decide +kernel

theorem prime_382948582799 : Nat.Prime 382948582799 := by
  apply nodeValid_prime [2, 97, 1973961767] ⟨382948582799, 19, [(2, 1), (97, 1), (1973961767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1973961767
  · decide +kernel

theorem prime_382948645631 : Nat.Prime 382948645631 := by
  apply nodeValid_prime [2, 5, 5419, 7066777] ⟨382948645631, 13, [(2, 1), (5, 1), (5419, 1), (7066777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5419
    · exact prime_7066777
  · decide +kernel

theorem prime_382948645907 : Nat.Prime 382948645907 := by
  apply nodeValid_prime [2, 31, 79, 2522087] ⟨382948645907, 2, [(2, 1), (31, 2), (79, 1), (2522087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_79
    · exact prime_2522087
  · decide +kernel

theorem prime_383628962753 : Nat.Prime 383628962753 := by
  apply nodeValid_prime [2, 7, 856314649] ⟨383628962753, 3, [(2, 6), (7, 1), (856314649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_856314649
  · decide +kernel

theorem prime_383628963551 : Nat.Prime 383628963551 := by
  apply nodeValid_prime [2, 5, 7, 29, 887, 42611] ⟨383628963551, 7, [(2, 1), (5, 2), (7, 1), (29, 1), (887, 1), (42611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_887
    · exact prime_42611
  · decide +kernel

theorem prime_383628968803 : Nat.Prime 383628968803 := by
  apply nodeValid_prime [2, 3, 19, 379, 986563] ⟨383628968803, 2, [(2, 1), (3, 3), (19, 1), (379, 1), (986563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_379
    · exact prime_986563
  · decide +kernel

theorem prime_384310165907 : Nat.Prime 384310165907 := by
  apply nodeValid_prime [2, 31, 6198551063] ⟨384310165907, 2, [(2, 1), (31, 1), (6198551063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_6198551063
  · decide +kernel

theorem prime_384310167209 : Nat.Prime 384310167209 := by
  apply nodeValid_prime [2, 11, 17, 31, 1597, 5189] ⟨384310167209, 3, [(2, 3), (11, 1), (17, 1), (31, 1), (1597, 1), (5189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_31
    · exact prime_1597
    · exact prime_5189
  · decide +kernel

theorem prime_384310180081 : Nat.Prime 384310180081 := by
  apply nodeValid_prime [2, 3, 5, 6917, 77167] ⟨384310180081, 53, [(2, 4), (3, 2), (5, 1), (6917, 1), (77167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6917
    · exact prime_77167
  · decide +kernel

theorem prime_384992208647 : Nat.Prime 384992208647 := by
  apply nodeValid_prime [2, 101, 17669, 107867] ⟨384992208647, 5, [(2, 1), (101, 1), (17669, 1), (107867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_17669
    · exact prime_107867
  · decide +kernel

theorem prime_384992218561 : Nat.Prime 384992218561 := by
  apply nodeValid_prime [2, 3, 5, 59, 373, 18223] ⟨384992218561, 7, [(2, 6), (3, 1), (5, 1), (59, 1), (373, 1), (18223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_373
    · exact prime_18223
  · decide +kernel

theorem prime_384992220967 : Nat.Prime 384992220967 := by
  apply nodeValid_prime [2, 3, 213019, 301219] ⟨384992220967, 6, [(2, 1), (3, 1), (213019, 1), (301219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_213019
    · exact prime_301219
  · decide +kernel

theorem prime_385675051207 : Nat.Prime 385675051207 := by
  apply nodeValid_prime [2, 3, 17, 41, 313, 294641] ⟨385675051207, 3, [(2, 1), (3, 1), (17, 1), (41, 1), (313, 1), (294641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_313
    · exact prime_294641
  · decide +kernel

theorem prime_385675052377 : Nat.Prime 385675052377 := by
  apply nodeValid_prime [2, 3, 16069793849] ⟨385675052377, 5, [(2, 3), (3, 1), (16069793849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16069793849
  · decide +kernel

theorem prime_385675064783 : Nat.Prime 385675064783 := by
  apply nodeValid_prime [2, 7, 31, 7517, 118219] ⟨385675064783, 7, [(2, 1), (7, 1), (31, 1), (7517, 1), (118219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_7517
    · exact prime_118219
  · decide +kernel

theorem prime_386358745811 : Nat.Prime 386358745811 := by
  apply nodeValid_prime [2, 5, 239, 601, 268979] ⟨386358745811, 2, [(2, 1), (5, 1), (239, 1), (601, 1), (268979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_601
    · exact prime_268979
  · decide +kernel

theorem prime_386358752119 : Nat.Prime 386358752119 := by
  apply nodeValid_prime [2, 3, 41, 1570564033] ⟨386358752119, 3, [(2, 1), (3, 1), (41, 1), (1570564033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1570564033
  · decide +kernel

theorem prime_386358752239 : Nat.Prime 386358752239 := by
  apply nodeValid_prime [2, 3, 64393125373] ⟨386358752239, 3, [(2, 1), (3, 1), (64393125373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_64393125373
  · decide +kernel

theorem prime_387043228333 : Nat.Prime 387043228333 := by
  apply nodeValid_prime [2, 3, 19, 565852673] ⟨387043228333, 2, [(2, 2), (3, 2), (19, 1), (565852673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_565852673
  · decide +kernel

theorem prime_387043228457 : Nat.Prime 387043228457 := by
  apply nodeValid_prime [2, 5107, 9473351] ⟨387043228457, 3, [(2, 3), (5107, 1), (9473351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5107
    · exact prime_9473351
  · decide +kernel

theorem prime_387043244179 : Nat.Prime 387043244179 := by
  apply nodeValid_prime [2, 3, 19, 173, 19624949] ⟨387043244179, 2, [(2, 1), (3, 1), (19, 1), (173, 1), (19624949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_173
    · exact prime_19624949
  · decide +kernel

theorem prime_387728546977 : Nat.Prime 387728546977 := by
  apply nodeValid_prime [2, 3, 23, 3821, 15319] ⟨387728546977, 10, [(2, 5), (3, 2), (23, 1), (3821, 1), (15319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3821
    · exact prime_15319
  · decide +kernel

theorem prime_387728550421 : Nat.Prime 387728550421 := by
  apply nodeValid_prime [2, 3, 5, 6462142507] ⟨387728550421, 10, [(2, 2), (3, 1), (5, 1), (6462142507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6462142507
  · decide +kernel

theorem prime_387728561399 : Nat.Prime 387728561399 := by
  apply nodeValid_prime [2, 193864280699] ⟨387728561399, 7, [(2, 1), (193864280699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193864280699
  · decide +kernel

theorem prime_388414702471 : Nat.Prime 388414702471 := by
  apply nodeValid_prime [2, 3, 5, 29, 1627, 274403] ⟨388414702471, 3, [(2, 1), (3, 1), (5, 1), (29, 1), (1627, 1), (274403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1627
    · exact prime_274403
  · decide +kernel

theorem prime_388414737199 : Nat.Prime 388414737199 := by
  apply nodeValid_prime [2, 3, 103, 209500937] ⟨388414737199, 6, [(2, 1), (3, 2), (103, 1), (209500937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_209500937
  · decide +kernel

theorem prime_388414738087 : Nat.Prime 388414738087 := by
  apply nodeValid_prime [2, 3, 263, 5503, 44729] ⟨388414738087, 3, [(2, 1), (3, 1), (263, 1), (5503, 1), (44729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_5503
    · exact prime_44729
  · decide +kernel

theorem prime_389101631489 : Nat.Prime 389101631489 := by
  apply nodeValid_prime [2, 17, 11175943] ⟨389101631489, 3, [(2, 11), (17, 1), (11175943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_11175943
  · decide +kernel

theorem prime_389101664089 : Nat.Prime 389101664089 := by
  apply nodeValid_prime [2, 3, 19, 23, 71, 6451] ⟨389101664089, 7, [(2, 3), (3, 5), (19, 1), (23, 1), (71, 1), (6451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_71
    · exact prime_6451
  · decide +kernel

theorem prime_389789447533 : Nat.Prime 389789447533 := by
  apply nodeValid_prime [2, 3, 23, 83, 4111, 4139] ⟨389789447533, 2, [(2, 2), (3, 1), (23, 1), (83, 1), (4111, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_83
    · exact prime_4111
    · exact prime_4139
  · decide +kernel

theorem prime_389789453957 : Nat.Prime 389789453957 := by
  apply nodeValid_prime [2, 7, 13921051927] ⟨389789453957, 2, [(2, 2), (7, 1), (13921051927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13921051927
  · decide +kernel

theorem prime_389789454287 : Nat.Prime 389789454287 := by
  apply nodeValid_prime [2, 2269, 2531, 33937] ⟨389789454287, 5, [(2, 1), (2269, 1), (2531, 1), (33937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2269
    · exact prime_2531
    · exact prime_33937
  · decide +kernel

theorem prime_390478053089 : Nat.Prime 390478053089 := by
  apply nodeValid_prime [2, 23, 530540833] ⟨390478053089, 3, [(2, 5), (23, 1), (530540833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_530540833
  · decide +kernel

theorem prime_390478058987 : Nat.Prime 390478058987 := by
  apply nodeValid_prime [2, 149, 26459, 49523] ⟨390478058987, 2, [(2, 1), (149, 1), (26459, 1), (49523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_26459
    · exact prime_49523
  · decide +kernel

theorem prime_390478059271 : Nat.Prime 390478059271 := by
  apply nodeValid_prime [2, 3, 5, 13, 333741931] ⟨390478059271, 6, [(2, 1), (3, 2), (5, 1), (13, 1), (333741931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_333741931
  · decide +kernel

theorem prime_391167487523 : Nat.Prime 391167487523 := by
  apply nodeValid_prime [2, 7, 15683, 1781581] ⟨391167487523, 2, [(2, 1), (7, 1), (15683, 1), (1781581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15683
    · exact prime_1781581
  · decide +kernel

theorem prime_391167511487 : Nat.Prime 391167511487 := by
  apply nodeValid_prime [2, 353, 1069, 518299] ⟨391167511487, 5, [(2, 1), (353, 1), (1069, 1), (518299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_1069
    · exact prime_518299
  · decide +kernel

theorem prime_391167511841 : Nat.Prime 391167511841 := by
  apply nodeValid_prime [2, 5, 7, 43, 8122249] ⟨391167511841, 3, [(2, 5), (5, 1), (7, 1), (43, 1), (8122249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_8122249
  · decide +kernel

theorem prime_391857755461 : Nat.Prime 391857755461 := by
  apply nodeValid_prime [2, 3, 5, 6530962591] ⟨391857755461, 10, [(2, 2), (3, 1), (5, 1), (6530962591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6530962591
  · decide +kernel

theorem prime_391857756637 : Nat.Prime 391857756637 := by
  apply nodeValid_prime [2, 3, 32654813053] ⟨391857756637, 2, [(2, 2), (3, 1), (32654813053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32654813053
  · decide +kernel

theorem prime_391857757789 : Nat.Prime 391857757789 := by
  apply nodeValid_prime [2, 3, 7, 4664973307] ⟨391857757789, 2, [(2, 2), (3, 1), (7, 1), (4664973307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4664973307
  · decide +kernel

theorem prime_392548850273 : Nat.Prime 392548850273 := by
  apply nodeValid_prime [2, 139, 88252889] ⟨392548850273, 3, [(2, 5), (139, 1), (88252889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_88252889
  · decide +kernel

theorem prime_392548853707 : Nat.Prime 392548853707 := by
  apply nodeValid_prime [2, 3, 523, 5653, 22129] ⟨392548853707, 3, [(2, 1), (3, 1), (523, 1), (5653, 1), (22129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_5653
    · exact prime_22129
  · decide +kernel

theorem prime_392548855177 : Nat.Prime 392548855177 := by
  apply nodeValid_prime [2, 3, 17, 31, 653, 5281] ⟨392548855177, 5, [(2, 3), (3, 3), (17, 1), (31, 1), (653, 1), (5281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_653
    · exact prime_5281
  · decide +kernel

theorem prime_393240768533 : Nat.Prime 393240768533 := by
  apply nodeValid_prime [2, 1093, 89945281] ⟨393240768533, 2, [(2, 2), (1093, 1), (89945281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1093
    · exact prime_89945281
  · decide +kernel

theorem prime_393240773747 : Nat.Prime 393240773747 := by
  apply nodeValid_prime [2, 509, 386287597] ⟨393240773747, 2, [(2, 1), (509, 1), (386287597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_386287597
  · decide +kernel

theorem prime_393240775013 : Nat.Prime 393240775013 := by
  apply nodeValid_prime [2, 70921, 1386193] ⟨393240775013, 2, [(2, 2), (70921, 1), (1386193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_70921
    · exact prime_1386193
  · decide +kernel

theorem prime_393933509261 : Nat.Prime 393933509261 := by
  apply nodeValid_prime [2, 5, 59, 333841957] ⟨393933509261, 3, [(2, 2), (5, 1), (59, 1), (333841957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_333841957
  · decide +kernel

theorem prime_393933576809 : Nat.Prime 393933576809 := by
  apply nodeValid_prime [2, 47, 67, 109, 143461] ⟨393933576809, 3, [(2, 3), (47, 1), (67, 1), (109, 1), (143461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_67
    · exact prime_109
    · exact prime_143461
  · decide +kernel

theorem prime_393933577637 : Nat.Prime 393933577637 := by
  apply nodeValid_prime [2, 53, 883, 2104391] ⟨393933577637, 2, [(2, 2), (53, 1), (883, 1), (2104391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_883
    · exact prime_2104391
  · decide +kernel

theorem prime_394627075471 : Nat.Prime 394627075471 := by
  apply nodeValid_prime [2, 3, 5, 3677, 397493] ⟨394627075471, 3, [(2, 1), (3, 3), (5, 1), (3677, 1), (397493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3677
    · exact prime_397493
  · decide +kernel

theorem prime_394627083997 : Nat.Prime 394627083997 := by
  apply nodeValid_prime [2, 3, 59, 557382887] ⟨394627083997, 2, [(2, 2), (3, 1), (59, 1), (557382887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_557382887
  · decide +kernel

theorem prime_394627086193 : Nat.Prime 394627086193 := by
  apply nodeValid_prime [2, 3, 2351, 3496979] ⟨394627086193, 5, [(2, 4), (3, 1), (2351, 1), (3496979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2351
    · exact prime_3496979
  · decide +kernel

end Sude.Lucas.Generated
