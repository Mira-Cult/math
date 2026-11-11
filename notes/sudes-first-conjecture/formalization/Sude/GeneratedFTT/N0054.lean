import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3727 : Nat.Prime 3727 := by
  apply nodeValid_prime [2, 3, 23] ⟨3727, 3, [(2, 1), (3, 4), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_4931 : Nat.Prime 4931 := by
  apply nodeValid_prime [2, 5, 17, 29] ⟨4931, 6, [(2, 1), (5, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_6271 : Nat.Prime 6271 := by
  apply nodeValid_prime [2, 3, 5, 11, 19] ⟨6271, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_9883 : Nat.Prime 9883 := by
  apply nodeValid_prime [2, 3, 61] ⟨9883, 2, [(2, 1), (3, 4), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel

theorem prime_11393 : Nat.Prime 11393 := by
  apply nodeValid_prime [2, 89] ⟨11393, 3, [(2, 7), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_89
  · decide +kernel

theorem prime_11903 : Nat.Prime 11903 := by
  apply nodeValid_prime [2, 11, 541] ⟨11903, 5, [(2, 1), (11, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_541
  · decide +kernel

theorem prime_14593 : Nat.Prime 14593 := by
  apply nodeValid_prime [2, 3, 19] ⟨14593, 5, [(2, 8), (3, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_15907 : Nat.Prime 15907 := by
  apply nodeValid_prime [2, 3, 11, 241] ⟨15907, 2, [(2, 1), (3, 1), (11, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_241
  · decide +kernel

theorem prime_16421 : Nat.Prime 16421 := by
  apply nodeValid_prime [2, 5, 821] ⟨16421, 2, [(2, 2), (5, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_821
  · decide +kernel

theorem prime_19681 : Nat.Prime 19681 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨19681, 11, [(2, 5), (3, 1), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_24611 : Nat.Prime 24611 := by
  apply nodeValid_prime [2, 5, 23, 107] ⟨24611, 13, [(2, 1), (5, 1), (23, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_107
  · decide +kernel

theorem prime_25171 : Nat.Prime 25171 := by
  apply nodeValid_prime [2, 3, 5, 839] ⟨25171, 3, [(2, 1), (3, 1), (5, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_839
  · decide +kernel

theorem prime_25673 : Nat.Prime 25673 := by
  apply nodeValid_prime [2, 3209] ⟨25673, 3, [(2, 3), (3209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3209
  · decide +kernel

theorem prime_27197 : Nat.Prime 27197 := by
  apply nodeValid_prime [2, 13, 523] ⟨27197, 2, [(2, 2), (13, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_523
  · decide +kernel

theorem prime_27367 : Nat.Prime 27367 := by
  apply nodeValid_prime [2, 3, 4561] ⟨27367, 3, [(2, 1), (3, 1), (4561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4561
  · decide +kernel

theorem prime_28649 : Nat.Prime 28649 := by
  apply nodeValid_prime [2, 3581] ⟨28649, 3, [(2, 3), (3581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3581
  · decide +kernel

theorem prime_30661 : Nat.Prime 30661 := by
  apply nodeValid_prime [2, 3, 5, 7, 73] ⟨30661, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_31123 : Nat.Prime 31123 := by
  apply nodeValid_prime [2, 3, 7, 13, 19] ⟨31123, 3, [(2, 1), (3, 2), (7, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_31489 : Nat.Prime 31489 := by
  apply nodeValid_prime [2, 3, 41] ⟨31489, 7, [(2, 8), (3, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_32233 : Nat.Prime 32233 := by
  apply nodeValid_prime [2, 3, 17, 79] ⟨32233, 5, [(2, 3), (3, 1), (17, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_79
  · decide +kernel

theorem prime_32843 : Nat.Prime 32843 := by
  apply nodeValid_prime [2, 16421] ⟨32843, 2, [(2, 1), (16421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16421
  · decide +kernel

theorem prime_37463 : Nat.Prime 37463 := by
  apply nodeValid_prime [2, 18731] ⟨37463, 5, [(2, 1), (18731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18731
  · decide +kernel

theorem prime_44797 : Nat.Prime 44797 := by
  apply nodeValid_prime [2, 3, 3733] ⟨44797, 2, [(2, 2), (3, 1), (3733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3733
  · decide +kernel

theorem prime_49081 : Nat.Prime 49081 := by
  apply nodeValid_prime [2, 3, 5, 409] ⟨49081, 11, [(2, 3), (3, 1), (5, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_409
  · decide +kernel

theorem prime_65171 : Nat.Prime 65171 := by
  apply nodeValid_prime [2, 5, 7, 19] ⟨65171, 2, [(2, 1), (5, 1), (7, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_65687 : Nat.Prime 65687 := by
  apply nodeValid_prime [2, 32843] ⟨65687, 5, [(2, 1), (32843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32843
  · decide +kernel

theorem prime_70901 : Nat.Prime 70901 := by
  apply nodeValid_prime [2, 5, 709] ⟨70901, 2, [(2, 2), (5, 2), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_709
  · decide +kernel

theorem prime_73043 : Nat.Prime 73043 := by
  apply nodeValid_prime [2, 59, 619] ⟨73043, 2, [(2, 1), (59, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_619
  · decide +kernel

theorem prime_82141 : Nat.Prime 82141 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨82141, 6, [(2, 2), (3, 1), (5, 1), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_84467 : Nat.Prime 84467 := by
  apply nodeValid_prime [2, 157, 269] ⟨84467, 2, [(2, 1), (157, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_269
  · decide +kernel

theorem prime_92669 : Nat.Prime 92669 := by
  apply nodeValid_prime [2, 23167] ⟨92669, 2, [(2, 2), (23167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23167
  · decide +kernel

theorem prime_102523 : Nat.Prime 102523 := by
  apply nodeValid_prime [2, 3, 7, 2441] ⟨102523, 2, [(2, 1), (3, 1), (7, 1), (2441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2441
  · decide +kernel

theorem prime_104173 : Nat.Prime 104173 := by
  apply nodeValid_prime [2, 3, 8681] ⟨104173, 2, [(2, 2), (3, 1), (8681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8681
  · decide +kernel

theorem prime_113027 : Nat.Prime 113027 := by
  apply nodeValid_prime [2, 31, 1823] ⟨113027, 2, [(2, 1), (31, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1823
  · decide +kernel

theorem prime_133349 : Nat.Prime 133349 := by
  apply nodeValid_prime [2, 17, 37, 53] ⟨133349, 2, [(2, 2), (17, 1), (37, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_53
  · decide +kernel

theorem prime_147547 : Nat.Prime 147547 := by
  apply nodeValid_prime [2, 3, 7, 1171] ⟨147547, 2, [(2, 1), (3, 2), (7, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1171
  · decide +kernel

theorem prime_157793 : Nat.Prime 157793 := by
  apply nodeValid_prime [2, 4931] ⟨157793, 3, [(2, 5), (4931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4931
  · decide +kernel

theorem prime_172969 : Nat.Prime 172969 := by
  apply nodeValid_prime [2, 3, 7207] ⟨172969, 7, [(2, 3), (3, 1), (7207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7207
  · decide +kernel

theorem prime_173021 : Nat.Prime 173021 := by
  apply nodeValid_prime [2, 5, 41, 211] ⟨173021, 2, [(2, 2), (5, 1), (41, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_211
  · decide +kernel

theorem prime_174067 : Nat.Prime 174067 := by
  apply nodeValid_prime [2, 3, 67, 433] ⟨174067, 2, [(2, 1), (3, 1), (67, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_433
  · decide +kernel

theorem prime_178897 : Nat.Prime 178897 := by
  apply nodeValid_prime [2, 3, 3727] ⟨178897, 7, [(2, 4), (3, 1), (3727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3727
  · decide +kernel

theorem prime_181361 : Nat.Prime 181361 := by
  apply nodeValid_prime [2, 5, 2267] ⟨181361, 3, [(2, 4), (5, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2267
  · decide +kernel

theorem prime_184477 : Nat.Prime 184477 := by
  apply nodeValid_prime [2, 3, 15373] ⟨184477, 2, [(2, 2), (3, 1), (15373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15373
  · decide +kernel

theorem prime_196597 : Nat.Prime 196597 := by
  apply nodeValid_prime [2, 3, 43, 127] ⟨196597, 5, [(2, 2), (3, 2), (43, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_127
  · decide +kernel

theorem prime_202679 : Nat.Prime 202679 := by
  apply nodeValid_prime [2, 7, 31, 467] ⟨202679, 7, [(2, 1), (7, 1), (31, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_467
  · decide +kernel

theorem prime_216113 : Nat.Prime 216113 := by
  apply nodeValid_prime [2, 13, 1039] ⟨216113, 3, [(2, 4), (13, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1039
  · decide +kernel

theorem prime_217577 : Nat.Prime 217577 := by
  apply nodeValid_prime [2, 27197] ⟨217577, 3, [(2, 3), (27197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27197
  · decide +kernel

theorem prime_224429 : Nat.Prime 224429 := by
  apply nodeValid_prime [2, 19, 2953] ⟨224429, 2, [(2, 2), (19, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2953
  · decide +kernel

theorem prime_318299 : Nat.Prime 318299 := by
  apply nodeValid_prime [2, 61, 2609] ⟨318299, 2, [(2, 1), (61, 1), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_2609
  · decide +kernel

theorem prime_370057 : Nat.Prime 370057 := by
  apply nodeValid_prime [2, 3, 17, 907] ⟨370057, 5, [(2, 3), (3, 1), (17, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_907
  · decide +kernel

theorem prime_406789 : Nat.Prime 406789 := by
  apply nodeValid_prime [2, 3, 109, 311] ⟨406789, 6, [(2, 2), (3, 1), (109, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_311
  · decide +kernel

theorem prime_438259 : Nat.Prime 438259 := by
  apply nodeValid_prime [2, 3, 73043] ⟨438259, 3, [(2, 1), (3, 1), (73043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73043
  · decide +kernel

theorem prime_478351 : Nat.Prime 478351 := by
  apply nodeValid_prime [2, 3, 5, 1063] ⟨478351, 3, [(2, 1), (3, 2), (5, 2), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1063
  · decide +kernel

theorem prime_501427 : Nat.Prime 501427 := by
  apply nodeValid_prime [2, 3, 89, 313] ⟨501427, 2, [(2, 1), (3, 2), (89, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_313
  · decide +kernel

theorem prime_511603 : Nat.Prime 511603 := by
  apply nodeValid_prime [2, 3, 7, 13, 937] ⟨511603, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_937
  · decide +kernel

theorem prime_530653 : Nat.Prime 530653 := by
  apply nodeValid_prime [2, 3, 44221] ⟨530653, 11, [(2, 2), (3, 1), (44221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44221
  · decide +kernel

theorem prime_564191 : Nat.Prime 564191 := by
  apply nodeValid_prime [2, 5, 11, 23, 223] ⟨564191, 11, [(2, 1), (5, 1), (11, 1), (23, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_223
  · decide +kernel

theorem prime_574813 : Nat.Prime 574813 := by
  apply nodeValid_prime [2, 3, 7, 2281] ⟨574813, 5, [(2, 2), (3, 2), (7, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2281
  · decide +kernel

theorem prime_652279 : Nat.Prime 652279 := by
  apply nodeValid_prime [2, 3, 11, 9883] ⟨652279, 12, [(2, 1), (3, 1), (11, 1), (9883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9883
  · decide +kernel

theorem prime_691877 : Nat.Prime 691877 := by
  apply nodeValid_prime [2, 172969] ⟨691877, 2, [(2, 2), (172969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_172969
  · decide +kernel

theorem prime_697069 : Nat.Prime 697069 := by
  apply nodeValid_prime [2, 3, 17, 67] ⟨697069, 2, [(2, 2), (3, 2), (17, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_703039 : Nat.Prime 703039 := by
  apply nodeValid_prime [2, 3, 7, 19, 881] ⟨703039, 3, [(2, 1), (3, 1), (7, 1), (19, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_881
  · decide +kernel

theorem prime_712891 : Nat.Prime 712891 := by
  apply nodeValid_prime [2, 3, 5, 89] ⟨712891, 2, [(2, 1), (3, 2), (5, 1), (89, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_746777 : Nat.Prime 746777 := by
  apply nodeValid_prime [2, 17, 19] ⟨746777, 3, [(2, 3), (17, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_1073383 : Nat.Prime 1073383 := by
  apply nodeValid_prime [2, 3, 178897] ⟨1073383, 3, [(2, 1), (3, 1), (178897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_178897
  · decide +kernel

theorem prime_1128383 : Nat.Prime 1128383 := by
  apply nodeValid_prime [2, 564191] ⟨1128383, 5, [(2, 1), (564191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_564191
  · decide +kernel

theorem prime_1525969 : Nat.Prime 1525969 := by
  apply nodeValid_prime [2, 3, 10597] ⟨1525969, 23, [(2, 4), (3, 2), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10597
  · decide +kernel

theorem prime_1612693 : Nat.Prime 1612693 := by
  apply nodeValid_prime [2, 3, 44797] ⟨1612693, 2, [(2, 2), (3, 2), (44797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44797
  · decide +kernel

theorem prime_1624327 : Nat.Prime 1624327 := by
  apply nodeValid_prime [2, 3, 11, 24611] ⟨1624327, 6, [(2, 1), (3, 1), (11, 1), (24611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_24611
  · decide +kernel

theorem prime_1663547 : Nat.Prime 1663547 := by
  apply nodeValid_prime [2, 761, 1093] ⟨1663547, 2, [(2, 1), (761, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_761
    · exact prime_1093
  · decide +kernel

theorem prime_1776239 : Nat.Prime 1776239 := by
  apply nodeValid_prime [2, 31, 28649] ⟨1776239, 11, [(2, 1), (31, 1), (28649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_28649
  · decide +kernel

theorem prime_1824673 : Nat.Prime 1824673 := by
  apply nodeValid_prime [2, 3, 83, 229] ⟨1824673, 10, [(2, 5), (3, 1), (83, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_229
  · decide +kernel

theorem prime_2007917 : Nat.Prime 2007917 := by
  apply nodeValid_prime [2, 37, 13567] ⟨2007917, 2, [(2, 2), (37, 1), (13567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_13567
  · decide +kernel

theorem prime_2089511 : Nat.Prime 2089511 := by
  apply nodeValid_prime [2, 5, 223, 937] ⟨2089511, 7, [(2, 1), (5, 1), (223, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_223
    · exact prime_937
  · decide +kernel

theorem prime_2620307 : Nat.Prime 2620307 := by
  apply nodeValid_prime [2, 13, 31, 3251] ⟨2620307, 2, [(2, 1), (13, 1), (31, 1), (3251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_3251
  · decide +kernel

theorem prime_3221819 : Nat.Prime 3221819 := by
  apply nodeValid_prime [2, 43, 37463] ⟨3221819, 2, [(2, 1), (43, 1), (37463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_37463
  · decide +kernel

theorem prime_3298019 : Nat.Prime 3298019 := by
  apply nodeValid_prime [2, 113, 14593] ⟨3298019, 2, [(2, 1), (113, 1), (14593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_14593
  · decide +kernel

theorem prime_4179023 : Nat.Prime 4179023 := by
  apply nodeValid_prime [2, 2089511] ⟨4179023, 5, [(2, 1), (2089511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2089511
  · decide +kernel

theorem prime_4553239 : Nat.Prime 4553239 := by
  apply nodeValid_prime [2, 3, 523, 1451] ⟨4553239, 3, [(2, 1), (3, 1), (523, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_1451
  · decide +kernel

theorem prime_5302403 : Nat.Prime 5302403 := by
  apply nodeValid_prime [2, 7, 17, 22279] ⟨5302403, 2, [(2, 1), (7, 1), (17, 1), (22279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_22279
  · decide +kernel

theorem prime_5306531 : Nat.Prime 5306531 := by
  apply nodeValid_prime [2, 5, 530653] ⟨5306531, 6, [(2, 1), (5, 1), (530653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_530653
  · decide +kernel

theorem prime_7145969 : Nat.Prime 7145969 := by
  apply nodeValid_prime [2, 83, 5381] ⟨7145969, 3, [(2, 4), (83, 1), (5381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_5381
  · decide +kernel

theorem prime_7389091 : Nat.Prime 7389091 := by
  apply nodeValid_prime [2, 3, 5, 27367] ⟨7389091, 2, [(2, 1), (3, 3), (5, 1), (27367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27367
  · decide +kernel

theorem prime_8020673 : Nat.Prime 8020673 := by
  apply nodeValid_prime [2, 11, 11393] ⟨8020673, 3, [(2, 6), (11, 1), (11393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11393
  · decide +kernel

theorem prime_9375571 : Nat.Prime 9375571 := by
  apply nodeValid_prime [2, 3, 5, 104173] ⟨9375571, 7, [(2, 1), (3, 2), (5, 1), (104173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_104173
  · decide +kernel

theorem prime_10613063 : Nat.Prime 10613063 := by
  apply nodeValid_prime [2, 5306531] ⟨10613063, 5, [(2, 1), (5306531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5306531
  · decide +kernel

theorem prime_12112957 : Nat.Prime 12112957 := by
  apply nodeValid_prime [2, 3, 19, 5903] ⟨12112957, 2, [(2, 2), (3, 3), (19, 1), (5903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_5903
  · decide +kernel

theorem prime_15259691 : Nat.Prime 15259691 := by
  apply nodeValid_prime [2, 5, 1525969] ⟨15259691, 2, [(2, 1), (5, 1), (1525969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1525969
  · decide +kernel

theorem prime_15627779 : Nat.Prime 15627779 := by
  apply nodeValid_prime [2, 103, 107, 709] ⟨15627779, 2, [(2, 1), (103, 1), (107, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_107
    · exact prime_709
  · decide +kernel

theorem prime_16256507 : Nat.Prime 16256507 := by
  apply nodeValid_prime [2, 7, 59, 19681] ⟨16256507, 5, [(2, 1), (7, 1), (59, 1), (19681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_19681
  · decide +kernel

theorem prime_22412059 : Nat.Prime 22412059 := by
  apply nodeValid_prime [2, 3, 19, 196597] ⟨22412059, 2, [(2, 1), (3, 1), (19, 1), (196597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_196597
  · decide +kernel

theorem prime_26551513 : Nat.Prime 26551513 := by
  apply nodeValid_prime [2, 3, 13, 19, 1493] ⟨26551513, 5, [(2, 3), (3, 2), (13, 1), (19, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_1493
  · decide +kernel

theorem prime_29341139 : Nat.Prime 29341139 := by
  apply nodeValid_prime [2, 2083, 7043] ⟨29341139, 2, [(2, 1), (2083, 1), (7043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2083
    · exact prime_7043
  · decide +kernel

theorem prime_33851491 : Nat.Prime 33851491 := by
  apply nodeValid_prime [2, 3, 5, 1128383] ⟨33851491, 2, [(2, 1), (3, 1), (5, 1), (1128383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1128383
  · decide +kernel

theorem prime_34455431 : Nat.Prime 34455431 := by
  apply nodeValid_prime [2, 5, 17, 202679] ⟨34455431, 31, [(2, 1), (5, 1), (17, 1), (202679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_202679
  · decide +kernel

theorem prime_36354677 : Nat.Prime 36354677 := by
  apply nodeValid_prime [2, 19, 478351] ⟨36354677, 2, [(2, 2), (19, 1), (478351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_478351
  · decide +kernel

theorem prime_49081001 : Nat.Prime 49081001 := by
  apply nodeValid_prime [2, 5, 49081] ⟨49081001, 3, [(2, 3), (5, 3), (49081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49081
  · decide +kernel

theorem prime_67497083 : Nat.Prime 67497083 := by
  apply nodeValid_prime [2, 19, 1776239] ⟨67497083, 2, [(2, 1), (19, 1), (1776239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1776239
  · decide +kernel

theorem prime_79216861 : Nat.Prime 79216861 := by
  apply nodeValid_prime [2, 3, 5, 83, 15907] ⟨79216861, 2, [(2, 2), (3, 1), (5, 1), (83, 1), (15907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_15907
  · decide +kernel

theorem prime_130966567 : Nat.Prime 130966567 := by
  apply nodeValid_prime [2, 3, 1277, 17093] ⟨130966567, 3, [(2, 1), (3, 1), (1277, 1), (17093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1277
    · exact prime_17093
  · decide +kernel

theorem prime_135551917 : Nat.Prime 135551917 := by
  apply nodeValid_prime [2, 3, 29, 157, 827] ⟨135551917, 2, [(2, 2), (3, 2), (29, 1), (157, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_157
    · exact prime_827
  · decide +kernel

theorem prime_168828991 : Nat.Prime 168828991 := by
  apply nodeValid_prime [2, 3, 5, 11, 511603] ⟨168828991, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (511603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_511603
  · decide +kernel

theorem prime_257810251 : Nat.Prime 257810251 := by
  apply nodeValid_prime [2, 3, 5, 139, 2473] ⟨257810251, 3, [(2, 1), (3, 1), (5, 3), (139, 1), (2473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_2473
  · decide +kernel

theorem prime_294486007 : Nat.Prime 294486007 := by
  apply nodeValid_prime [2, 3, 49081001] ⟨294486007, 3, [(2, 1), (3, 1), (49081001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49081001
  · decide +kernel

theorem prime_404982499 : Nat.Prime 404982499 := by
  apply nodeValid_prime [2, 3, 67497083] ⟨404982499, 2, [(2, 1), (3, 1), (67497083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67497083
  · decide +kernel

theorem prime_475375057 : Nat.Prime 475375057 := by
  apply nodeValid_prime [2, 3, 13, 457, 1667] ⟨475375057, 5, [(2, 4), (3, 1), (13, 1), (457, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_457
    · exact prime_1667
  · decide +kernel

theorem prime_503908333 : Nat.Prime 503908333 := by
  apply nodeValid_prime [2, 3, 193, 217577] ⟨503908333, 13, [(2, 2), (3, 1), (193, 1), (217577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_217577
  · decide +kernel

theorem prime_646893167 : Nat.Prime 646893167 := by
  apply nodeValid_prime [2, 61, 5302403] ⟨646893167, 5, [(2, 1), (61, 1), (5302403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_5302403
  · decide +kernel

theorem prime_750133393 : Nat.Prime 750133393 := by
  apply nodeValid_prime [2, 3, 15627779] ⟨750133393, 5, [(2, 4), (3, 1), (15627779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15627779
  · decide +kernel

theorem prime_1027910599 : Nat.Prime 1027910599 := by
  apply nodeValid_prime [2, 3, 11, 13, 439, 2729] ⟨1027910599, 6, [(2, 1), (3, 1), (11, 1), (13, 1), (439, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_439
    · exact prime_2729
  · decide +kernel

theorem prime_1231115309 : Nat.Prime 1231115309 := by
  apply nodeValid_prime [2, 29, 10613063] ⟨1231115309, 2, [(2, 2), (29, 1), (10613063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_10613063
  · decide +kernel

theorem prime_1670847917 : Nat.Prime 1670847917 := by
  apply nodeValid_prime [2, 19, 1847, 11903] ⟨1670847917, 2, [(2, 2), (19, 1), (1847, 1), (11903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1847
    · exact prime_11903
  · decide +kernel

theorem prime_2716364951 : Nat.Prime 2716364951 := by
  apply nodeValid_prime [2, 5, 13, 4179023] ⟨2716364951, 17, [(2, 1), (5, 2), (13, 1), (4179023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4179023
  · decide +kernel

theorem prime_4111642397 : Nat.Prime 4111642397 := by
  apply nodeValid_prime [2, 1027910599] ⟨4111642397, 2, [(2, 2), (1027910599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1027910599
  · decide +kernel

theorem prime_5039083331 : Nat.Prime 5039083331 := by
  apply nodeValid_prime [2, 5, 503908333] ⟨5039083331, 6, [(2, 1), (5, 1), (503908333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_503908333
  · decide +kernel

theorem prime_5432729903 : Nat.Prime 5432729903 := by
  apply nodeValid_prime [2, 2716364951] ⟨5432729903, 5, [(2, 1), (2716364951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2716364951
  · decide +kernel

theorem prime_10865459807 : Nat.Prime 10865459807 := by
  apply nodeValid_prime [2, 5432729903] ⟨10865459807, 5, [(2, 1), (5432729903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5432729903
  · decide +kernel

theorem prime_13331220061 : Nat.Prime 13331220061 := by
  apply nodeValid_prime [2, 3, 5, 47, 739, 6397] ⟨13331220061, 6, [(2, 2), (3, 1), (5, 1), (47, 1), (739, 1), (6397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_739
    · exact prime_6397
  · decide +kernel

theorem prime_20071138333 : Nat.Prime 20071138333 := by
  apply nodeValid_prime [2, 3, 7, 17, 2007917] ⟨20071138333, 5, [(2, 2), (3, 1), (7, 2), (17, 1), (2007917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_2007917
  · decide +kernel

theorem prime_33729405727 : Nat.Prime 33729405727 := by
  apply nodeValid_prime [2, 3, 31, 983, 184477] ⟨33729405727, 3, [(2, 1), (3, 1), (31, 1), (983, 1), (184477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_983
    · exact prime_184477
  · decide +kernel

theorem prime_52328784199 : Nat.Prime 52328784199 := by
  apply nodeValid_prime [2, 3, 2707, 3221819] ⟨52328784199, 6, [(2, 1), (3, 1), (2707, 1), (3221819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2707
    · exact prime_3221819
  · decide +kernel

theorem prime_58168771537 : Nat.Prime 58168771537 := by
  apply nodeValid_prime [2, 3, 1129, 1073383] ⟨58168771537, 5, [(2, 4), (3, 1), (1129, 1), (1073383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1129
    · exact prime_1073383
  · decide +kernel

theorem prime_58401846361 : Nat.Prime 58401846361 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 37, 30661] ⟨58401846361, 7, [(2, 3), (3, 2), (5, 1), (11, 1), (13, 1), (37, 1), (30661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_37
    · exact prime_30661
  · decide +kernel

theorem prime_58713599047 : Nat.Prime 58713599047 := by
  apply nodeValid_prime [2, 3, 31, 449, 703039] ⟨58713599047, 5, [(2, 1), (3, 1), (31, 1), (449, 1), (703039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_449
    · exact prime_703039
  · decide +kernel

theorem prime_76939362023 : Nat.Prime 76939362023 := by
  apply nodeValid_prime [2, 2521, 15259691] ⟨76939362023, 5, [(2, 1), (2521, 1), (15259691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2521
    · exact prime_15259691
  · decide +kernel

theorem prime_78493176361 : Nat.Prime 78493176361 := by
  apply nodeValid_prime [2, 3, 5, 83, 151, 1933] ⟨78493176361, 11, [(2, 3), (3, 4), (5, 1), (83, 1), (151, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_151
    · exact prime_1933
  · decide +kernel

theorem prime_114792846017 : Nat.Prime 114792846017 := by
  apply nodeValid_prime [2, 251, 7145969] ⟨114792846017, 3, [(2, 6), (251, 1), (7145969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_7145969
  · decide +kernel

theorem prime_116027486759 : Nat.Prime 116027486759 := by
  apply nodeValid_prime [2, 197, 294486007] ⟨116027486759, 7, [(2, 1), (197, 1), (294486007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_294486007
  · decide +kernel

theorem prime_230509571711 : Nat.Prime 230509571711 := by
  apply nodeValid_prime [2, 5, 11, 173, 12112957] ⟨230509571711, 11, [(2, 1), (5, 1), (11, 1), (173, 1), (12112957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_173
    · exact prime_12112957
  · decide +kernel

theorem prime_458556561761 : Nat.Prime 458556561761 := by
  apply nodeValid_prime [2, 5, 11, 79, 3298019] ⟨458556561761, 6, [(2, 5), (5, 1), (11, 1), (79, 1), (3298019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_79
    · exact prime_3298019
  · decide +kernel

theorem prime_461019143423 : Nat.Prime 461019143423 := by
  apply nodeValid_prime [2, 230509571711] ⟨461019143423, 5, [(2, 1), (230509571711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_230509571711
  · decide +kernel

theorem prime_917113122703 : Nat.Prime 917113122703 := by
  apply nodeValid_prime [2, 3, 7, 29, 617, 406789] ⟨917113122703, 3, [(2, 1), (3, 2), (7, 1), (29, 1), (617, 1), (406789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_617
    · exact prime_406789
  · decide +kernel

theorem prime_917113123523 : Nat.Prime 917113123523 := by
  apply nodeValid_prime [2, 458556561761] ⟨917113123523, 2, [(2, 1), (458556561761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_458556561761
  · decide +kernel

theorem prime_917113166243 : Nat.Prime 917113166243 := by
  apply nodeValid_prime [2, 7, 13, 5039083331] ⟨917113166243, 2, [(2, 1), (7, 1), (13, 1), (5039083331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_5039083331
  · decide +kernel

theorem prime_918342768137 : Nat.Prime 918342768137 := by
  apply nodeValid_prime [2, 114792846017] ⟨918342768137, 3, [(2, 3), (114792846017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_114792846017
  · decide +kernel

theorem prime_918342772723 : Nat.Prime 918342772723 := by
  apply nodeValid_prime [2, 3, 499, 677, 50341] ⟨918342772723, 3, [(2, 1), (3, 3), (499, 1), (677, 1), (50341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_499
    · exact prime_677
    · exact prime_50341
  · decide +kernel

theorem prime_918342773911 : Nat.Prime 918342773911 := by
  apply nodeValid_prime [2, 3, 5, 83, 4553239] ⟨918342773911, 21, [(2, 1), (3, 5), (5, 1), (83, 1), (4553239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_4553239
  · decide +kernel

theorem prime_919573477327 : Nat.Prime 919573477327 := by
  apply nodeValid_prime [2, 3, 7, 83, 347, 84467] ⟨919573477327, 12, [(2, 1), (3, 3), (7, 1), (83, 1), (347, 1), (84467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_347
    · exact prime_84467
  · decide +kernel

theorem prime_919573487029 : Nat.Prime 919573487029 := by
  apply nodeValid_prime [2, 3, 7, 35593, 102523] ⟨919573487029, 2, [(2, 2), (3, 2), (7, 1), (35593, 1), (102523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_35593
    · exact prime_102523
  · decide +kernel

theorem prime_920805333163 : Nat.Prime 920805333163 := by
  apply nodeValid_prime [2, 3, 11, 13, 37, 313, 92669] ⟨920805333163, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (37, 1), (313, 1), (92669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_37
    · exact prime_313
    · exact prime_92669
  · decide +kernel

theorem prime_920805342673 : Nat.Prime 920805342673 := by
  apply nodeValid_prime [2, 3, 19, 29, 61, 19681] ⟨920805342673, 5, [(2, 4), (3, 1), (19, 1), (29, 2), (61, 1), (19681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_61
    · exact prime_19681
  · decide +kernel

theorem prime_920805343093 : Nat.Prime 920805343093 := by
  apply nodeValid_prime [2, 3, 1063, 8020673] ⟨920805343093, 2, [(2, 2), (3, 3), (1063, 1), (8020673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1063
    · exact prime_8020673
  · decide +kernel

theorem prime_922038286847 : Nat.Prime 922038286847 := by
  apply nodeValid_prime [2, 461019143423] ⟨922038286847, 5, [(2, 1), (461019143423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_461019143423
  · decide +kernel

theorem prime_922038293789 : Nat.Prime 922038293789 := by
  apply nodeValid_prime [2, 19, 137, 1249, 70901] ⟨922038293789, 2, [(2, 2), (19, 1), (137, 1), (1249, 1), (70901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_137
    · exact prime_1249
    · exact prime_70901
  · decide +kernel

theorem prime_923272343321 : Nat.Prime 923272343321 := by
  apply nodeValid_prime [2, 5, 149, 2377, 65171] ⟨923272343321, 3, [(2, 3), (5, 1), (149, 1), (2377, 1), (65171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_2377
    · exact prime_65171
  · decide +kernel

theorem prime_923272344277 : Nat.Prime 923272344277 := by
  apply nodeValid_prime [2, 3, 76939362023] ⟨923272344277, 2, [(2, 2), (3, 1), (76939362023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76939362023
  · decide +kernel

theorem prime_923272363319 : Nat.Prime 923272363319 := by
  apply nodeValid_prime [2, 23, 20071138333] ⟨923272363319, 11, [(2, 1), (23, 1), (20071138333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_20071138333
  · decide +kernel

theorem prime_924507553091 : Nat.Prime 924507553091 := by
  apply nodeValid_prime [2, 5, 11, 47, 16256507] ⟨924507553091, 6, [(2, 1), (5, 1), (11, 2), (47, 1), (16256507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
    · exact prime_16256507
  · decide +kernel

theorem prime_924507554717 : Nat.Prime 924507554717 := by
  apply nodeValid_prime [2, 37, 168828991] ⟨924507554717, 2, [(2, 2), (37, 2), (168828991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_168828991
  · decide +kernel

theorem prime_924507560087 : Nat.Prime 924507560087 := by
  apply nodeValid_prime [2, 11, 163, 257810251] ⟨924507560087, 10, [(2, 1), (11, 1), (163, 1), (257810251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_163
    · exact prime_257810251
  · decide +kernel

theorem prime_925743879589 : Nat.Prime 925743879589 := by
  apply nodeValid_prime [2, 3, 11, 10061, 697069] ⟨925743879589, 2, [(2, 2), (3, 1), (11, 1), (10061, 1), (697069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_10061
    · exact prime_697069
  · decide +kernel

theorem prime_925743879787 : Nat.Prime 925743879787 := by
  apply nodeValid_prime [2, 3, 11, 19, 97, 691877] ⟨925743879787, 11, [(2, 1), (3, 1), (11, 2), (19, 1), (97, 1), (691877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_97
    · exact prime_691877
  · decide +kernel

theorem prime_925743880541 : Nat.Prime 925743880541 := by
  apply nodeValid_prime [2, 5, 4937, 9375571] ⟨925743880541, 2, [(2, 2), (5, 1), (4937, 1), (9375571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4937
    · exact prime_9375571
  · decide +kernel

theorem prime_926981325499 : Nat.Prime 926981325499 := by
  apply nodeValid_prime [2, 3, 227, 373, 1824673] ⟨926981325499, 2, [(2, 1), (3, 1), (227, 1), (373, 1), (1824673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_373
    · exact prime_1824673
  · decide +kernel

theorem prime_926981361151 : Nat.Prime 926981361151 := by
  apply nodeValid_prime [2, 3, 5, 13, 475375057] ⟨926981361151, 12, [(2, 1), (3, 1), (5, 2), (13, 1), (475375057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_475375057
  · decide +kernel

theorem prime_926981361227 : Nat.Prime 926981361227 := by
  apply nodeValid_prime [2, 3539, 130966567] ⟨926981361227, 2, [(2, 1), (3539, 1), (130966567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3539
    · exact prime_130966567
  · decide +kernel

theorem prime_928219887709 : Nat.Prime 928219887709 := by
  apply nodeValid_prime [2, 3, 191, 404982499] ⟨928219887709, 2, [(2, 2), (3, 1), (191, 1), (404982499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_404982499
  · decide +kernel

theorem prime_928219894013 : Nat.Prime 928219894013 := by
  apply nodeValid_prime [2, 17, 36887, 370057] ⟨928219894013, 2, [(2, 2), (17, 1), (36887, 1), (370057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_36887
    · exact prime_370057
  · decide +kernel

theorem prime_928219894073 : Nat.Prime 928219894073 := by
  apply nodeValid_prime [2, 116027486759] ⟨928219894073, 3, [(2, 3), (116027486759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_116027486759
  · decide +kernel

theorem prime_929459563511 : Nat.Prime 929459563511 := by
  apply nodeValid_prime [2, 5, 23, 181, 887, 25171] ⟨929459563511, 13, [(2, 1), (5, 1), (23, 1), (181, 1), (887, 1), (25171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_181
    · exact prime_887
    · exact prime_25171
  · decide +kernel

theorem prime_929459563957 : Nat.Prime 929459563957 := by
  apply nodeValid_prime [2, 3, 7, 11, 449, 746777] ⟨929459563957, 2, [(2, 2), (3, 2), (7, 1), (11, 1), (449, 1), (746777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_449
    · exact prime_746777
  · decide +kernel

theorem prime_929459577199 : Nat.Prime 929459577199 := by
  apply nodeValid_prime [2, 3, 59119, 2620307] ⟨929459577199, 6, [(2, 1), (3, 1), (59119, 1), (2620307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59119
    · exact prime_2620307
  · decide +kernel

theorem prime_930700344593 : Nat.Prime 930700344593 := by
  apply nodeValid_prime [2, 58168771537] ⟨930700344593, 3, [(2, 4), (58168771537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58168771537
  · decide +kernel

theorem prime_930700345997 : Nat.Prime 930700345997 := by
  apply nodeValid_prime [2, 31489, 7389091] ⟨930700345997, 2, [(2, 2), (31489, 1), (7389091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31489
    · exact prime_7389091
  · decide +kernel

theorem prime_930700387153 : Nat.Prime 930700387153 := by
  apply nodeValid_prime [2, 3, 23, 173, 1624327] ⟨930700387153, 7, [(2, 4), (3, 2), (23, 1), (173, 1), (1624327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_173
    · exact prime_1624327
  · decide +kernel

theorem prime_931942316693 : Nat.Prime 931942316693 := by
  apply nodeValid_prime [2, 17, 21011, 652279] ⟨931942316693, 2, [(2, 2), (17, 1), (21011, 1), (652279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_21011
    · exact prime_652279
  · decide +kernel

theorem prime_931942319059 : Nat.Prime 931942319059 := by
  apply nodeValid_prime [2, 3, 31123, 1663547] ⟨931942319059, 2, [(2, 1), (3, 2), (31123, 1), (1663547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31123
    · exact prime_1663547
  · decide +kernel

theorem prime_931942320217 : Nat.Prime 931942320217 := by
  apply nodeValid_prime [2, 3, 173021, 224429] ⟨931942320217, 7, [(2, 3), (3, 1), (173021, 1), (224429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173021
    · exact prime_224429
  · decide +kernel

theorem prime_933185371691 : Nat.Prime 933185371691 := by
  apply nodeValid_prime [2, 5, 11, 13, 23, 163, 174067] ⟨933185371691, 6, [(2, 1), (5, 1), (11, 1), (13, 1), (23, 1), (163, 1), (174067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_163
    · exact prime_174067
  · decide +kernel

theorem prime_933185404223 : Nat.Prime 933185404223 := by
  apply nodeValid_prime [2, 379, 1231115309] ⟨933185404223, 5, [(2, 1), (379, 1), (1231115309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_1231115309
  · decide +kernel

theorem prime_933185404271 : Nat.Prime 933185404271 := by
  apply nodeValid_prime [2, 5, 7, 13331220061] ⟨933185404271, 21, [(2, 1), (5, 1), (7, 1), (13331220061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13331220061
  · decide +kernel

theorem prime_934429541777 : Nat.Prime 934429541777 := by
  apply nodeValid_prime [2, 58401846361] ⟨934429541777, 3, [(2, 4), (58401846361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58401846361
  · decide +kernel

theorem prime_934429543403 : Nat.Prime 934429543403 := by
  apply nodeValid_prime [2, 43, 10865459807] ⟨934429543403, 2, [(2, 1), (43, 1), (10865459807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_10865459807
  · decide +kernel

theorem prime_934429544261 : Nat.Prime 934429544261 := by
  apply nodeValid_prime [2, 5, 17, 6271, 438259] ⟨934429544261, 2, [(2, 2), (5, 1), (17, 1), (6271, 1), (438259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_6271
    · exact prime_438259
  · decide +kernel

theorem prime_935674802443 : Nat.Prime 935674802443 := by
  apply nodeValid_prime [2, 3, 32233, 1612693] ⟨935674802443, 2, [(2, 1), (3, 2), (32233, 1), (1612693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32233
    · exact prime_1612693
  · decide +kernel

theorem prime_935674833521 : Nat.Prime 935674833521 := by
  apply nodeValid_prime [2, 5, 7, 1670847917] ⟨935674833521, 3, [(2, 4), (5, 1), (7, 1), (1670847917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1670847917
  · decide +kernel

theorem prime_936921250549 : Nat.Prime 936921250549 := by
  apply nodeValid_prime [2, 3, 887, 29341139] ⟨936921250549, 6, [(2, 2), (3, 2), (887, 1), (29341139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_887
    · exact prime_29341139
  · decide +kernel

theorem prime_936921274097 : Nat.Prime 936921274097 := by
  apply nodeValid_prime [2, 82141, 712891] ⟨936921274097, 3, [(2, 4), (82141, 1), (712891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_82141
    · exact prime_712891
  · decide +kernel

theorem prime_936921275317 : Nat.Prime 936921275317 := by
  apply nodeValid_prime [2, 3, 13, 15013, 133349] ⟨936921275317, 2, [(2, 2), (3, 2), (13, 1), (15013, 1), (133349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_15013
    · exact prime_133349
  · decide +kernel

theorem prime_938168789741 : Nat.Prime 938168789741 := by
  apply nodeValid_prime [2, 5, 7, 13, 23, 22412059] ⟨938168789741, 2, [(2, 2), (5, 1), (7, 1), (13, 1), (23, 1), (22412059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_22412059
  · decide +kernel

theorem prime_938168790127 : Nat.Prime 938168790127 := by
  apply nodeValid_prime [2, 3, 73, 107, 2287, 8753] ⟨938168790127, 5, [(2, 1), (3, 1), (73, 1), (107, 1), (2287, 1), (8753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_107
    · exact prime_2287
    · exact prime_8753
  · decide +kernel

theorem prime_938168794663 : Nat.Prime 938168794663 := by
  apply nodeValid_prime [2, 3, 11, 17, 23, 36354677] ⟨938168794663, 5, [(2, 1), (3, 1), (11, 1), (17, 1), (23, 1), (36354677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_23
    · exact prime_36354677
  · decide +kernel

theorem prime_939417467377 : Nat.Prime 939417467377 := by
  apply nodeValid_prime [2, 3, 23, 1697, 501427] ⟨939417467377, 15, [(2, 4), (3, 1), (23, 1), (1697, 1), (501427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1697
    · exact prime_501427
  · decide +kernel

theorem prime_939417584489 : Nat.Prime 939417584489 := by
  apply nodeValid_prime [2, 31, 25673, 147547] ⟨939417584489, 3, [(2, 3), (31, 1), (25673, 1), (147547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_25673
    · exact prime_147547
  · decide +kernel

theorem prime_939417584753 : Nat.Prime 939417584753 := by
  apply nodeValid_prime [2, 58713599047] ⟨939417584753, 3, [(2, 4), (58713599047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58713599047
  · decide +kernel

theorem prime_940667267777 : Nat.Prime 940667267777 := by
  apply nodeValid_prime [2, 65687, 223757] ⟨940667267777, 3, [(2, 6), (65687, 1), (223757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_65687
    · exact prime_223757
  · decide +kernel

theorem prime_940667274823 : Nat.Prime 940667274823 := by
  apply nodeValid_prime [2, 3, 11, 19, 750133393] ⟨940667274823, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (750133393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_750133393
  · decide +kernel

theorem prime_940667275033 : Nat.Prime 940667275033 := by
  apply nodeValid_prime [2, 3, 181361, 216113] ⟨940667275033, 5, [(2, 3), (3, 1), (181361, 1), (216113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181361
    · exact prime_216113
  · decide +kernel

theorem prime_941918115583 : Nat.Prime 941918115583 := by
  apply nodeValid_prime [2, 3, 52328784199] ⟨941918115583, 3, [(2, 1), (3, 2), (52328784199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52328784199
  · decide +kernel

theorem prime_941918116333 : Nat.Prime 941918116333 := by
  apply nodeValid_prime [2, 3, 78493176361] ⟨941918116333, 2, [(2, 2), (3, 1), (78493176361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_78493176361
  · decide +kernel

theorem prime_941918190337 : Nat.Prime 941918190337 := by
  apply nodeValid_prime [2, 3, 3617, 113027] ⟨941918190337, 5, [(2, 8), (3, 2), (3617, 1), (113027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3617
    · exact prime_113027
  · decide +kernel

theorem prime_943170237487 : Nat.Prime 943170237487 := by
  apply nodeValid_prime [2, 3, 646893167] ⟨943170237487, 3, [(2, 1), (3, 6), (646893167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_646893167
  · decide +kernel

theorem prime_943170238487 : Nat.Prime 943170238487 := by
  apply nodeValid_prime [2, 7, 71, 135551917] ⟨943170238487, 5, [(2, 1), (7, 2), (71, 1), (135551917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_135551917
  · decide +kernel

theorem prime_943170242243 : Nat.Prime 943170242243 := by
  apply nodeValid_prime [2, 13931, 33851491] ⟨943170242243, 2, [(2, 1), (13931, 1), (33851491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13931
    · exact prime_33851491
  · decide +kernel

theorem prime_944423360357 : Nat.Prime 944423360357 := by
  apply nodeValid_prime [2, 7, 33729405727] ⟨944423360357, 2, [(2, 2), (7, 1), (33729405727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_33729405727
  · decide +kernel

theorem prime_944423363711 : Nat.Prime 944423363711 := by
  apply nodeValid_prime [2, 5, 2741, 34455431] ⟨944423363711, 7, [(2, 1), (5, 1), (2741, 1), (34455431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2741
    · exact prime_34455431
  · decide +kernel

theorem prime_944423416843 : Nat.Prime 944423416843 := by
  apply nodeValid_prime [2, 3, 1987, 79216861] ⟨944423416843, 5, [(2, 1), (3, 1), (1987, 1), (79216861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1987
    · exact prime_79216861
  · decide +kernel

theorem prime_945677717041 : Nat.Prime 945677717041 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 2411, 10151] ⟨945677717041, 22, [(2, 4), (3, 1), (5, 1), (7, 1), (23, 1), (2411, 1), (10151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_2411
    · exact prime_10151
  · decide +kernel

theorem prime_945677749123 : Nat.Prime 945677749123 := by
  apply nodeValid_prime [2, 3, 73, 4561, 157793] ⟨945677749123, 3, [(2, 1), (3, 2), (73, 1), (4561, 1), (157793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_4561
    · exact prime_157793
  · decide +kernel

theorem prime_945677751311 : Nat.Prime 945677751311 := by
  apply nodeValid_prime [2, 5, 23, 4111642397] ⟨945677751311, 13, [(2, 1), (5, 1), (23, 1), (4111642397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_4111642397
  · decide +kernel

theorem prime_946933140689 : Nat.Prime 946933140689 := by
  apply nodeValid_prime [2, 19, 5419, 574813] ⟨946933140689, 3, [(2, 4), (19, 1), (5419, 1), (574813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5419
    · exact prime_574813
  · decide +kernel

theorem prime_946933159021 : Nat.Prime 946933159021 := by
  apply nodeValid_prime [2, 3, 5, 179, 277, 318299] ⟨946933159021, 10, [(2, 2), (3, 1), (5, 1), (179, 1), (277, 1), (318299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_277
    · exact prime_318299
  · decide +kernel

theorem prime_946933159633 : Nat.Prime 946933159633 := by
  apply nodeValid_prime [2, 3, 743, 26551513] ⟨946933159633, 5, [(2, 4), (3, 1), (743, 1), (26551513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_743
    · exact prime_26551513
  · decide +kernel

end Sude.Lucas.Generated
