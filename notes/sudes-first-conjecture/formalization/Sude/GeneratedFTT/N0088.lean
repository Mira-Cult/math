import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0085

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6217 : Nat.Prime 6217 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨6217, 5, [(2, 3), (3, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_9749 : Nat.Prime 9749 := by
  apply nodeValid_prime [2, 2437] ⟨9749, 2, [(2, 2), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2437
  · decide +kernel

theorem prime_15919 : Nat.Prime 15919 := by
  apply nodeValid_prime [2, 3, 7, 379] ⟨15919, 6, [(2, 1), (3, 1), (7, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_379
  · decide +kernel

theorem prime_17203 : Nat.Prime 17203 := by
  apply nodeValid_prime [2, 3, 47, 61] ⟨17203, 2, [(2, 1), (3, 1), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_19751 : Nat.Prime 19751 := by
  apply nodeValid_prime [2, 5, 79] ⟨19751, 7, [(2, 1), (5, 3), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_19961 : Nat.Prime 19961 := by
  apply nodeValid_prime [2, 5, 499] ⟨19961, 6, [(2, 3), (5, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_499
  · decide +kernel

theorem prime_20161 : Nat.Prime 20161 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨20161, 13, [(2, 6), (3, 2), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_23689 : Nat.Prime 23689 := by
  apply nodeValid_prime [2, 3, 7, 47] ⟨23689, 11, [(2, 3), (3, 2), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_23893 : Nat.Prime 23893 := by
  apply nodeValid_prime [2, 3, 11, 181] ⟨23893, 5, [(2, 2), (3, 1), (11, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_181
  · decide +kernel

theorem prime_23981 : Nat.Prime 23981 := by
  apply nodeValid_prime [2, 5, 11, 109] ⟨23981, 3, [(2, 2), (5, 1), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_27539 : Nat.Prime 27539 := by
  apply nodeValid_prime [2, 7, 281] ⟨27539, 2, [(2, 1), (7, 2), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_281
  · decide +kernel

theorem prime_32257 : Nat.Prime 32257 := by
  apply nodeValid_prime [2, 3, 7] ⟨32257, 15, [(2, 9), (3, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_33037 : Nat.Prime 33037 := by
  apply nodeValid_prime [2, 3, 2753] ⟨33037, 2, [(2, 2), (3, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2753
  · decide +kernel

theorem prime_38707 : Nat.Prime 38707 := by
  apply nodeValid_prime [2, 3, 6451] ⟨38707, 2, [(2, 1), (3, 1), (6451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6451
  · decide +kernel

theorem prime_39503 : Nat.Prime 39503 := by
  apply nodeValid_prime [2, 19751] ⟨39503, 5, [(2, 1), (19751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19751
  · decide +kernel

theorem prime_41621 : Nat.Prime 41621 := by
  apply nodeValid_prime [2, 5, 2081] ⟨41621, 3, [(2, 2), (5, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2081
  · decide +kernel

theorem prime_45841 : Nat.Prime 45841 := by
  apply nodeValid_prime [2, 3, 5, 191] ⟨45841, 7, [(2, 4), (3, 1), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_46187 : Nat.Prime 46187 := by
  apply nodeValid_prime [2, 7, 3299] ⟨46187, 2, [(2, 1), (7, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3299
  · decide +kernel

theorem prime_46901 : Nat.Prime 46901 := by
  apply nodeValid_prime [2, 5, 7, 67] ⟨46901, 11, [(2, 2), (5, 2), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_52313 : Nat.Prime 52313 := by
  apply nodeValid_prime [2, 13, 503] ⟨52313, 3, [(2, 3), (13, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_503
  · decide +kernel

theorem prime_58337 : Nat.Prime 58337 := by
  apply nodeValid_prime [2, 1823] ⟨58337, 3, [(2, 5), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1823
  · decide +kernel

theorem prime_69677 : Nat.Prime 69677 := by
  apply nodeValid_prime [2, 17419] ⟨69677, 2, [(2, 2), (17419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17419
  · decide +kernel

theorem prime_73727 : Nat.Prime 73727 := by
  apply nodeValid_prime [2, 191, 193] ⟨73727, 5, [(2, 1), (191, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_193
  · decide +kernel

theorem prime_83231 : Nat.Prime 83231 := by
  apply nodeValid_prime [2, 5, 7, 29, 41] ⟨83231, 7, [(2, 1), (5, 1), (7, 1), (29, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_41
  · decide +kernel

theorem prime_83243 : Nat.Prime 83243 := by
  apply nodeValid_prime [2, 41621] ⟨83243, 2, [(2, 1), (41621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41621
  · decide +kernel

theorem prime_103951 : Nat.Prime 103951 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨103951, 6, [(2, 1), (3, 3), (5, 2), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_107077 : Nat.Prime 107077 := by
  apply nodeValid_prime [2, 3, 8923] ⟨107077, 2, [(2, 2), (3, 1), (8923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8923
  · decide +kernel

theorem prime_141511 : Nat.Prime 141511 := by
  apply nodeValid_prime [2, 3, 5, 53, 89] ⟨141511, 3, [(2, 1), (3, 1), (5, 1), (53, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_89
  · decide +kernel

theorem prime_166781 : Nat.Prime 166781 := by
  apply nodeValid_prime [2, 5, 31, 269] ⟨166781, 2, [(2, 2), (5, 1), (31, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_269
  · decide +kernel

theorem prime_188827 : Nat.Prime 188827 := by
  apply nodeValid_prime [2, 3, 11, 2861] ⟨188827, 3, [(2, 1), (3, 1), (11, 1), (2861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2861
  · decide +kernel

theorem prime_207079 : Nat.Prime 207079 := by
  apply nodeValid_prime [2, 3, 34513] ⟨207079, 6, [(2, 1), (3, 1), (34513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34513
  · decide +kernel

theorem prime_238181 : Nat.Prime 238181 := by
  apply nodeValid_prime [2, 5, 11909] ⟨238181, 2, [(2, 2), (5, 1), (11909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11909
  · decide +kernel

theorem prime_242521 : Nat.Prime 242521 := by
  apply nodeValid_prime [2, 3, 5, 43, 47] ⟨242521, 14, [(2, 3), (3, 1), (5, 1), (43, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_47
  · decide +kernel

theorem prime_313879 : Nat.Prime 313879 := by
  apply nodeValid_prime [2, 3, 52313] ⟨313879, 3, [(2, 1), (3, 1), (52313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52313
  · decide +kernel

theorem prime_317701 : Nat.Prime 317701 := by
  apply nodeValid_prime [2, 3, 5, 353] ⟨317701, 2, [(2, 2), (3, 2), (5, 2), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
  · decide +kernel

theorem prime_319201 : Nat.Prime 319201 := by
  apply nodeValid_prime [2, 3, 5, 7, 19] ⟨319201, 23, [(2, 5), (3, 1), (5, 2), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_326701 : Nat.Prime 326701 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨326701, 13, [(2, 2), (3, 3), (5, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_330469 : Nat.Prime 330469 := by
  apply nodeValid_prime [2, 3, 27539] ⟨330469, 2, [(2, 2), (3, 1), (27539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27539
  · decide +kernel

theorem prime_333563 : Nat.Prime 333563 := by
  apply nodeValid_prime [2, 166781] ⟨333563, 2, [(2, 1), (166781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_166781
  · decide +kernel

theorem prime_339727 : Nat.Prime 339727 := by
  apply nodeValid_prime [2, 3, 41, 1381] ⟨339727, 5, [(2, 1), (3, 1), (41, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1381
  · decide +kernel

theorem prime_367181 : Nat.Prime 367181 := by
  apply nodeValid_prime [2, 5, 11, 1669] ⟨367181, 2, [(2, 2), (5, 1), (11, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1669
  · decide +kernel

theorem prime_372451 : Nat.Prime 372451 := by
  apply nodeValid_prime [2, 3, 5, 13, 191] ⟨372451, 7, [(2, 1), (3, 1), (5, 2), (13, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_191
  · decide +kernel

theorem prime_390967 : Nat.Prime 390967 := by
  apply nodeValid_prime [2, 3, 17, 3833] ⟨390967, 3, [(2, 1), (3, 1), (17, 1), (3833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3833
  · decide +kernel

theorem prime_406591 : Nat.Prime 406591 := by
  apply nodeValid_prime [2, 3, 5, 13553] ⟨406591, 6, [(2, 1), (3, 1), (5, 1), (13553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13553
  · decide +kernel

theorem prime_431659 : Nat.Prime 431659 := by
  apply nodeValid_prime [2, 3, 23981] ⟨431659, 3, [(2, 1), (3, 2), (23981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23981
  · decide +kernel

theorem prime_482803 : Nat.Prime 482803 := by
  apply nodeValid_prime [2, 3, 67, 1201] ⟨482803, 2, [(2, 1), (3, 1), (67, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1201
  · decide +kernel

theorem prime_558937 : Nat.Prime 558937 := by
  apply nodeValid_prime [2, 3, 7, 1109] ⟨558937, 10, [(2, 3), (3, 2), (7, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1109
  · decide +kernel

theorem prime_689467 : Nat.Prime 689467 := by
  apply nodeValid_prime [2, 3, 151, 761] ⟨689467, 2, [(2, 1), (3, 1), (151, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_761
  · decide +kernel

theorem prime_755273 : Nat.Prime 755273 := by
  apply nodeValid_prime [2, 7, 13487] ⟨755273, 3, [(2, 3), (7, 1), (13487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13487
  · decide +kernel

theorem prime_757753 : Nat.Prime 757753 := by
  apply nodeValid_prime [2, 3, 31573] ⟨757753, 5, [(2, 3), (3, 1), (31573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31573
  · decide +kernel

theorem prime_795877 : Nat.Prime 795877 := by
  apply nodeValid_prime [2, 3, 29, 2287] ⟨795877, 6, [(2, 2), (3, 1), (29, 1), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2287
  · decide +kernel

theorem prime_891551 : Nat.Prime 891551 := by
  apply nodeValid_prime [2, 5, 11, 1621] ⟨891551, 13, [(2, 1), (5, 2), (11, 1), (1621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1621
  · decide +kernel

theorem prime_1074371 : Nat.Prime 1074371 := by
  apply nodeValid_prime [2, 5, 11, 9767] ⟨1074371, 6, [(2, 1), (5, 1), (11, 1), (9767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_9767
  · decide +kernel

theorem prime_1375219 : Nat.Prime 1375219 := by
  apply nodeValid_prime [2, 3, 13, 653] ⟨1375219, 2, [(2, 1), (3, 4), (13, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_653
  · decide +kernel

theorem prime_1412641 : Nat.Prime 1412641 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨1412641, 7, [(2, 5), (3, 4), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_1547893 : Nat.Prime 1547893 := by
  apply nodeValid_prime [2, 3, 19, 31, 73] ⟨1547893, 2, [(2, 2), (3, 2), (19, 1), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_1672441 : Nat.Prime 1672441 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 181] ⟨1672441, 23, [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_181
  · decide +kernel

theorem prime_1769171 : Nat.Prime 1769171 := by
  apply nodeValid_prime [2, 5, 13, 31, 439] ⟨1769171, 2, [(2, 1), (5, 1), (13, 1), (31, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_439
  · decide +kernel

theorem prime_2928209 : Nat.Prime 2928209 := by
  apply nodeValid_prime [2, 197, 929] ⟨2928209, 3, [(2, 4), (197, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_929
  · decide +kernel

theorem prime_3531677 : Nat.Prime 3531677 := by
  apply nodeValid_prime [2, 43, 20533] ⟨3531677, 2, [(2, 2), (43, 1), (20533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_20533
  · decide +kernel

theorem prime_3599737 : Nat.Prime 3599737 := by
  apply nodeValid_prime [2, 3, 7, 3061] ⟨3599737, 5, [(2, 3), (3, 1), (7, 2), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3061
  · decide +kernel

theorem prime_3707111 : Nat.Prime 3707111 := by
  apply nodeValid_prime [2, 5, 11, 67, 503] ⟨3707111, 7, [(2, 1), (5, 1), (11, 1), (67, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_67
    · exact prime_503
  · decide +kernel

theorem prime_5127299 : Nat.Prime 5127299 := by
  apply nodeValid_prime [2, 11, 23, 10133] ⟨5127299, 2, [(2, 1), (11, 1), (23, 1), (10133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_10133
  · decide +kernel

theorem prime_5636791 : Nat.Prime 5636791 := by
  apply nodeValid_prime [2, 3, 5, 6959] ⟨5636791, 3, [(2, 1), (3, 4), (5, 1), (6959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6959
  · decide +kernel

theorem prime_5750707 : Nat.Prime 5750707 := by
  apply nodeValid_prime [2, 3, 13, 73727] ⟨5750707, 2, [(2, 1), (3, 1), (13, 1), (73727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73727
  · decide +kernel

theorem prime_6167101 : Nat.Prime 6167101 := by
  apply nodeValid_prime [2, 3, 5, 61, 337] ⟨6167101, 2, [(2, 2), (3, 1), (5, 2), (61, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_337
  · decide +kernel

theorem prime_6564457 : Nat.Prime 6564457 := by
  apply nodeValid_prime [2, 3, 30391] ⟨6564457, 5, [(2, 3), (3, 3), (30391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30391
  · decide +kernel

theorem prime_7145951 : Nat.Prime 7145951 := by
  apply nodeValid_prime [2, 5, 7, 17, 1201] ⟨7145951, 7, [(2, 1), (5, 2), (7, 1), (17, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_1201
  · decide +kernel

theorem prime_8382937 : Nat.Prime 8382937 := by
  apply nodeValid_prime [2, 3, 43, 8123] ⟨8382937, 5, [(2, 3), (3, 1), (43, 1), (8123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_8123
  · decide +kernel

theorem prime_8961401 : Nat.Prime 8961401 := by
  apply nodeValid_prime [2, 5, 7, 37, 173] ⟨8961401, 3, [(2, 3), (5, 2), (7, 1), (37, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_173
  · decide +kernel

theorem prime_10754837 : Nat.Prime 10754837 := by
  apply nodeValid_prime [2, 19, 141511] ⟨10754837, 2, [(2, 2), (19, 1), (141511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_141511
  · decide +kernel

theorem prime_11085691 : Nat.Prime 11085691 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 4799] ⟨11085691, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (4799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_4799
  · decide +kernel

theorem prime_12238859 : Nat.Prime 12238859 := by
  apply nodeValid_prime [2, 181, 33809] ⟨12238859, 2, [(2, 1), (181, 1), (33809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_33809
  · decide +kernel

theorem prime_16047919 : Nat.Prime 16047919 := by
  apply nodeValid_prime [2, 3, 891551] ⟨16047919, 3, [(2, 1), (3, 2), (891551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_891551
  · decide +kernel

theorem prime_19069381 : Nat.Prime 19069381 := by
  apply nodeValid_prime [2, 3, 5, 11, 9631] ⟨19069381, 2, [(2, 2), (3, 2), (5, 1), (11, 1), (9631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_9631
  · decide +kernel

theorem prime_25468039 : Nat.Prime 25468039 := by
  apply nodeValid_prime [2, 3, 23, 227, 271] ⟨25468039, 6, [(2, 1), (3, 2), (23, 1), (227, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_227
    · exact prime_271
  · decide +kernel

theorem prime_25763603 : Nat.Prime 25763603 := by
  apply nodeValid_prime [2, 17, 757753] ⟨25763603, 2, [(2, 1), (17, 1), (757753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_757753
  · decide +kernel

theorem prime_26816473 : Nat.Prime 26816473 := by
  apply nodeValid_prime [2, 3, 372451] ⟨26816473, 5, [(2, 3), (3, 2), (372451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_372451
  · decide +kernel

theorem prime_31715483 : Nat.Prime 31715483 := by
  apply nodeValid_prime [2, 23, 689467] ⟨31715483, 2, [(2, 1), (23, 1), (689467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_689467
  · decide +kernel

theorem prime_36133679 : Nat.Prime 36133679 := by
  apply nodeValid_prime [2, 7, 52673] ⟨36133679, 7, [(2, 1), (7, 3), (52673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_52673
  · decide +kernel

theorem prime_36186239 : Nat.Prime 36186239 := by
  apply nodeValid_prime [2, 11, 31, 97, 547] ⟨36186239, 11, [(2, 1), (11, 1), (31, 1), (97, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_97
    · exact prime_547
  · decide +kernel

theorem prime_41301131 : Nat.Prime 41301131 := by
  apply nodeValid_prime [2, 5, 13, 317701] ⟨41301131, 6, [(2, 1), (5, 1), (13, 1), (317701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_317701
  · decide +kernel

theorem prime_61989289 : Nat.Prime 61989289 := by
  apply nodeValid_prime [2, 3, 709, 3643] ⟨61989289, 13, [(2, 3), (3, 1), (709, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_709
    · exact prime_3643
  · decide +kernel

theorem prime_71691209 : Nat.Prime 71691209 := by
  apply nodeValid_prime [2, 8961401] ⟨71691209, 3, [(2, 3), (8961401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8961401
  · decide +kernel

theorem prime_92011313 : Nat.Prime 92011313 := by
  apply nodeValid_prime [2, 5750707] ⟨92011313, 3, [(2, 4), (5750707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5750707
  · decide +kernel

theorem prime_101918101 : Nat.Prime 101918101 := by
  apply nodeValid_prime [2, 3, 5, 339727] ⟨101918101, 7, [(2, 2), (3, 1), (5, 2), (339727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_339727
  · decide +kernel

theorem prime_102911491 : Nat.Prime 102911491 := by
  apply nodeValid_prime [2, 3, 5, 11, 103951] ⟨102911491, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (103951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_103951
  · decide +kernel

theorem prime_103544971 : Nat.Prime 103544971 := by
  apply nodeValid_prime [2, 3, 5, 107, 32257] ⟨103544971, 3, [(2, 1), (3, 1), (5, 1), (107, 1), (32257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
    · exact prime_32257
  · decide +kernel

theorem prime_106938037 : Nat.Prime 106938037 := by
  apply nodeValid_prime [2, 3, 953, 1039] ⟨106938037, 11, [(2, 2), (3, 3), (953, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_953
    · exact prime_1039
  · decide +kernel

theorem prime_115925039 : Nat.Prime 115925039 := by
  apply nodeValid_prime [2, 239, 242521] ⟨115925039, 19, [(2, 1), (239, 1), (242521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_242521
  · decide +kernel

theorem prime_158776687 : Nat.Prime 158776687 := by
  apply nodeValid_prime [2, 3, 326701] ⟨158776687, 3, [(2, 1), (3, 5), (326701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_326701
  · decide +kernel

theorem prime_184022627 : Nat.Prime 184022627 := by
  apply nodeValid_prime [2, 92011313] ⟨184022627, 2, [(2, 1), (92011313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92011313
  · decide +kernel

theorem prime_210111193 : Nat.Prime 210111193 := by
  apply nodeValid_prime [2, 3, 107, 9091] ⟨210111193, 5, [(2, 3), (3, 3), (107, 1), (9091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_9091
  · decide +kernel

theorem prime_324606463 : Nat.Prime 324606463 := by
  apply nodeValid_prime [2, 3, 71, 701, 1087] ⟨324606463, 3, [(2, 1), (3, 1), (71, 1), (701, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_701
    · exact prime_1087
  · decide +kernel

theorem prime_468540991 : Nat.Prime 468540991 := by
  apply nodeValid_prime [2, 3, 5, 37, 46901] ⟨468540991, 6, [(2, 1), (3, 3), (5, 1), (37, 1), (46901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_46901
  · decide +kernel

theorem prime_536250593 : Nat.Prime 536250593 := by
  apply nodeValid_prime [2, 43, 211, 1847] ⟨536250593, 3, [(2, 5), (43, 1), (211, 1), (1847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_211
    · exact prime_1847
  · decide +kernel

theorem prime_620686909 : Nat.Prime 620686909 := by
  apply nodeValid_prime [2, 3, 19, 131, 2309] ⟨620686909, 2, [(2, 2), (3, 3), (19, 1), (131, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_131
    · exact prime_2309
  · decide +kernel

theorem prime_674141563 : Nat.Prime 674141563 := by
  apply nodeValid_prime [2, 3, 17, 31, 23689] ⟨674141563, 5, [(2, 1), (3, 3), (17, 1), (31, 1), (23689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_23689
  · decide +kernel

theorem prime_840110129 : Nat.Prime 840110129 := by
  apply nodeValid_prime [2, 11, 13, 367181] ⟨840110129, 7, [(2, 4), (11, 1), (13, 1), (367181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_367181
  · decide +kernel

theorem prime_1044807013 : Nat.Prime 1044807013 := by
  apply nodeValid_prime [2, 3, 17, 29, 31, 211] ⟨1044807013, 2, [(2, 2), (3, 4), (17, 1), (29, 1), (31, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_31
    · exact prime_211
  · decide +kernel

theorem prime_1072501187 : Nat.Prime 1072501187 := by
  apply nodeValid_prime [2, 536250593] ⟨1072501187, 2, [(2, 1), (536250593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_536250593
  · decide +kernel

theorem prime_1079192291 : Nat.Prime 1079192291 := by
  apply nodeValid_prime [2, 5, 11, 499, 19661] ⟨1079192291, 2, [(2, 1), (5, 1), (11, 1), (499, 1), (19661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_499
    · exact prime_19661
  · decide +kernel

theorem prime_1381590103 : Nat.Prime 1381590103 := by
  apply nodeValid_prime [2, 3, 17, 29, 617, 757] ⟨1381590103, 6, [(2, 1), (3, 1), (17, 1), (29, 1), (617, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_617
    · exact prime_757
  · decide +kernel

theorem prime_2568181339 : Nat.Prime 2568181339 := by
  apply nodeValid_prime [2, 3, 101, 1412641] ⟨2568181339, 2, [(2, 1), (3, 2), (101, 1), (1412641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1412641
  · decide +kernel

theorem prime_2830269049 : Nat.Prime 2830269049 := by
  apply nodeValid_prime [2, 3, 23, 5127299] ⟨2830269049, 14, [(2, 3), (3, 1), (23, 1), (5127299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_5127299
  · decide +kernel

theorem prime_3481160447 : Nat.Prime 3481160447 := by
  apply nodeValid_prime [2, 23, 229, 330469] ⟨3481160447, 5, [(2, 1), (23, 1), (229, 1), (330469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_229
    · exact prime_330469
  · decide +kernel

theorem prime_4763279567 : Nat.Prime 4763279567 := by
  apply nodeValid_prime [2, 4463, 533641] ⟨4763279567, 5, [(2, 1), (4463, 1), (533641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4463
    · exact prime_533641
  · decide +kernel

theorem prime_9785868997 : Nat.Prime 9785868997 := by
  apply nodeValid_prime [2, 3, 1459, 558937] ⟨9785868997, 5, [(2, 2), (3, 1), (1459, 1), (558937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1459
    · exact prime_558937
  · decide +kernel

theorem prime_10942669271 : Nat.Prime 10942669271 := by
  apply nodeValid_prime [2, 5, 13, 1901, 44279] ⟨10942669271, 17, [(2, 1), (5, 1), (13, 1), (1901, 1), (44279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1901
    · exact prime_44279
  · decide +kernel

theorem prime_23979960721 : Nat.Prime 23979960721 := by
  apply nodeValid_prime [2, 3, 5, 31, 1074371] ⟨23979960721, 14, [(2, 4), (3, 2), (5, 1), (31, 1), (1074371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1074371
  · decide +kernel

theorem prime_45739330057 : Nat.Prime 45739330057 := by
  apply nodeValid_prime [2, 3, 7, 41, 67, 33037] ⟨45739330057, 13, [(2, 3), (3, 2), (7, 1), (41, 1), (67, 1), (33037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_67
    · exact prime_33037
  · decide +kernel

theorem prime_58237047521 : Nat.Prime 58237047521 := by
  apply nodeValid_prime [2, 5, 199, 653, 2801] ⟨58237047521, 3, [(2, 5), (5, 1), (199, 1), (653, 1), (2801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_653
    · exact prime_2801
  · decide +kernel

theorem prime_61928626541 : Nat.Prime 61928626541 := by
  apply nodeValid_prime [2, 5, 11, 23, 12238859] ⟨61928626541, 2, [(2, 2), (5, 1), (11, 1), (23, 1), (12238859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_12238859
  · decide +kernel

theorem prime_81213772267 : Nat.Prime 81213772267 := by
  apply nodeValid_prime [2, 3, 11, 37, 11085691] ⟨81213772267, 3, [(2, 1), (3, 2), (11, 1), (37, 1), (11085691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_11085691
  · decide +kernel

theorem prime_81372714877 : Nat.Prime 81372714877 := by
  apply nodeValid_prime [2, 3, 401, 5636791] ⟨81372714877, 5, [(2, 2), (3, 2), (401, 1), (5636791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_5636791
  · decide +kernel

theorem prime_123857253083 : Nat.Prime 123857253083 := by
  apply nodeValid_prime [2, 61928626541] ⟨123857253083, 2, [(2, 1), (61928626541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61928626541
  · decide +kernel

theorem prime_610891992229 : Nat.Prime 610891992229 := by
  apply nodeValid_prime [2, 3, 7, 9629, 755273] ⟨610891992229, 2, [(2, 2), (3, 1), (7, 1), (9629, 1), (755273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9629
    · exact prime_755273
  · decide +kernel

theorem prime_1213447737401 : Nat.Prime 1213447737401 := by
  apply nodeValid_prime [2, 5, 31, 6217, 31481] ⟨1213447737401, 3, [(2, 3), (5, 2), (31, 1), (6217, 1), (31481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_6217
    · exact prime_31481
  · decide +kernel

theorem prime_1213447755629 : Nat.Prime 1213447755629 := by
  apply nodeValid_prime [2, 31, 9785868997] ⟨1213447755629, 2, [(2, 2), (31, 1), (9785868997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_9785868997
  · decide +kernel

theorem prime_1217015691071 : Nat.Prime 1217015691071 := by
  apply nodeValid_prime [2, 5, 43, 2830269049] ⟨1217015691071, 11, [(2, 1), (5, 1), (43, 1), (2830269049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_2830269049
  · decide +kernel

theorem prime_1238572438973 : Nat.Prime 1238572438973 := by
  apply nodeValid_prime [2, 11, 113, 313, 795877] ⟨1238572438973, 2, [(2, 2), (11, 1), (113, 1), (313, 1), (795877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
    · exact prime_313
    · exact prime_795877
  · decide +kernel

theorem prime_2419773795979 : Nat.Prime 2419773795979 := by
  apply nodeValid_prime [2, 3, 7, 11, 487, 10754837] ⟨2419773795979, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (487, 1), (10754837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_487
    · exact prime_10754837
  · decide +kernel

theorem prime_2419773801931 : Nat.Prime 2419773801931 := by
  apply nodeValid_prime [2, 3, 5, 743, 36186239] ⟨2419773801931, 3, [(2, 1), (3, 2), (5, 1), (743, 1), (36186239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_743
    · exact prime_36186239
  · decide +kernel

theorem prime_2419773802343 : Nat.Prime 2419773802343 := by
  apply nodeValid_prime [2, 13, 47, 18493, 107077] ⟨2419773802343, 5, [(2, 1), (13, 1), (47, 1), (18493, 1), (107077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_18493
    · exact prime_107077
  · decide +kernel

theorem prime_2422146126091 : Nat.Prime 2422146126091 := by
  apply nodeValid_prime [2, 3, 5, 29, 7121, 390967] ⟨2422146126091, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (7121, 1), (390967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_7121
    · exact prime_390967
  · decide +kernel

theorem prime_2422146128627 : Nat.Prime 2422146128627 := by
  apply nodeValid_prime [2, 7, 59, 71, 41301131] ⟨2422146128627, 2, [(2, 1), (7, 1), (59, 1), (71, 1), (41301131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_71
    · exact prime_41301131
  · decide +kernel

theorem prime_2422146128659 : Nat.Prime 2422146128659 := by
  apply nodeValid_prime [2, 3, 23, 47, 18523, 20161] ⟨2422146128659, 2, [(2, 1), (3, 1), (23, 1), (47, 1), (18523, 1), (20161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47
    · exact prime_18523
    · exact prime_20161
  · decide +kernel

theorem prime_2424520010491 : Nat.Prime 2424520010491 := by
  apply nodeValid_prime [2, 3, 5, 509, 158776687] ⟨2424520010491, 2, [(2, 1), (3, 1), (5, 1), (509, 1), (158776687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_509
    · exact prime_158776687
  · decide +kernel

theorem prime_2424520010777 : Nat.Prime 2424520010777 := by
  apply nodeValid_prime [2, 23, 39503, 333563] ⟨2424520010777, 3, [(2, 3), (23, 1), (39503, 1), (333563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_39503
    · exact prime_333563
  · decide +kernel

theorem prime_2424520028773 : Nat.Prime 2424520028773 := by
  apply nodeValid_prime [2, 3, 83, 9749, 83231] ⟨2424520028773, 5, [(2, 2), (3, 2), (83, 1), (9749, 1), (83231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_9749
    · exact prime_83231
  · decide +kernel

theorem prime_2426895473141 : Nat.Prime 2426895473141 := by
  apply nodeValid_prime [2, 5, 373, 1571, 207079] ⟨2426895473141, 2, [(2, 2), (5, 1), (373, 1), (1571, 1), (207079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_373
    · exact prime_1571
    · exact prime_207079
  · decide +kernel

theorem prime_2426895474803 : Nat.Prime 2426895474803 := by
  apply nodeValid_prime [2, 1213447737401] ⟨2426895474803, 2, [(2, 1), (1213447737401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1213447737401
  · decide +kernel

theorem prime_2426895511259 : Nat.Prime 2426895511259 := by
  apply nodeValid_prime [2, 1213447755629] ⟨2426895511259, 2, [(2, 1), (1213447755629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1213447755629
  · decide +kernel

theorem prime_2429272561559 : Nat.Prime 2429272561559 := by
  apply nodeValid_prime [2, 17, 31, 1489, 1547893] ⟨2429272561559, 7, [(2, 1), (17, 1), (31, 1), (1489, 1), (1547893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_1489
    · exact prime_1547893
  · decide +kernel

theorem prime_2429272578163 : Nat.Prime 2429272578163 := by
  apply nodeValid_prime [2, 3, 37, 10942669271] ⟨2429272578163, 2, [(2, 1), (3, 1), (37, 1), (10942669271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_10942669271
  · decide +kernel

theorem prime_2429272579171 : Nat.Prime 2429272579171 := by
  apply nodeValid_prime [2, 3, 5, 17, 4763279567] ⟨2429272579171, 10, [(2, 1), (3, 1), (5, 1), (17, 1), (4763279567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_4763279567
  · decide +kernel

theorem prime_2431651187597 : Nat.Prime 2431651187597 := by
  apply nodeValid_prime [2, 71, 449, 19069381] ⟨2431651187597, 2, [(2, 2), (71, 1), (449, 1), (19069381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_449
    · exact prime_19069381
  · decide +kernel

theorem prime_2431651234049 : Nat.Prime 2431651234049 := by
  apply nodeValid_prime [2, 6907, 1375219] ⟨2431651234049, 3, [(2, 8), (6907, 1), (1375219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6907
    · exact prime_1375219
  · decide +kernel

theorem prime_2431651234319 : Nat.Prime 2431651234319 := by
  apply nodeValid_prime [2, 229, 3001, 1769171] ⟨2431651234319, 13, [(2, 1), (229, 1), (3001, 1), (1769171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_3001
    · exact prime_1769171
  · decide +kernel

theorem prime_2434031382143 : Nat.Prime 2434031382143 := by
  apply nodeValid_prime [2, 1217015691071] ⟨2434031382143, 5, [(2, 1), (1217015691071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1217015691071
  · decide +kernel

theorem prime_2434031422681 : Nat.Prime 2434031422681 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 23, 6167101] ⟨2434031422681, 14, [(2, 3), (3, 1), (5, 1), (11, 1), (13, 1), (23, 1), (6167101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_6167101
  · decide +kernel

theorem prime_2434031423309 : Nat.Prime 2434031423309 := by
  apply nodeValid_prime [2, 23893, 25468039] ⟨2434031423309, 2, [(2, 2), (23893, 1), (25468039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23893
    · exact prime_25468039
  · decide +kernel

theorem prime_2436413153201 : Nat.Prime 2436413153201 := by
  apply nodeValid_prime [2, 5, 13, 468540991] ⟨2436413153201, 6, [(2, 4), (5, 2), (13, 1), (468540991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_468540991
  · decide +kernel

theorem prime_2436413167631 : Nat.Prime 2436413167631 := by
  apply nodeValid_prime [2, 5, 13, 181, 103544971] ⟨2436413167631, 7, [(2, 1), (5, 1), (13, 1), (181, 1), (103544971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_181
    · exact prime_103544971
  · decide +kernel

theorem prime_2436413168011 : Nat.Prime 2436413168011 := by
  apply nodeValid_prime [2, 3, 5, 81213772267] ⟨2436413168011, 3, [(2, 1), (3, 1), (5, 1), (81213772267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_81213772267
  · decide +kernel

theorem prime_2438796507517 : Nat.Prime 2438796507517 := by
  apply nodeValid_prime [2, 3, 83, 2557, 319201] ⟨2438796507517, 2, [(2, 2), (3, 2), (83, 1), (2557, 1), (319201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_2557
    · exact prime_319201
  · decide +kernel

theorem prime_2438796513719 : Nat.Prime 2438796513719 := by
  apply nodeValid_prime [2, 17, 41, 102911491] ⟨2438796513719, 11, [(2, 1), (17, 2), (41, 1), (102911491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_102911491
  · decide +kernel

theorem prime_2438796514699 : Nat.Prime 2438796514699 := by
  apply nodeValid_prime [2, 3, 313879, 431659] ⟨2438796514699, 2, [(2, 1), (3, 2), (313879, 1), (431659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313879
    · exact prime_431659
  · decide +kernel

theorem prime_2441181446311 : Nat.Prime 2441181446311 := by
  apply nodeValid_prime [2, 3, 5, 81372714877] ⟨2441181446311, 3, [(2, 1), (3, 1), (5, 1), (81372714877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_81372714877
  · decide +kernel

theorem prime_2441181508637 : Nat.Prime 2441181508637 := by
  apply nodeValid_prime [2, 13, 439, 106938037] ⟨2441181508637, 2, [(2, 2), (13, 1), (439, 1), (106938037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_439
    · exact prime_106938037
  · decide +kernel

theorem prime_2441181514127 : Nat.Prime 2441181514127 := by
  apply nodeValid_prime [2, 167, 38707, 188827] ⟨2441181514127, 5, [(2, 1), (167, 1), (38707, 1), (188827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_38707
    · exact prime_188827
  · decide +kernel

theorem prime_2443567963997 : Nat.Prime 2443567963997 := by
  apply nodeValid_prime [2, 349, 443, 709, 5573] ⟨2443567963997, 2, [(2, 2), (349, 1), (443, 1), (709, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_349
    · exact prime_443
    · exact prime_709
    · exact prime_5573
  · decide +kernel

theorem prime_2443567964549 : Nat.Prime 2443567964549 := by
  apply nodeValid_prime [2, 461, 15919, 83243] ⟨2443567964549, 2, [(2, 2), (461, 1), (15919, 1), (83243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_461
    · exact prime_15919
    · exact prime_83243
  · decide +kernel

theorem prime_2443567968917 : Nat.Prime 2443567968917 := by
  apply nodeValid_prime [2, 610891992229] ⟨2443567968917, 2, [(2, 2), (610891992229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_610891992229
  · decide +kernel

theorem prime_2445955993543 : Nat.Prime 2445955993543 := by
  apply nodeValid_prime [2, 3, 17, 23979960721] ⟨2445955993543, 5, [(2, 1), (3, 1), (17, 1), (23979960721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23979960721
  · decide +kernel

theorem prime_2445955995883 : Nat.Prime 2445955995883 := by
  apply nodeValid_prime [2, 3, 7, 58237047521] ⟨2445955995883, 3, [(2, 1), (3, 1), (7, 1), (58237047521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_58237047521
  · decide +kernel

theorem prime_2445956064943 : Nat.Prime 2445956064943 := by
  apply nodeValid_prime [2, 3, 13, 17, 281, 6564457] ⟨2445956064943, 3, [(2, 1), (3, 1), (13, 1), (17, 1), (281, 1), (6564457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_281
    · exact prime_6564457
  · decide +kernel

theorem prime_2448345731621 : Nat.Prime 2448345731621 := by
  apply nodeValid_prime [2, 5, 37, 463, 7145951] ⟨2448345731621, 2, [(2, 2), (5, 1), (37, 1), (463, 1), (7145951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_463
    · exact prime_7145951
  · decide +kernel

theorem prime_2448345821683 : Nat.Prime 2448345821683 := by
  apply nodeValid_prime [2, 3, 23, 491, 36133679] ⟨2448345821683, 5, [(2, 1), (3, 1), (23, 1), (491, 1), (36133679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_491
    · exact prime_36133679
  · decide +kernel

theorem prime_2448345821917 : Nat.Prime 2448345821917 := by
  apply nodeValid_prime [2, 3, 69677, 2928209] ⟨2448345821917, 2, [(2, 2), (3, 1), (69677, 1), (2928209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_69677
    · exact prime_2928209
  · decide +kernel

theorem prime_2450736954689 : Nat.Prime 2450736954689 := by
  apply nodeValid_prime [2, 11, 3481160447] ⟨2450736954689, 3, [(2, 6), (11, 1), (3481160447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3481160447
  · decide +kernel

theorem prime_2450736955153 : Nat.Prime 2450736955153 := by
  apply nodeValid_prime [2, 3, 210111193] ⟨2450736955153, 5, [(2, 4), (3, 6), (210111193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_210111193
  · decide +kernel

theorem prime_2450736971773 : Nat.Prime 2450736971773 := by
  apply nodeValid_prime [2, 3, 7927, 25763603] ⟨2450736971773, 2, [(2, 2), (3, 1), (7927, 1), (25763603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7927
    · exact prime_25763603
  · decide +kernel

theorem prime_2453129767849 : Nat.Prime 2453129767849 := by
  apply nodeValid_prime [2, 3, 127, 1667, 482803] ⟨2453129767849, 7, [(2, 3), (3, 1), (127, 1), (1667, 1), (482803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_1667
    · exact prime_482803
  · decide +kernel

theorem prime_2453129769037 : Nat.Prime 2453129769037 := by
  apply nodeValid_prime [2, 3, 31, 3943, 1672441] ⟨2453129769037, 2, [(2, 2), (3, 1), (31, 1), (3943, 1), (1672441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3943
    · exact prime_1672441
  · decide +kernel

theorem prime_2453129789563 : Nat.Prime 2453129789563 := by
  apply nodeValid_prime [2, 3, 1901, 71691209] ⟨2453129789563, 2, [(2, 1), (3, 2), (1901, 1), (71691209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1901
    · exact prime_71691209
  · decide +kernel

theorem prime_2455524176099 : Nat.Prime 2455524176099 := by
  apply nodeValid_prime [2, 7, 17, 89, 115925039] ⟨2455524176099, 2, [(2, 1), (7, 1), (17, 1), (89, 1), (115925039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_89
    · exact prime_115925039
  · decide +kernel

theorem prime_2455524177269 : Nat.Prime 2455524177269 := by
  apply nodeValid_prime [2, 29, 59, 103, 577, 6037] ⟨2455524177269, 2, [(2, 2), (29, 1), (59, 1), (103, 1), (577, 1), (6037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_59
    · exact prime_103
    · exact prime_577
    · exact prime_6037
  · decide +kernel

theorem prime_2455524182029 : Nat.Prime 2455524182029 := by
  apply nodeValid_prime [2, 3, 41, 311, 16047919] ⟨2455524182029, 2, [(2, 2), (3, 1), (41, 1), (311, 1), (16047919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_311
    · exact prime_16047919
  · decide +kernel

theorem prime_2457920137837 : Nat.Prime 2457920137837 := by
  apply nodeValid_prime [2, 3, 631, 324606463] ⟨2457920137837, 2, [(2, 2), (3, 1), (631, 1), (324606463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
    · exact prime_324606463
  · decide +kernel

theorem prime_2457920138699 : Nat.Prime 2457920138699 := by
  apply nodeValid_prime [2, 1823, 674141563] ⟨2457920138699, 2, [(2, 1), (1823, 1), (674141563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1823
    · exact prime_674141563
  · decide +kernel

theorem prime_2457920159641 : Nat.Prime 2457920159641 := by
  apply nodeValid_prime [2, 3, 5, 11, 620686909] ⟨2457920159641, 13, [(2, 3), (3, 2), (5, 1), (11, 1), (620686909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_620686909
  · decide +kernel

theorem prime_2460317722763 : Nat.Prime 2460317722763 := by
  apply nodeValid_prime [2, 479, 2568181339] ⟨2460317722763, 2, [(2, 1), (479, 1), (2568181339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_2568181339
  · decide +kernel

theorem prime_2460317722979 : Nat.Prime 2460317722979 := by
  apply nodeValid_prime [2, 31, 37, 1072501187] ⟨2460317722979, 2, [(2, 1), (31, 1), (37, 1), (1072501187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37
    · exact prime_1072501187
  · decide +kernel

theorem prime_2460317724353 : Nat.Prime 2460317724353 := by
  apply nodeValid_prime [2, 43, 431, 683, 3037] ⟨2460317724353, 3, [(2, 6), (43, 1), (431, 1), (683, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_431
    · exact prime_683
    · exact prime_3037
  · decide +kernel

theorem prime_2462716807909 : Nat.Prime 2462716807909 := by
  apply nodeValid_prime [2, 3, 7, 10301, 406591] ⟨2462716807909, 2, [(2, 2), (3, 1), (7, 2), (10301, 1), (406591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10301
    · exact prime_406591
  · decide +kernel

theorem prime_2462716808063 : Nat.Prime 2462716808063 := by
  apply nodeValid_prime [2, 7, 163, 1079192291] ⟨2462716808063, 5, [(2, 1), (7, 1), (163, 1), (1079192291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163
    · exact prime_1079192291
  · decide +kernel

theorem prime_2462716871707 : Nat.Prime 2462716871707 := by
  apply nodeValid_prime [2, 3, 7, 13, 179, 3599737] ⟨2462716871707, 3, [(2, 1), (3, 1), (7, 2), (13, 1), (179, 1), (3599737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_179
    · exact prime_3599737
  · decide +kernel

theorem prime_2465117601671 : Nat.Prime 2465117601671 := by
  apply nodeValid_prime [2, 5, 29, 2293, 3707111] ⟨2465117601671, 7, [(2, 1), (5, 1), (29, 1), (2293, 1), (3707111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_2293
    · exact prime_3707111
  · decide +kernel

theorem prime_2465117630711 : Nat.Prime 2465117630711 := by
  apply nodeValid_prime [2, 5, 7, 37, 107, 983, 9049] ⟨2465117630711, 7, [(2, 1), (5, 1), (7, 1), (37, 1), (107, 1), (983, 1), (9049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_107
    · exact prime_983
    · exact prime_9049
  · decide +kernel

theorem prime_2465117631659 : Nat.Prime 2465117631659 := by
  apply nodeValid_prime [2, 11, 3533, 31715483] ⟨2465117631659, 2, [(2, 1), (11, 1), (3533, 1), (31715483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3533
    · exact prime_31715483
  · decide +kernel

theorem prime_2467519908727 : Nat.Prime 2467519908727 := by
  apply nodeValid_prime [2, 3, 1571, 15217, 17203] ⟨2467519908727, 3, [(2, 1), (3, 1), (1571, 1), (15217, 1), (17203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1571
    · exact prime_15217
    · exact prime_17203
  · decide +kernel

theorem prime_2467519909213 : Nat.Prime 2467519909213 := by
  apply nodeValid_prime [2, 3, 37, 23333, 238181] ⟨2467519909213, 2, [(2, 2), (3, 1), (37, 1), (23333, 1), (238181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_23333
    · exact prime_238181
  · decide +kernel

theorem prime_2467519923959 : Nat.Prime 2467519923959 := by
  apply nodeValid_prime [2, 19, 47, 1381590103] ⟨2467519923959, 19, [(2, 1), (19, 1), (47, 1), (1381590103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_1381590103
  · decide +kernel

theorem prime_2469923778733 : Nat.Prime 2469923778733 := by
  apply nodeValid_prime [2, 3, 197, 1044807013] ⟨2469923778733, 2, [(2, 2), (3, 1), (197, 1), (1044807013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1044807013
  · decide +kernel

theorem prime_2469923779261 : Nat.Prime 2469923779261 := by
  apply nodeValid_prime [2, 3, 5, 7, 840110129] ⟨2469923779261, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (840110129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_840110129
  · decide +kernel

theorem prime_2469923823079 : Nat.Prime 2469923823079 := by
  apply nodeValid_prime [2, 3, 45739330057] ⟨2469923823079, 13, [(2, 1), (3, 3), (45739330057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45739330057
  · decide +kernel

theorem prime_2472329293789 : Nat.Prime 2472329293789 := by
  apply nodeValid_prime [2, 3, 58337, 3531677] ⟨2472329293789, 2, [(2, 2), (3, 1), (58337, 1), (3531677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58337
    · exact prime_3531677
  · decide +kernel

theorem prime_2472329294059 : Nat.Prime 2472329294059 := by
  apply nodeValid_prime [2, 3, 13, 311, 101918101] ⟨2472329294059, 2, [(2, 1), (3, 1), (13, 1), (311, 1), (101918101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_311
    · exact prime_101918101
  · decide +kernel

theorem prime_2472329311789 : Nat.Prime 2472329311789 := by
  apply nodeValid_prime [2, 3, 7, 3511, 8382937] ⟨2472329311789, 6, [(2, 2), (3, 1), (7, 1), (3511, 1), (8382937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3511
    · exact prime_8382937
  · decide +kernel

theorem prime_2474736286657 : Nat.Prime 2474736286657 := by
  apply nodeValid_prime [2, 3, 479, 587, 45841] ⟨2474736286657, 5, [(2, 6), (3, 1), (479, 1), (587, 1), (45841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
    · exact prime_587
    · exact prime_45841
  · decide +kernel

theorem prime_2474736287897 : Nat.Prime 2474736287897 := by
  apply nodeValid_prime [2, 41, 184022627] ⟨2474736287897, 3, [(2, 3), (41, 2), (184022627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_184022627
  · decide +kernel

theorem prime_2474736395459 : Nat.Prime 2474736395459 := by
  apply nodeValid_prime [2, 19961, 61989289] ⟨2474736395459, 2, [(2, 1), (19961, 1), (61989289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19961
    · exact prime_61989289
  · decide +kernel

theorem prime_2477144876903 : Nat.Prime 2477144876903 := by
  apply nodeValid_prime [2, 46187, 26816473] ⟨2477144876903, 5, [(2, 1), (46187, 1), (26816473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_46187
    · exact prime_26816473
  · decide +kernel

theorem prime_2477144877947 : Nat.Prime 2477144877947 := by
  apply nodeValid_prime [2, 1238572438973] ⟨2477144877947, 2, [(2, 1), (1238572438973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1238572438973
  · decide +kernel

theorem prime_2477145061661 : Nat.Prime 2477145061661 := by
  apply nodeValid_prime [2, 5, 123857253083] ⟨2477145061661, 2, [(2, 2), (5, 1), (123857253083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_123857253083
  · decide +kernel

end Sude.Lucas.Generated
