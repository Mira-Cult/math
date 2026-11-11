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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0095

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5783 : Nat.Prime 5783 := by
  apply nodeValid_prime [2, 7, 59] ⟨5783, 7, [(2, 1), (7, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_5923 : Nat.Prime 5923 := by
  apply nodeValid_prime [2, 3, 7, 47] ⟨5923, 2, [(2, 1), (3, 2), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_11503 : Nat.Prime 11503 := by
  apply nodeValid_prime [2, 3, 71] ⟨11503, 3, [(2, 1), (3, 4), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_14423 : Nat.Prime 14423 := by
  apply nodeValid_prime [2, 7211] ⟨14423, 5, [(2, 1), (7211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7211
  · decide +kernel

theorem prime_18701 : Nat.Prime 18701 := by
  apply nodeValid_prime [2, 5, 11, 17] ⟨18701, 2, [(2, 2), (5, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_19949 : Nat.Prime 19949 := by
  apply nodeValid_prime [2, 4987] ⟨19949, 2, [(2, 2), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4987
  · decide +kernel

theorem prime_23059 : Nat.Prime 23059 := by
  apply nodeValid_prime [2, 3, 7, 61] ⟨23059, 3, [(2, 1), (3, 3), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_24821 : Nat.Prime 24821 := by
  apply nodeValid_prime [2, 5, 17, 73] ⟨24821, 2, [(2, 2), (5, 1), (17, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_73
  · decide +kernel

theorem prime_25621 : Nat.Prime 25621 := by
  apply nodeValid_prime [2, 3, 5, 7, 61] ⟨25621, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_28349 : Nat.Prime 28349 := by
  apply nodeValid_prime [2, 19, 373] ⟨28349, 2, [(2, 2), (19, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_373
  · decide +kernel

theorem prime_33871 : Nat.Prime 33871 := by
  apply nodeValid_prime [2, 3, 5, 1129] ⟨33871, 15, [(2, 1), (3, 1), (5, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1129
  · decide +kernel

theorem prime_44777 : Nat.Prime 44777 := by
  apply nodeValid_prime [2, 29, 193] ⟨44777, 3, [(2, 3), (29, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_193
  · decide +kernel

theorem prime_47363 : Nat.Prime 47363 := by
  apply nodeValid_prime [2, 7, 17, 199] ⟨47363, 2, [(2, 1), (7, 1), (17, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_199
  · decide +kernel

theorem prime_50647 : Nat.Prime 50647 := by
  apply nodeValid_prime [2, 3, 23, 367] ⟨50647, 3, [(2, 1), (3, 1), (23, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_367
  · decide +kernel

theorem prime_58997 : Nat.Prime 58997 := by
  apply nodeValid_prime [2, 7, 43] ⟨58997, 3, [(2, 2), (7, 3), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_62171 : Nat.Prime 62171 := by
  apply nodeValid_prime [2, 5, 6217] ⟨62171, 2, [(2, 1), (5, 1), (6217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6217
  · decide +kernel

theorem prime_67121 : Nat.Prime 67121 := by
  apply nodeValid_prime [2, 5, 839] ⟨67121, 6, [(2, 4), (5, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_839
  · decide +kernel

theorem prime_68947 : Nat.Prime 68947 := by
  apply nodeValid_prime [2, 3, 11491] ⟨68947, 2, [(2, 1), (3, 1), (11491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11491
  · decide +kernel

theorem prime_71887 : Nat.Prime 71887 := by
  apply nodeValid_prime [2, 3, 11981] ⟨71887, 3, [(2, 1), (3, 1), (11981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11981
  · decide +kernel

theorem prime_82051 : Nat.Prime 82051 := by
  apply nodeValid_prime [2, 3, 5, 547] ⟨82051, 2, [(2, 1), (3, 1), (5, 2), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_547
  · decide +kernel

theorem prime_94099 : Nat.Prime 94099 := by
  apply nodeValid_prime [2, 3, 15683] ⟨94099, 2, [(2, 1), (3, 1), (15683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15683
  · decide +kernel

theorem prime_98641 : Nat.Prime 98641 := by
  apply nodeValid_prime [2, 3, 5, 137] ⟨98641, 17, [(2, 4), (3, 2), (5, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_101161 : Nat.Prime 101161 := by
  apply nodeValid_prime [2, 3, 5, 281] ⟨101161, 13, [(2, 3), (3, 2), (5, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_281
  · decide +kernel

theorem prime_107201 : Nat.Prime 107201 := by
  apply nodeValid_prime [2, 5, 67] ⟨107201, 7, [(2, 6), (5, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_112207 : Nat.Prime 112207 := by
  apply nodeValid_prime [2, 3, 18701] ⟨112207, 5, [(2, 1), (3, 1), (18701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18701
  · decide +kernel

theorem prime_118757 : Nat.Prime 118757 := by
  apply nodeValid_prime [2, 11, 2699] ⟨118757, 2, [(2, 2), (11, 1), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2699
  · decide +kernel

theorem prime_126359 : Nat.Prime 126359 := by
  apply nodeValid_prime [2, 63179] ⟨126359, 7, [(2, 1), (63179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63179
  · decide +kernel

theorem prime_134243 : Nat.Prime 134243 := by
  apply nodeValid_prime [2, 67121] ⟨134243, 2, [(2, 1), (67121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67121
  · decide +kernel

theorem prime_139981 : Nat.Prime 139981 := by
  apply nodeValid_prime [2, 3, 5, 2333] ⟨139981, 10, [(2, 2), (3, 1), (5, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2333
  · decide +kernel

theorem prime_181061 : Nat.Prime 181061 := by
  apply nodeValid_prime [2, 5, 11, 823] ⟨181061, 2, [(2, 2), (5, 1), (11, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_823
  · decide +kernel

theorem prime_183569 : Nat.Prime 183569 := by
  apply nodeValid_prime [2, 7, 11, 149] ⟨183569, 3, [(2, 4), (7, 1), (11, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_149
  · decide +kernel

theorem prime_187349 : Nat.Prime 187349 := by
  apply nodeValid_prime [2, 7, 6691] ⟨187349, 2, [(2, 2), (7, 1), (6691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6691
  · decide +kernel

theorem prime_189529 : Nat.Prime 189529 := by
  apply nodeValid_prime [2, 3, 53, 149] ⟨189529, 22, [(2, 3), (3, 1), (53, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_149
  · decide +kernel

theorem prime_191969 : Nat.Prime 191969 := by
  apply nodeValid_prime [2, 7, 857] ⟨191969, 3, [(2, 5), (7, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_857
  · decide +kernel

theorem prime_257293 : Nat.Prime 257293 := by
  apply nodeValid_prime [2, 3, 7, 1021] ⟨257293, 14, [(2, 2), (3, 2), (7, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1021
  · decide +kernel

theorem prime_268487 : Nat.Prime 268487 := by
  apply nodeValid_prime [2, 134243] ⟨268487, 5, [(2, 1), (134243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_134243
  · decide +kernel

theorem prime_285473 : Nat.Prime 285473 := by
  apply nodeValid_prime [2, 11, 811] ⟨285473, 3, [(2, 5), (11, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_811
  · decide +kernel

theorem prime_287549 : Nat.Prime 287549 := by
  apply nodeValid_prime [2, 71887] ⟨287549, 2, [(2, 2), (71887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71887
  · decide +kernel

theorem prime_287857 : Nat.Prime 287857 := by
  apply nodeValid_prime [2, 3, 1999] ⟨287857, 10, [(2, 4), (3, 2), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1999
  · decide +kernel

theorem prime_327889 : Nat.Prime 327889 := by
  apply nodeValid_prime [2, 3, 11, 23] ⟨327889, 17, [(2, 4), (3, 4), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_396631 : Nat.Prime 396631 := by
  apply nodeValid_prime [2, 3, 5, 13, 113] ⟨396631, 3, [(2, 1), (3, 3), (5, 1), (13, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_113
  · decide +kernel

theorem prime_405347 : Nat.Prime 405347 := by
  apply nodeValid_prime [2, 19, 10667] ⟨405347, 2, [(2, 1), (19, 1), (10667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_10667
  · decide +kernel

theorem prime_419599 : Nat.Prime 419599 := by
  apply nodeValid_prime [2, 3, 23311] ⟨419599, 3, [(2, 1), (3, 2), (23311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23311
  · decide +kernel

theorem prime_472817 : Nat.Prime 472817 := by
  apply nodeValid_prime [2, 29, 1019] ⟨472817, 3, [(2, 4), (29, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1019
  · decide +kernel

theorem prime_510931 : Nat.Prime 510931 := by
  apply nodeValid_prime [2, 3, 5, 7, 811] ⟨510931, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_811
  · decide +kernel

theorem prime_602461 : Nat.Prime 602461 := by
  apply nodeValid_prime [2, 3, 5, 3347] ⟨602461, 6, [(2, 2), (3, 2), (5, 1), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3347
  · decide +kernel

theorem prime_675931 : Nat.Prime 675931 := by
  apply nodeValid_prime [2, 3, 5, 22531] ⟨675931, 2, [(2, 1), (3, 1), (5, 1), (22531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22531
  · decide +kernel

theorem prime_793453 : Nat.Prime 793453 := by
  apply nodeValid_prime [2, 3, 11, 6011] ⟨793453, 2, [(2, 2), (3, 1), (11, 1), (6011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6011
  · decide +kernel

theorem prime_839887 : Nat.Prime 839887 := by
  apply nodeValid_prime [2, 3, 139981] ⟨839887, 3, [(2, 1), (3, 1), (139981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139981
  · decide +kernel

theorem prime_989869 : Nat.Prime 989869 := by
  apply nodeValid_prime [2, 3, 11, 7499] ⟨989869, 2, [(2, 2), (3, 1), (11, 1), (7499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_7499
  · decide +kernel

theorem prime_1023133 : Nat.Prime 1023133 := by
  apply nodeValid_prime [2, 3, 11, 23, 337] ⟨1023133, 2, [(2, 2), (3, 1), (11, 1), (23, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_337
  · decide +kernel

theorem prime_1273411 : Nat.Prime 1273411 := by
  apply nodeValid_prime [2, 3, 5, 14149] ⟨1273411, 2, [(2, 1), (3, 2), (5, 1), (14149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14149
  · decide +kernel

theorem prime_1672501 : Nat.Prime 1672501 := by
  apply nodeValid_prime [2, 3, 5, 223] ⟨1672501, 6, [(2, 2), (3, 1), (5, 4), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
  · decide +kernel

theorem prime_1831979 : Nat.Prime 1831979 := by
  apply nodeValid_prime [2, 641, 1429] ⟨1831979, 2, [(2, 1), (641, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_1429
  · decide +kernel

theorem prime_1938971 : Nat.Prime 1938971 := by
  apply nodeValid_prime [2, 5, 11, 17627] ⟨1938971, 2, [(2, 1), (5, 1), (11, 1), (17627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17627
  · decide +kernel

theorem prime_1983563 : Nat.Prime 1983563 := by
  apply nodeValid_prime [2, 7, 19, 7457] ⟨1983563, 2, [(2, 1), (7, 1), (19, 1), (7457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_7457
  · decide +kernel

theorem prime_2422463 : Nat.Prime 2422463 := by
  apply nodeValid_prime [2, 7, 19, 1301] ⟨2422463, 5, [(2, 1), (7, 2), (19, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_1301
  · decide +kernel

theorem prime_2477681 : Nat.Prime 2477681 := by
  apply nodeValid_prime [2, 5, 30971] ⟨2477681, 7, [(2, 4), (5, 1), (30971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30971
  · decide +kernel

theorem prime_2894431 : Nat.Prime 2894431 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 179] ⟨2894431, 24, [(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_179
  · decide +kernel

theorem prime_3017603 : Nat.Prime 3017603 := by
  apply nodeValid_prime [2, 7, 17, 31, 409] ⟨3017603, 2, [(2, 1), (7, 1), (17, 1), (31, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_409
  · decide +kernel

theorem prime_3836279 : Nat.Prime 3836279 := by
  apply nodeValid_prime [2, 809, 2371] ⟨3836279, 13, [(2, 1), (809, 1), (2371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_809
    · exact prime_2371
  · decide +kernel

theorem prime_4832767 : Nat.Prime 4832767 := by
  apply nodeValid_prime [2, 3, 268487] ⟨4832767, 3, [(2, 1), (3, 2), (268487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_268487
  · decide +kernel

theorem prime_5918461 : Nat.Prime 5918461 := by
  apply nodeValid_prime [2, 3, 5, 98641] ⟨5918461, 6, [(2, 2), (3, 1), (5, 1), (98641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_98641
  · decide +kernel

theorem prime_7186037 : Nat.Prime 7186037 := by
  apply nodeValid_prime [2, 11, 13, 17, 739] ⟨7186037, 2, [(2, 2), (11, 1), (13, 1), (17, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_739
  · decide +kernel

theorem prime_9622931 : Nat.Prime 9622931 := by
  apply nodeValid_prime [2, 5, 19, 50647] ⟨9622931, 2, [(2, 1), (5, 1), (19, 1), (50647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_50647
  · decide +kernel

theorem prime_11633827 : Nat.Prime 11633827 := by
  apply nodeValid_prime [2, 3, 1938971] ⟨11633827, 3, [(2, 1), (3, 1), (1938971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1938971
  · decide +kernel

theorem prime_11933153 : Nat.Prime 11933153 := by
  apply nodeValid_prime [2, 7, 11, 29, 167] ⟨11933153, 3, [(2, 5), (7, 1), (11, 1), (29, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_167
  · decide +kernel

theorem prime_14091551 : Nat.Prime 14091551 := by
  apply nodeValid_prime [2, 5, 11, 25621] ⟨14091551, 11, [(2, 1), (5, 2), (11, 1), (25621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_25621
  · decide +kernel

theorem prime_15429671 : Nat.Prime 15429671 := by
  apply nodeValid_prime [2, 5, 461, 3347] ⟨15429671, 17, [(2, 1), (5, 1), (461, 1), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_461
    · exact prime_3347
  · decide +kernel

theorem prime_16194301 : Nat.Prime 16194301 := by
  apply nodeValid_prime [2, 3, 5, 23, 2347] ⟨16194301, 2, [(2, 2), (3, 1), (5, 2), (23, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_2347
  · decide +kernel

theorem prime_17262379 : Nat.Prime 17262379 := by
  apply nodeValid_prime [2, 3, 7, 17, 8059] ⟨17262379, 3, [(2, 1), (3, 2), (7, 1), (17, 1), (8059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_8059
  · decide +kernel

theorem prime_25331417 : Nat.Prime 25331417 := by
  apply nodeValid_prime [2, 11, 287857] ⟨25331417, 3, [(2, 3), (11, 1), (287857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_287857
  · decide +kernel

theorem prime_25933741 : Nat.Prime 25933741 := by
  apply nodeValid_prime [2, 3, 5, 7, 8821] ⟨25933741, 14, [(2, 2), (3, 1), (5, 1), (7, 2), (8821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_8821
  · decide +kernel

theorem prime_30534701 : Nat.Prime 30534701 := by
  apply nodeValid_prime [2, 5, 7, 181, 241] ⟨30534701, 3, [(2, 2), (5, 2), (7, 1), (181, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_181
    · exact prime_241
  · decide +kernel

theorem prime_33198103 : Nat.Prime 33198103 := by
  apply nodeValid_prime [2, 3, 7, 37, 7121] ⟨33198103, 7, [(2, 1), (3, 2), (7, 1), (37, 1), (7121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_7121
  · decide +kernel

theorem prime_46035349 : Nat.Prime 46035349 := by
  apply nodeValid_prime [2, 3, 3836279] ⟨46035349, 2, [(2, 2), (3, 1), (3836279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3836279
  · decide +kernel

theorem prime_87934993 : Nat.Prime 87934993 := by
  apply nodeValid_prime [2, 3, 1831979] ⟨87934993, 5, [(2, 4), (3, 1), (1831979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1831979
  · decide +kernel

theorem prime_96713311 : Nat.Prime 96713311 := by
  apply nodeValid_prime [2, 3, 5, 47, 113, 607] ⟨96713311, 6, [(2, 1), (3, 1), (5, 1), (47, 1), (113, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_113
    · exact prime_607
  · decide +kernel

theorem prime_114622301 : Nat.Prime 114622301 := by
  apply nodeValid_prime [2, 5, 13, 37, 2383] ⟨114622301, 3, [(2, 2), (5, 2), (13, 1), (37, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_2383
  · decide +kernel

theorem prime_144086879 : Nat.Prime 144086879 := by
  apply nodeValid_prime [2, 13, 1499, 3697] ⟨144086879, 29, [(2, 1), (13, 1), (1499, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1499
    · exact prime_3697
  · decide +kernel

theorem prime_148802809 : Nat.Prime 148802809 := by
  apply nodeValid_prime [2, 3, 7, 11, 11503] ⟨148802809, 38, [(2, 3), (3, 1), (7, 2), (11, 1), (11503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_11503
  · decide +kernel

theorem prime_209408887 : Nat.Prime 209408887 := by
  apply nodeValid_prime [2, 3, 11633827] ⟨209408887, 3, [(2, 1), (3, 2), (11633827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11633827
  · decide +kernel

theorem prime_244277609 : Nat.Prime 244277609 := by
  apply nodeValid_prime [2, 30534701] ⟨244277609, 3, [(2, 3), (30534701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30534701
  · decide +kernel

theorem prime_253334959 : Nat.Prime 253334959 := by
  apply nodeValid_prime [2, 3, 71, 401, 1483] ⟨253334959, 15, [(2, 1), (3, 1), (71, 1), (401, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_401
    · exact prime_1483
  · decide +kernel

theorem prime_280502921 : Nat.Prime 280502921 := by
  apply nodeValid_prime [2, 5, 37, 189529] ⟨280502921, 3, [(2, 3), (5, 1), (37, 1), (189529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_189529
  · decide +kernel

theorem prime_405952429 : Nat.Prime 405952429 := by
  apply nodeValid_prime [2, 3, 7, 4832767] ⟨405952429, 2, [(2, 2), (3, 1), (7, 1), (4832767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4832767
  · decide +kernel

theorem prime_440179211 : Nat.Prime 440179211 := by
  apply nodeValid_prime [2, 5, 97, 101, 4493] ⟨440179211, 6, [(2, 1), (5, 1), (97, 1), (101, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_101
    · exact prime_4493
  · decide +kernel

theorem prime_656217589 : Nat.Prime 656217589 := by
  apply nodeValid_prime [2, 3, 13, 59, 83, 859] ⟨656217589, 2, [(2, 2), (3, 1), (13, 1), (59, 1), (83, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_83
    · exact prime_859
  · decide +kernel

theorem prime_728837467 : Nat.Prime 728837467 := by
  apply nodeValid_prime [2, 3, 7, 31, 211, 379] ⟨728837467, 3, [(2, 1), (3, 1), (7, 2), (31, 1), (211, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_211
    · exact prime_379
  · decide +kernel

theorem prime_1085968369 : Nat.Prime 1085968369 := by
  apply nodeValid_prime [2, 3, 23, 327889] ⟨1085968369, 7, [(2, 4), (3, 2), (23, 1), (327889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_327889
  · decide +kernel

theorem prime_1540859533 : Nat.Prime 1540859533 := by
  apply nodeValid_prime [2, 3, 17, 223, 33871] ⟨1540859533, 5, [(2, 2), (3, 1), (17, 1), (223, 1), (33871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_223
    · exact prime_33871
  · decide +kernel

theorem prime_1559188537 : Nat.Prime 1559188537 := by
  apply nodeValid_prime [2, 3, 1607, 40427] ⟨1559188537, 23, [(2, 3), (3, 1), (1607, 1), (40427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1607
    · exact prime_40427
  · decide +kernel

theorem prime_1630259467 : Nat.Prime 1630259467 := by
  apply nodeValid_prime [2, 3, 11, 41, 602461] ⟨1630259467, 2, [(2, 1), (3, 1), (11, 1), (41, 1), (602461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_602461
  · decide +kernel

theorem prime_2188790599 : Nat.Prime 2188790599 := by
  apply nodeValid_prime [2, 3, 2887, 126359] ⟨2188790599, 3, [(2, 1), (3, 1), (2887, 1), (126359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2887
    · exact prime_126359
  · decide +kernel

theorem prime_2563823761 : Nat.Prime 2563823761 := by
  apply nodeValid_prime [2, 3, 5, 59, 181061] ⟨2563823761, 17, [(2, 4), (3, 1), (5, 1), (59, 1), (181061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_181061
  · decide +kernel

theorem prime_2756550127 : Nat.Prime 2756550127 := by
  apply nodeValid_prime [2, 3, 11, 331, 11471] ⟨2756550127, 3, [(2, 1), (3, 1), (11, 2), (331, 1), (11471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_331
    · exact prime_11471
  · decide +kernel

theorem prime_3389111321 : Nat.Prime 3389111321 := by
  apply nodeValid_prime [2, 5, 7, 19, 33529] ⟨3389111321, 11, [(2, 3), (5, 1), (7, 1), (19, 2), (33529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_33529
  · decide +kernel

theorem prime_3841194853 : Nat.Prime 3841194853 := by
  apply nodeValid_prime [2, 3, 11, 193, 1523] ⟨3841194853, 6, [(2, 2), (3, 3), (11, 2), (193, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193
    · exact prime_1523
  · decide +kernel

theorem prime_4393699711 : Nat.Prime 4393699711 := by
  apply nodeValid_prime [2, 3, 5, 5197, 28181] ⟨4393699711, 3, [(2, 1), (3, 1), (5, 1), (5197, 1), (28181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5197
    · exact prime_28181
  · decide +kernel

theorem prime_4725901571 : Nat.Prime 4725901571 := by
  apply nodeValid_prime [2, 5, 13, 17, 487, 4391] ⟨4725901571, 2, [(2, 1), (5, 1), (13, 1), (17, 1), (487, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_487
    · exact prime_4391
  · decide +kernel

theorem prime_6236754149 : Nat.Prime 6236754149 := by
  apply nodeValid_prime [2, 1559188537] ⟨6236754149, 2, [(2, 2), (1559188537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1559188537
  · decide +kernel

theorem prime_7178706527 : Nat.Prime 7178706527 := by
  apply nodeValid_prime [2, 373, 9622931] ⟨7178706527, 5, [(2, 1), (373, 1), (9622931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_9622931
  · decide +kernel

theorem prime_17259525847 : Nat.Prime 17259525847 := by
  apply nodeValid_prime [2, 3, 43, 2477681] ⟨17259525847, 6, [(2, 1), (3, 4), (43, 1), (2477681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_2477681
  · decide +kernel

theorem prime_20689324769 : Nat.Prime 20689324769 := by
  apply nodeValid_prime [2, 7, 17, 29, 187349] ⟨20689324769, 3, [(2, 5), (7, 1), (17, 1), (29, 1), (187349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_29
    · exact prime_187349
  · decide +kernel

theorem prime_22634349719 : Nat.Prime 22634349719 := by
  apply nodeValid_prime [2, 43, 71, 641, 5783] ⟨22634349719, 7, [(2, 1), (43, 1), (71, 1), (641, 1), (5783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_71
    · exact prime_641
    · exact prime_5783
  · decide +kernel

theorem prime_41378649539 : Nat.Prime 41378649539 := by
  apply nodeValid_prime [2, 20689324769] ⟨41378649539, 2, [(2, 1), (20689324769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20689324769
  · decide +kernel

theorem prime_45268699439 : Nat.Prime 45268699439 := by
  apply nodeValid_prime [2, 22634349719] ⟨45268699439, 13, [(2, 1), (22634349719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22634349719
  · decide +kernel

theorem prime_49472017351 : Nat.Prime 49472017351 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 1273411] ⟨49472017351, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (37, 1), (1273411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_1273411
  · decide +kernel

theorem prime_134000797471 : Nat.Prime 134000797471 := by
  apply nodeValid_prime [2, 3, 5, 31, 144086879] ⟨134000797471, 3, [(2, 1), (3, 1), (5, 1), (31, 1), (144086879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_144086879
  · decide +kernel

theorem prime_134480610983 : Nat.Prime 134480610983 := by
  apply nodeValid_prime [2, 41, 677, 2422463] ⟨134480610983, 5, [(2, 1), (41, 1), (677, 1), (2422463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_677
    · exact prime_2422463
  · decide +kernel

theorem prime_272096095463 : Nat.Prime 272096095463 := by
  apply nodeValid_prime [2, 31, 37, 461, 257293] ⟨272096095463, 5, [(2, 1), (31, 1), (37, 1), (461, 1), (257293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37
    · exact prime_461
    · exact prime_257293
  · decide +kernel

theorem prime_320740074397 : Nat.Prime 320740074397 := by
  apply nodeValid_prime [2, 3, 7, 269, 675931] ⟨320740074397, 2, [(2, 2), (3, 2), (7, 2), (269, 1), (675931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_269
    · exact prime_675931
  · decide +kernel

theorem prime_535045301423 : Nat.Prime 535045301423 := by
  apply nodeValid_prime [2, 659, 405952429] ⟨535045301423, 5, [(2, 1), (659, 1), (405952429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_659
    · exact prime_405952429
  · decide +kernel

theorem prime_804004784827 : Nat.Prime 804004784827 := by
  apply nodeValid_prime [2, 3, 134000797471] ⟨804004784827, 2, [(2, 1), (3, 1), (134000797471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_134000797471
  · decide +kernel

theorem prime_808325756569 : Nat.Prime 808325756569 := by
  apply nodeValid_prime [2, 3, 11, 19, 59, 101161] ⟨808325756569, 17, [(2, 3), (3, 4), (11, 1), (19, 1), (59, 1), (101161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_59
    · exact prime_101161
  · decide +kernel

theorem prime_817741703659 : Nat.Prime 817741703659 := by
  apply nodeValid_prime [2, 3, 11, 73, 15429671] ⟨817741703659, 2, [(2, 1), (3, 1), (11, 2), (73, 1), (15429671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_15429671
  · decide +kernel

theorem prime_1610886716891 : Nat.Prime 1610886716891 := by
  apply nodeValid_prime [2, 5, 11, 17, 2053, 419599] ⟨1610886716891, 10, [(2, 1), (5, 1), (11, 1), (17, 1), (2053, 1), (419599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_2053
    · exact prime_419599
  · decide +kernel

theorem prime_1616651509409 : Nat.Prime 1616651509409 := by
  apply nodeValid_prime [2, 13, 47363, 82051] ⟨1616651509409, 3, [(2, 5), (13, 1), (47363, 1), (82051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47363
    · exact prime_82051
  · decide +kernel

theorem prime_1635483407471 : Nat.Prime 1635483407471 := by
  apply nodeValid_prime [2, 5, 11, 71, 209408887] ⟨1635483407471, 7, [(2, 1), (5, 1), (11, 1), (71, 1), (209408887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_71
    · exact prime_209408887
  · decide +kernel

theorem prime_3204531429809 : Nat.Prime 3204531429809 := by
  apply nodeValid_prime [2, 61, 233, 14091551] ⟨3204531429809, 3, [(2, 4), (61, 1), (233, 1), (14091551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_233
    · exact prime_14091551
  · decide +kernel

theorem prime_3204531434107 : Nat.Prime 3204531434107 := by
  apply nodeValid_prime [2, 3, 631, 14143, 19949] ⟨3204531434107, 2, [(2, 1), (3, 2), (631, 1), (14143, 1), (19949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
    · exact prime_14143
    · exact prime_19949
  · decide +kernel

theorem prime_3204531435439 : Nat.Prime 3204531435439 := by
  apply nodeValid_prime [2, 3, 58997, 3017603] ⟨3204531435439, 6, [(2, 1), (3, 2), (58997, 1), (3017603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58997
    · exact prime_3017603
  · decide +kernel

theorem prime_3207400743971 : Nat.Prime 3207400743971 := by
  apply nodeValid_prime [2, 5, 320740074397] ⟨3207400743971, 2, [(2, 1), (5, 1), (320740074397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_320740074397
  · decide +kernel

theorem prime_3207400789031 : Nat.Prime 3207400789031 := by
  apply nodeValid_prime [2, 5, 73, 4393699711] ⟨3207400789031, 31, [(2, 1), (5, 1), (73, 1), (4393699711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_4393699711
  · decide +kernel

theorem prime_3207400790177 : Nat.Prime 3207400790177 := by
  apply nodeValid_prime [2, 11, 19, 571, 839887] ⟨3207400790177, 3, [(2, 5), (11, 1), (19, 1), (571, 1), (839887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_571
    · exact prime_839887
  · decide +kernel

theorem prime_3210271801367 : Nat.Prime 3210271801367 := by
  apply nodeValid_prime [2, 7, 23, 67, 148802809] ⟨3210271801367, 5, [(2, 1), (7, 1), (23, 1), (67, 1), (148802809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_67
    · exact prime_148802809
  · decide +kernel

theorem prime_3210271807543 : Nat.Prime 3210271807543 := by
  apply nodeValid_prime [2, 3, 31, 17259525847] ⟨3210271807543, 3, [(2, 1), (3, 1), (31, 1), (17259525847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_17259525847
  · decide +kernel

theorem prime_3210271808539 : Nat.Prime 3210271808539 := by
  apply nodeValid_prime [2, 3, 535045301423] ⟨3210271808539, 2, [(2, 1), (3, 1), (535045301423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_535045301423
  · decide +kernel

theorem prime_3213144599333 : Nat.Prime 3213144599333 := by
  apply nodeValid_prime [2, 367, 2188790599] ⟨3213144599333, 2, [(2, 2), (367, 1), (2188790599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_2188790599
  · decide +kernel

theorem prime_3213144643087 : Nat.Prime 3213144643087 := by
  apply nodeValid_prime [2, 3, 7, 2137, 11933153] ⟨3213144643087, 7, [(2, 1), (3, 2), (7, 1), (2137, 1), (11933153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2137
    · exact prime_11933153
  · decide +kernel

theorem prime_3213144644221 : Nat.Prime 3213144644221 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 87934993] ⟨3213144644221, 11, [(2, 2), (3, 2), (5, 1), (7, 1), (29, 1), (87934993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_87934993
  · decide +kernel

theorem prime_3216019049647 : Nat.Prime 3216019049647 := by
  apply nodeValid_prime [2, 3, 13, 23, 1811, 989869] ⟨3216019049647, 23, [(2, 1), (3, 1), (13, 1), (23, 1), (1811, 1), (989869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_1811
    · exact prime_989869
  · decide +kernel

theorem prime_3216019049731 : Nat.Prime 3216019049731 := by
  apply nodeValid_prime [2, 3, 5, 179, 13841, 14423] ⟨3216019049731, 2, [(2, 1), (3, 2), (5, 1), (179, 1), (13841, 1), (14423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_13841
    · exact prime_14423
  · decide +kernel

theorem prime_3216019139309 : Nat.Prime 3216019139309 := by
  apply nodeValid_prime [2, 804004784827] ⟨3216019139309, 2, [(2, 2), (804004784827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_804004784827
  · decide +kernel

theorem prime_3218895393251 : Nat.Prime 3218895393251 := by
  apply nodeValid_prime [2, 5, 44777, 287549] ⟨3218895393251, 2, [(2, 1), (5, 3), (44777, 1), (287549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_44777
    · exact prime_287549
  · decide +kernel

theorem prime_3218895393281 : Nat.Prime 3218895393281 := by
  apply nodeValid_prime [2, 5, 7, 17, 709, 2129] ⟨3218895393281, 3, [(2, 9), (5, 1), (7, 2), (17, 1), (709, 1), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_709
    · exact prime_2129
  · decide +kernel

theorem prime_3218895424601 : Nat.Prime 3218895424601 := by
  apply nodeValid_prime [2, 5, 9623, 1672501] ⟨3218895424601, 3, [(2, 3), (5, 2), (9623, 1), (1672501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9623
    · exact prime_1672501
  · decide +kernel

theorem prime_3221773429961 : Nat.Prime 3221773429961 := by
  apply nodeValid_prime [2, 5, 31, 439, 5918461] ⟨3221773429961, 3, [(2, 3), (5, 1), (31, 1), (439, 1), (5918461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_439
    · exact prime_5918461
  · decide +kernel

theorem prime_3221773433783 : Nat.Prime 3221773433783 := by
  apply nodeValid_prime [2, 1610886716891] ⟨3221773433783, 5, [(2, 1), (1610886716891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1610886716891
  · decide +kernel

theorem prime_3221773456507 : Nat.Prime 3221773456507 := by
  apply nodeValid_prime [2, 3, 11, 6793, 7186037] ⟨3221773456507, 3, [(2, 1), (3, 1), (11, 1), (6793, 1), (7186037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6793
    · exact prime_7186037
  · decide +kernel

theorem prime_3224653223423 : Nat.Prime 3224653223423 := by
  apply nodeValid_prime [2, 62171, 25933741] ⟨3224653223423, 5, [(2, 1), (62171, 1), (25933741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_62171
    · exact prime_25933741
  · decide +kernel

theorem prime_3224653225727 : Nat.Prime 3224653225727 := by
  apply nodeValid_prime [2, 23, 43, 1630259467] ⟨3224653225727, 5, [(2, 1), (23, 1), (43, 1), (1630259467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
    · exact prime_1630259467
  · decide +kernel

theorem prime_3224653232347 : Nat.Prime 3224653232347 := by
  apply nodeValid_prime [2, 3, 7, 13, 656217589] ⟨3224653232347, 5, [(2, 1), (3, 3), (7, 1), (13, 1), (656217589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_656217589
  · decide +kernel

theorem prime_3227534663593 : Nat.Prime 3227534663593 := by
  apply nodeValid_prime [2, 3, 134480610983] ⟨3227534663593, 5, [(2, 3), (3, 1), (134480610983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_134480610983
  · decide +kernel

theorem prime_3227534664043 : Nat.Prime 3227534664043 := by
  apply nodeValid_prime [2, 3, 13, 41378649539] ⟨3227534664043, 3, [(2, 1), (3, 1), (13, 1), (41378649539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41378649539
  · decide +kernel

theorem prime_3227534751559 : Nat.Prime 3227534751559 := by
  apply nodeValid_prime [2, 3, 13, 19, 114622301] ⟨3227534751559, 15, [(2, 1), (3, 1), (13, 1), (19, 2), (114622301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_114622301
  · decide +kernel

theorem prime_3230417937151 : Nat.Prime 3230417937151 := by
  apply nodeValid_prime [2, 3, 5, 7178706527] ⟨3230417937151, 3, [(2, 1), (3, 2), (5, 2), (7178706527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7178706527
  · decide +kernel

theorem prime_3230417938861 : Nat.Prime 3230417938861 := by
  apply nodeValid_prime [2, 3, 5, 7, 2563823761] ⟨3230417938861, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (2563823761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2563823761
  · decide +kernel

theorem prime_3230418014023 : Nat.Prime 3230418014023 := by
  apply nodeValid_prime [2, 3, 19, 293, 96713311] ⟨3230418014023, 3, [(2, 1), (3, 1), (19, 1), (293, 1), (96713311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_293
    · exact prime_96713311
  · decide +kernel

theorem prime_3233303018819 : Nat.Prime 3233303018819 := by
  apply nodeValid_prime [2, 1616651509409] ⟨3233303018819, 2, [(2, 1), (1616651509409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1616651509409
  · decide +kernel

theorem prime_3233303026277 : Nat.Prime 3233303026277 := by
  apply nodeValid_prime [2, 808325756569] ⟨3233303026277, 2, [(2, 2), (808325756569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_808325756569
  · decide +kernel

theorem prime_3233303026433 : Nat.Prime 3233303026433 := by
  apply nodeValid_prime [2, 29, 89, 54983] ⟨3233303026433, 3, [(2, 8), (29, 1), (89, 2), (54983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_89
    · exact prime_54983
  · decide +kernel

theorem prime_3236189764033 : Nat.Prime 3236189764033 := by
  apply nodeValid_prime [2, 3, 23, 244277609] ⟨3236189764033, 5, [(2, 6), (3, 2), (23, 1), (244277609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_244277609
  · decide +kernel

theorem prime_3236189847419 : Nat.Prime 3236189847419 := by
  apply nodeValid_prime [2, 11, 5807, 25331417] ⟨3236189847419, 2, [(2, 1), (11, 1), (5807, 1), (25331417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_5807
    · exact prime_25331417
  · decide +kernel

theorem prime_3236189849099 : Nat.Prime 3236189849099 := by
  apply nodeValid_prime [2, 587, 2756550127] ⟨3236189849099, 2, [(2, 1), (587, 1), (2756550127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_587
    · exact prime_2756550127
  · decide +kernel

theorem prime_3239078248933 : Nat.Prime 3239078248933 := by
  apply nodeValid_prime [2, 3, 23, 24821, 472817] ⟨3239078248933, 2, [(2, 2), (3, 1), (23, 1), (24821, 1), (472817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_24821
    · exact prime_472817
  · decide +kernel

theorem prime_3239078269969 : Nat.Prime 3239078269969 := by
  apply nodeValid_prime [2, 3, 28349, 793453] ⟨3239078269969, 7, [(2, 4), (3, 2), (28349, 1), (793453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28349
    · exact prime_793453
  · decide +kernel

theorem prime_3239078270803 : Nat.Prime 3239078270803 := by
  apply nodeValid_prime [2, 3, 11, 2843, 17262379] ⟨3239078270803, 2, [(2, 1), (3, 1), (11, 1), (2843, 1), (17262379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2843
    · exact prime_17262379
  · decide +kernel

theorem prime_3241968455933 : Nat.Prime 3241968455933 := by
  apply nodeValid_prime [2, 211, 3841194853] ⟨3241968455933, 2, [(2, 2), (211, 1), (3841194853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_3841194853
  · decide +kernel

theorem prime_3241968457433 : Nat.Prime 3241968457433 := by
  apply nodeValid_prime [2, 263, 1540859533] ⟨3241968457433, 3, [(2, 3), (263, 1), (1540859533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_1540859533
  · decide +kernel

theorem prime_3241968477707 : Nat.Prime 3241968477707 := by
  apply nodeValid_prime [2, 7, 4725901571] ⟨3241968477707, 5, [(2, 1), (7, 3), (4725901571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4725901571
  · decide +kernel

theorem prime_3244860418717 : Nat.Prime 3244860418717 := by
  apply nodeValid_prime [2, 3, 7, 557, 1301, 5923] ⟨3244860418717, 14, [(2, 2), (3, 3), (7, 1), (557, 1), (1301, 1), (5923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_557
    · exact prime_1301
    · exact prime_5923
  · decide +kernel

theorem prime_3244860422539 : Nat.Prime 3244860422539 := by
  apply nodeValid_prime [2, 3, 7, 19, 83, 457, 107201] ⟨3244860422539, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (83, 1), (457, 1), (107201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_83
    · exact prime_457
    · exact prime_107201
  · decide +kernel

theorem prime_3244860447419 : Nat.Prime 3244860447419 := by
  apply nodeValid_prime [2, 59, 107, 503, 510931] ⟨3244860447419, 2, [(2, 1), (59, 1), (107, 1), (503, 1), (510931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_107
    · exact prime_503
    · exact prime_510931
  · decide +kernel

theorem prime_3247754174381 : Nat.Prime 3247754174381 := by
  apply nodeValid_prime [2, 5, 641, 253334959] ⟨3247754174381, 7, [(2, 2), (5, 1), (641, 1), (253334959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
    · exact prime_253334959
  · decide +kernel

theorem prime_3247754192171 : Nat.Prime 3247754192171 := by
  apply nodeValid_prime [2, 5, 112207, 2894431] ⟨3247754192171, 2, [(2, 1), (5, 1), (112207, 1), (2894431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_112207
    · exact prime_2894431
  · decide +kernel

theorem prime_3247754194343 : Nat.Prime 3247754194343 := by
  apply nodeValid_prime [2, 7, 223, 5419, 191969] ⟨3247754194343, 5, [(2, 1), (7, 1), (223, 1), (5419, 1), (191969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_223
    · exact prime_5419
    · exact prime_191969
  · decide +kernel

theorem prime_3250649648413 : Nat.Prime 3250649648413 := by
  apply nodeValid_prime [2, 3, 251, 907, 396631] ⟨3250649648413, 2, [(2, 2), (3, 2), (251, 1), (907, 1), (396631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_907
    · exact prime_396631
  · decide +kernel

theorem prime_3250649648971 : Nat.Prime 3250649648971 := by
  apply nodeValid_prime [2, 3, 5, 19, 6659, 285473] ⟨3250649648971, 12, [(2, 1), (3, 2), (5, 1), (19, 1), (6659, 1), (285473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_6659
    · exact prime_285473
  · decide +kernel

theorem prime_3250649651129 : Nat.Prime 3250649651129 := by
  apply nodeValid_prime [2, 11, 2281, 16194301] ⟨3250649651129, 3, [(2, 3), (11, 1), (2281, 1), (16194301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2281
    · exact prime_16194301
  · decide +kernel

theorem prime_3253546868161 : Nat.Prime 3253546868161 := by
  apply nodeValid_prime [2, 3, 5, 3389111321] ⟨3253546868161, 11, [(2, 6), (3, 1), (5, 1), (3389111321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3389111321
  · decide +kernel

theorem prime_3253546886413 : Nat.Prime 3253546886413 := by
  apply nodeValid_prime [2, 3, 8167, 33198103] ⟨3253546886413, 5, [(2, 2), (3, 1), (8167, 1), (33198103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8167
    · exact prime_33198103
  · decide +kernel

theorem prime_3253546889137 : Nat.Prime 3253546889137 := by
  apply nodeValid_prime [2, 3, 31, 101, 1319, 5471] ⟨3253546889137, 5, [(2, 4), (3, 2), (31, 1), (101, 1), (1319, 1), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_101
    · exact prime_1319
    · exact prime_5471
  · decide +kernel

theorem prime_3256445802557 : Nat.Prime 3256445802557 := by
  apply nodeValid_prime [2, 1117, 728837467] ⟨3256445802557, 2, [(2, 2), (1117, 1), (728837467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1117
    · exact prime_728837467
  · decide +kernel

theorem prime_3256445802979 : Nat.Prime 3256445802979 := by
  apply nodeValid_prime [2, 3, 137, 440179211] ⟨3256445802979, 2, [(2, 1), (3, 3), (137, 1), (440179211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_440179211
  · decide +kernel

theorem prime_3256445823263 : Nat.Prime 3256445823263 := by
  apply nodeValid_prime [2, 47, 73, 6883, 68947] ⟨3256445823263, 5, [(2, 1), (47, 1), (73, 1), (6883, 1), (68947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_73
    · exact prime_6883
    · exact prime_68947
  · decide +kernel

theorem prime_3259346359609 : Nat.Prime 3259346359609 := by
  apply nodeValid_prime [2, 3, 45268699439] ⟨3259346359609, 11, [(2, 3), (3, 2), (45268699439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45268699439
  · decide +kernel

theorem prime_3259346529671 : Nat.Prime 3259346529671 := by
  apply nodeValid_prime [2, 5, 7, 11, 23059, 183569] ⟨3259346529671, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (23059, 1), (183569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23059
    · exact prime_183569
  · decide +kernel

theorem prime_3262248971231 : Nat.Prime 3262248971231 := by
  apply nodeValid_prime [2, 5, 1163, 280502921] ⟨3262248971231, 17, [(2, 1), (5, 1), (1163, 1), (280502921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1163
    · exact prime_280502921
  · decide +kernel

theorem prime_3262248971537 : Nat.Prime 3262248971537 := by
  apply nodeValid_prime [2, 43, 103, 46035349] ⟨3262248971537, 3, [(2, 4), (43, 1), (103, 1), (46035349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_103
    · exact prime_46035349
  · decide +kernel

theorem prime_3262248980477 : Nat.Prime 3262248980477 := by
  apply nodeValid_prime [2, 751, 1085968369] ⟨3262248980477, 2, [(2, 2), (751, 1), (1085968369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_751
    · exact prime_1085968369
  · decide +kernel

theorem prime_3265153145167 : Nat.Prime 3265153145167 := by
  apply nodeValid_prime [2, 3, 11, 49472017351] ⟨3265153145167, 5, [(2, 1), (3, 1), (11, 1), (49472017351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_49472017351
  · decide +kernel

theorem prime_3265153145557 : Nat.Prime 3265153145557 := by
  apply nodeValid_prime [2, 3, 272096095463] ⟨3265153145557, 5, [(2, 2), (3, 1), (272096095463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_272096095463
  · decide +kernel

theorem prime_3265153173343 : Nat.Prime 3265153173343 := by
  apply nodeValid_prime [2, 3, 17, 19, 4729, 118757] ⟨3265153173343, 3, [(2, 1), (3, 2), (17, 1), (19, 1), (4729, 1), (118757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_4729
    · exact prime_118757
  · decide +kernel

theorem prime_3268059113779 : Nat.Prime 3268059113779 := by
  apply nodeValid_prime [2, 3, 23, 37, 1579, 405347] ⟨3268059113779, 2, [(2, 1), (3, 1), (23, 1), (37, 1), (1579, 1), (405347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
    · exact prime_1579
    · exact prime_405347
  · decide +kernel

theorem prime_3268059174077 : Nat.Prime 3268059174077 := by
  apply nodeValid_prime [2, 131, 6236754149] ⟨3268059174077, 2, [(2, 2), (131, 1), (6236754149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_6236754149
  · decide +kernel

theorem prime_3268059177209 : Nat.Prime 3268059177209 := by
  apply nodeValid_prime [2, 7, 59, 151, 2347, 2791] ⟨3268059177209, 3, [(2, 3), (7, 1), (59, 1), (151, 1), (2347, 1), (2791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_151
    · exact prime_2347
    · exact prime_2791
  · decide +kernel

theorem prime_3270966795269 : Nat.Prime 3270966795269 := by
  apply nodeValid_prime [2, 173, 2383, 1983563] ⟨3270966795269, 2, [(2, 2), (173, 1), (2383, 1), (1983563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_2383
    · exact prime_1983563
  · decide +kernel

theorem prime_3270966814637 : Nat.Prime 3270966814637 := by
  apply nodeValid_prime [2, 817741703659] ⟨3270966814637, 2, [(2, 2), (817741703659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_817741703659
  · decide +kernel

theorem prime_3270966814943 : Nat.Prime 3270966814943 := by
  apply nodeValid_prime [2, 1635483407471] ⟨3270966814943, 5, [(2, 1), (1635483407471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1635483407471
  · decide +kernel

theorem prime_3273876222583 : Nat.Prime 3273876222583 := by
  apply nodeValid_prime [2, 3, 7, 47, 1621, 1023133] ⟨3273876222583, 3, [(2, 1), (3, 1), (7, 1), (47, 1), (1621, 1), (1023133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_1621
    · exact prime_1023133
  · decide +kernel

theorem prime_3273876222973 : Nat.Prime 3273876222973 := by
  apply nodeValid_prime [2, 3, 59, 157, 313, 94099] ⟨3273876222973, 2, [(2, 2), (3, 1), (59, 1), (157, 1), (313, 1), (94099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_157
    · exact prime_313
    · exact prime_94099
  · decide +kernel

theorem prime_3273876226711 : Nat.Prime 3273876226711 := by
  apply nodeValid_prime [2, 3, 5, 19, 239, 661, 12119] ⟨3273876226711, 3, [(2, 1), (3, 2), (5, 1), (19, 1), (239, 1), (661, 1), (12119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_239
    · exact prime_661
    · exact prime_12119
  · decide +kernel

end Sude.Lucas.Generated
