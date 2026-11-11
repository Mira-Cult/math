import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0130
import Sude.GeneratedFTT.N0132
import Sude.GeneratedFTT.N0135

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_14951 : Nat.Prime 14951 := by
  apply nodeValid_prime [2, 5, 13, 23] ⟨14951, 19, [(2, 1), (5, 2), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_31729 : Nat.Prime 31729 := by
  apply nodeValid_prime [2, 3, 661] ⟨31729, 7, [(2, 4), (3, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_661
  · decide +kernel

theorem prime_37337 : Nat.Prime 37337 := by
  apply nodeValid_prime [2, 13, 359] ⟨37337, 3, [(2, 3), (13, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_359
  · decide +kernel

theorem prime_44269 : Nat.Prime 44269 := by
  apply nodeValid_prime [2, 3, 7, 17, 31] ⟨44269, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_50591 : Nat.Prime 50591 := by
  apply nodeValid_prime [2, 5, 5059] ⟨50591, 7, [(2, 1), (5, 1), (5059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5059
  · decide +kernel

theorem prime_51473 : Nat.Prime 51473 := by
  apply nodeValid_prime [2, 3217] ⟨51473, 3, [(2, 4), (3217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3217
  · decide +kernel

theorem prime_52769 : Nat.Prime 52769 := by
  apply nodeValid_prime [2, 17, 97] ⟨52769, 3, [(2, 5), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_64381 : Nat.Prime 64381 := by
  apply nodeValid_prime [2, 3, 5, 29, 37] ⟨64381, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_76777 : Nat.Prime 76777 := by
  apply nodeValid_prime [2, 3, 7, 457] ⟨76777, 5, [(2, 3), (3, 1), (7, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_457
  · decide +kernel

theorem prime_99563 : Nat.Prime 99563 := by
  apply nodeValid_prime [2, 67, 743] ⟨99563, 2, [(2, 1), (67, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_743
  · decide +kernel

theorem prime_101503 : Nat.Prime 101503 := by
  apply nodeValid_prime [2, 3, 5639] ⟨101503, 5, [(2, 1), (3, 2), (5639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5639
  · decide +kernel

theorem prime_107671 : Nat.Prime 107671 := by
  apply nodeValid_prime [2, 3, 5, 37, 97] ⟨107671, 6, [(2, 1), (3, 1), (5, 1), (37, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_97
  · decide +kernel

theorem prime_111409 : Nat.Prime 111409 := by
  apply nodeValid_prime [2, 3, 11, 211] ⟨111409, 31, [(2, 4), (3, 1), (11, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_211
  · decide +kernel

theorem prime_124427 : Nat.Prime 124427 := by
  apply nodeValid_prime [2, 62213] ⟨124427, 2, [(2, 1), (62213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_62213
  · decide +kernel

theorem prime_131861 : Nat.Prime 131861 := by
  apply nodeValid_prime [2, 5, 19, 347] ⟨131861, 2, [(2, 2), (5, 1), (19, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_347
  · decide +kernel

theorem prime_139123 : Nat.Prime 139123 := by
  apply nodeValid_prime [2, 3, 59, 131] ⟨139123, 2, [(2, 1), (3, 2), (59, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_131
  · decide +kernel

theorem prime_228929 : Nat.Prime 228929 := by
  apply nodeValid_prime [2, 7, 73] ⟨228929, 3, [(2, 6), (7, 2), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_238159 : Nat.Prime 238159 := by
  apply nodeValid_prime [2, 3, 101, 131] ⟨238159, 3, [(2, 1), (3, 2), (101, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_131
  · decide +kernel

theorem prime_247259 : Nat.Prime 247259 := by
  apply nodeValid_prime [2, 11, 11239] ⟨247259, 2, [(2, 1), (11, 1), (11239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11239
  · decide +kernel

theorem prime_252209 : Nat.Prime 252209 := by
  apply nodeValid_prime [2, 11, 1433] ⟨252209, 3, [(2, 4), (11, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1433
  · decide +kernel

theorem prime_263723 : Nat.Prime 263723 := by
  apply nodeValid_prime [2, 131861] ⟨263723, 2, [(2, 1), (131861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_131861
  · decide +kernel

theorem prime_299371 : Nat.Prime 299371 := by
  apply nodeValid_prime [2, 3, 5, 17, 587] ⟨299371, 7, [(2, 1), (3, 1), (5, 1), (17, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_587
  · decide +kernel

theorem prime_300239 : Nat.Prime 300239 := by
  apply nodeValid_prime [2, 19, 7901] ⟨300239, 7, [(2, 1), (19, 1), (7901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_7901
  · decide +kernel

theorem prime_306827 : Nat.Prime 306827 := by
  apply nodeValid_prime [2, 13, 11801] ⟨306827, 2, [(2, 1), (13, 1), (11801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_11801
  · decide +kernel

theorem prime_324931 : Nat.Prime 324931 := by
  apply nodeValid_prime [2, 3, 5, 10831] ⟨324931, 14, [(2, 1), (3, 1), (5, 1), (10831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10831
  · decide +kernel

theorem prime_329683 : Nat.Prime 329683 := by
  apply nodeValid_prime [2, 3, 23, 2389] ⟨329683, 2, [(2, 1), (3, 1), (23, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2389
  · decide +kernel

theorem prime_363809 : Nat.Prime 363809 := by
  apply nodeValid_prime [2, 11369] ⟨363809, 3, [(2, 5), (11369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11369
  · decide +kernel

theorem prime_400601 : Nat.Prime 400601 := by
  apply nodeValid_prime [2, 5, 2003] ⟨400601, 3, [(2, 3), (5, 2), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2003
  · decide +kernel

theorem prime_475691 : Nat.Prime 475691 := by
  apply nodeValid_prime [2, 5, 47569] ⟨475691, 2, [(2, 1), (5, 1), (47569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47569
  · decide +kernel

theorem prime_599843 : Nat.Prime 599843 := by
  apply nodeValid_prime [2, 107, 2803] ⟨599843, 2, [(2, 1), (107, 1), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_2803
  · decide +kernel

theorem prime_675253 : Nat.Prime 675253 := by
  apply nodeValid_prime [2, 3, 18757] ⟨675253, 6, [(2, 2), (3, 2), (18757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18757
  · decide +kernel

theorem prime_702353 : Nat.Prime 702353 := by
  apply nodeValid_prime [2, 7, 6271] ⟨702353, 3, [(2, 4), (7, 1), (6271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6271
  · decide +kernel

theorem prime_851117 : Nat.Prime 851117 := by
  apply nodeValid_prime [2, 7, 113, 269] ⟨851117, 2, [(2, 2), (7, 1), (113, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_269
  · decide +kernel

theorem prime_860809 : Nat.Prime 860809 := by
  apply nodeValid_prime [2, 3, 13, 31, 89] ⟨860809, 7, [(2, 3), (3, 1), (13, 1), (31, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_89
  · decide +kernel

theorem prime_1022773 : Nat.Prime 1022773 := by
  apply nodeValid_prime [2, 3, 29, 2939] ⟨1022773, 2, [(2, 2), (3, 1), (29, 1), (2939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2939
  · decide +kernel

theorem prime_1146989 : Nat.Prime 1146989 := by
  apply nodeValid_prime [2, 47, 6101] ⟨1146989, 2, [(2, 2), (47, 1), (6101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_6101
  · decide +kernel

theorem prime_1261289 : Nat.Prime 1261289 := by
  apply nodeValid_prime [2, 7, 101, 223] ⟨1261289, 3, [(2, 3), (7, 1), (101, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_223
  · decide +kernel

theorem prime_2225969 : Nat.Prime 2225969 := by
  apply nodeValid_prime [2, 139123] ⟨2225969, 3, [(2, 4), (139123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_139123
  · decide +kernel

theorem prime_2428099 : Nat.Prime 2428099 := by
  apply nodeValid_prime [2, 3, 89, 4547] ⟨2428099, 3, [(2, 1), (3, 1), (89, 1), (4547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_4547
  · decide +kernel

theorem prime_2524651 : Nat.Prime 2524651 := by
  apply nodeValid_prime [2, 3, 5, 16831] ⟨2524651, 14, [(2, 1), (3, 1), (5, 2), (16831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16831
  · decide +kernel

theorem prime_2995081 : Nat.Prime 2995081 := by
  apply nodeValid_prime [2, 3, 5, 11, 2269] ⟨2995081, 21, [(2, 3), (3, 1), (5, 1), (11, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2269
  · decide +kernel

theorem prime_3191327 : Nat.Prime 3191327 := by
  apply nodeValid_prime [2, 31, 51473] ⟨3191327, 5, [(2, 1), (31, 1), (51473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_51473
  · decide +kernel

theorem prime_3204809 : Nat.Prime 3204809 := by
  apply nodeValid_prime [2, 400601] ⟨3204809, 3, [(2, 3), (400601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_400601
  · decide +kernel

theorem prime_3316321 : Nat.Prime 3316321 := by
  apply nodeValid_prime [2, 3, 5, 7, 47] ⟨3316321, 11, [(2, 5), (3, 2), (5, 1), (7, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_3318719 : Nat.Prime 3318719 := by
  apply nodeValid_prime [2, 13, 127643] ⟨3318719, 23, [(2, 1), (13, 1), (127643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_127643
  · decide +kernel

theorem prime_4906333 : Nat.Prime 4906333 := by
  apply nodeValid_prime [2, 3, 19, 797] ⟨4906333, 6, [(2, 2), (3, 4), (19, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_797
  · decide +kernel

theorem prime_7371197 : Nat.Prime 7371197 := by
  apply nodeValid_prime [2, 7, 263257] ⟨7371197, 2, [(2, 2), (7, 1), (263257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_263257
  · decide +kernel

theorem prime_8382389 : Nat.Prime 8382389 := by
  apply nodeValid_prime [2, 7, 299371] ⟨8382389, 2, [(2, 2), (7, 1), (299371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_299371
  · decide +kernel

theorem prime_9499309 : Nat.Prime 9499309 := by
  apply nodeValid_prime [2, 3, 7, 13, 8699] ⟨9499309, 2, [(2, 2), (3, 1), (7, 1), (13, 1), (8699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_8699
  · decide +kernel

theorem prime_9541283 : Nat.Prime 9541283 := by
  apply nodeValid_prime [2, 47, 101503] ⟨9541283, 2, [(2, 1), (47, 1), (101503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_101503
  · decide +kernel

theorem prime_9712397 : Nat.Prime 9712397 := by
  apply nodeValid_prime [2, 2428099] ⟨9712397, 2, [(2, 2), (2428099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2428099
  · decide +kernel

theorem prime_10311151 : Nat.Prime 10311151 := by
  apply nodeValid_prime [2, 3, 5, 53, 1297] ⟨10311151, 7, [(2, 1), (3, 1), (5, 2), (53, 1), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_1297
  · decide +kernel

theorem prime_10804049 : Nat.Prime 10804049 := by
  apply nodeValid_prime [2, 675253] ⟨10804049, 3, [(2, 4), (675253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_675253
  · decide +kernel

theorem prime_11035723 : Nat.Prime 11035723 := by
  apply nodeValid_prime [2, 3, 23, 211, 379] ⟨11035723, 2, [(2, 1), (3, 1), (23, 1), (211, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_211
    · exact prime_379
  · decide +kernel

theorem prime_12710051 : Nat.Prime 12710051 := by
  apply nodeValid_prime [2, 5, 17, 19, 787] ⟨12710051, 2, [(2, 1), (5, 2), (17, 1), (19, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_787
  · decide +kernel

theorem prime_17336443 : Nat.Prime 17336443 := by
  apply nodeValid_prime [2, 3, 59, 48973] ⟨17336443, 2, [(2, 1), (3, 1), (59, 1), (48973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_48973
  · decide +kernel

theorem prime_17680177 : Nat.Prime 17680177 := by
  apply nodeValid_prime [2, 3, 59, 2081] ⟨17680177, 5, [(2, 4), (3, 2), (59, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2081
  · decide +kernel

theorem prime_17995291 : Nat.Prime 17995291 := by
  apply nodeValid_prime [2, 3, 5, 599843] ⟨17995291, 2, [(2, 1), (3, 1), (5, 1), (599843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_599843
  · decide +kernel

theorem prime_18430903 : Nat.Prime 18430903 := by
  apply nodeValid_prime [2, 3, 7, 16253] ⟨18430903, 5, [(2, 1), (3, 4), (7, 1), (16253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_16253
  · decide +kernel

theorem prime_19538537 : Nat.Prime 19538537 := by
  apply nodeValid_prime [2, 19, 191, 673] ⟨19538537, 3, [(2, 3), (19, 1), (191, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_191
    · exact prime_673
  · decide +kernel

theorem prime_29531717 : Nat.Prime 29531717 := by
  apply nodeValid_prime [2, 31, 238159] ⟨29531717, 3, [(2, 2), (31, 1), (238159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_238159
  · decide +kernel

theorem prime_36002009 : Nat.Prime 36002009 := by
  apply nodeValid_prime [2, 7, 43, 14951] ⟨36002009, 3, [(2, 3), (7, 1), (43, 1), (14951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_14951
  · decide +kernel

theorem prime_38323517 : Nat.Prime 38323517 := by
  apply nodeValid_prime [2, 7, 11, 124427] ⟨38323517, 2, [(2, 2), (7, 1), (11, 1), (124427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_124427
  · decide +kernel

theorem prime_44391001 : Nat.Prime 44391001 := by
  apply nodeValid_prime [2, 3, 5, 14797] ⟨44391001, 11, [(2, 3), (3, 1), (5, 3), (14797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14797
  · decide +kernel

theorem prime_57247699 : Nat.Prime 57247699 := by
  apply nodeValid_prime [2, 3, 9541283] ⟨57247699, 2, [(2, 1), (3, 1), (9541283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9541283
  · decide +kernel

theorem prime_74380051 : Nat.Prime 74380051 := by
  apply nodeValid_prime [2, 3, 5, 67, 2467] ⟨74380051, 3, [(2, 1), (3, 2), (5, 2), (67, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_2467
  · decide +kernel

theorem prime_86432393 : Nat.Prime 86432393 := by
  apply nodeValid_prime [2, 10804049] ⟨86432393, 3, [(2, 3), (10804049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10804049
  · decide +kernel

theorem prime_90224633 : Nat.Prime 90224633 := by
  apply nodeValid_prime [2, 31, 363809] ⟨90224633, 3, [(2, 3), (31, 1), (363809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_363809
  · decide +kernel

theorem prime_100585951 : Nat.Prime 100585951 := by
  apply nodeValid_prime [2, 3, 5, 61, 10993] ⟨100585951, 13, [(2, 1), (3, 1), (5, 2), (61, 1), (10993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_10993
  · decide +kernel

theorem prime_112404923 : Nat.Prime 112404923 := by
  apply nodeValid_prime [2, 7, 1146989] ⟨112404923, 2, [(2, 1), (7, 2), (1146989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1146989
  · decide +kernel

theorem prime_146265829 : Nat.Prime 146265829 := by
  apply nodeValid_prime [2, 3, 1747, 6977] ⟨146265829, 2, [(2, 2), (3, 1), (1747, 1), (6977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1747
    · exact prime_6977
  · decide +kernel

theorem prime_166815323 : Nat.Prime 166815323 := by
  apply nodeValid_prime [2, 17, 4906333] ⟨166815323, 2, [(2, 1), (17, 1), (4906333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4906333
  · decide +kernel

theorem prime_172864787 : Nat.Prime 172864787 := by
  apply nodeValid_prime [2, 86432393] ⟨172864787, 2, [(2, 1), (86432393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_86432393
  · decide +kernel

theorem prime_172927367 : Nat.Prime 172927367 := by
  apply nodeValid_prime [2, 17, 79, 64381] ⟨172927367, 5, [(2, 1), (17, 1), (79, 1), (64381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_79
    · exact prime_64381
  · decide +kernel

theorem prime_176461409 : Nat.Prime 176461409 := by
  apply nodeValid_prime [2, 109, 50591] ⟨176461409, 3, [(2, 5), (109, 1), (50591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_50591
  · decide +kernel

theorem prime_335012077 : Nat.Prime 335012077 := by
  apply nodeValid_prime [2, 3, 7, 457, 2909] ⟨335012077, 2, [(2, 2), (3, 2), (7, 1), (457, 1), (2909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_457
    · exact prime_2909
  · decide +kernel

theorem prime_337179373 : Nat.Prime 337179373 := by
  apply nodeValid_prime [2, 3, 37, 97, 7829] ⟨337179373, 2, [(2, 2), (3, 1), (37, 1), (97, 1), (7829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_97
    · exact prime_7829
  · decide +kernel

theorem prime_546818953 : Nat.Prime 546818953 := by
  apply nodeValid_prime [2, 3, 1259, 18097] ⟨546818953, 5, [(2, 3), (3, 1), (1259, 1), (18097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1259
    · exact prime_18097
  · decide +kernel

theorem prime_572241409 : Nat.Prime 572241409 := by
  apply nodeValid_prime [2, 3, 37, 10069] ⟨572241409, 7, [(2, 9), (3, 1), (37, 1), (10069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_10069
  · decide +kernel

theorem prime_606382039 : Nat.Prime 606382039 := by
  apply nodeValid_prime [2, 3, 79, 47381] ⟨606382039, 3, [(2, 1), (3, 4), (79, 1), (47381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_47381
  · decide +kernel

theorem prime_986097953 : Nat.Prime 986097953 := by
  apply nodeValid_prime [2, 7, 23, 37, 739] ⟨986097953, 3, [(2, 5), (7, 2), (23, 1), (37, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_37
    · exact prime_739
  · decide +kernel

theorem prime_1147955581 : Nat.Prime 1147955581 := by
  apply nodeValid_prime [2, 3, 5, 1693, 3767] ⟨1147955581, 10, [(2, 2), (3, 2), (5, 1), (1693, 1), (3767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1693
    · exact prime_3767
  · decide +kernel

theorem prime_1382918297 : Nat.Prime 1382918297 := by
  apply nodeValid_prime [2, 172864787] ⟨1382918297, 3, [(2, 3), (172864787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_172864787
  · decide +kernel

theorem prime_2984615981 : Nat.Prime 2984615981 := by
  apply nodeValid_prime [2, 5, 3371, 44269] ⟨2984615981, 2, [(2, 2), (5, 1), (3371, 1), (44269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3371
    · exact prime_44269
  · decide +kernel

theorem prime_2999432593 : Nat.Prime 2999432593 := by
  apply nodeValid_prime [2, 3, 13, 131, 151] ⟨2999432593, 5, [(2, 4), (3, 6), (13, 1), (131, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_131
    · exact prime_151
  · decide +kernel

theorem prime_3191000801 : Nat.Prime 3191000801 := by
  apply nodeValid_prime [2, 5, 13, 306827] ⟨3191000801, 3, [(2, 5), (5, 2), (13, 1), (306827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_306827
  · decide +kernel

theorem prime_3304613261 : Nat.Prime 3304613261 := by
  apply nodeValid_prime [2, 5, 13, 12710051] ⟨3304613261, 2, [(2, 2), (5, 1), (13, 1), (12710051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_12710051
  · decide +kernel

theorem prime_4929082127 : Nat.Prime 4929082127 := by
  apply nodeValid_prime [2, 2591, 951193] ⟨4929082127, 5, [(2, 1), (2591, 1), (951193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2591
    · exact prime_951193
  · decide +kernel

theorem prime_5426681551 : Nat.Prime 5426681551 := by
  apply nodeValid_prime [2, 3, 5, 29, 89, 107, 131] ⟨5426681551, 11, [(2, 1), (3, 1), (5, 2), (29, 1), (89, 1), (107, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_89
    · exact prime_107
    · exact prime_131
  · decide +kernel

theorem prime_8996159407 : Nat.Prime 8996159407 := by
  apply nodeValid_prime [2, 3, 13, 19, 163, 167, 223] ⟨8996159407, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (163, 1), (167, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_163
    · exact prime_167
    · exact prime_223
  · decide +kernel

theorem prime_9958278133 : Nat.Prime 9958278133 := by
  apply nodeValid_prime [2, 3, 11, 8382389] ⟨9958278133, 2, [(2, 2), (3, 3), (11, 1), (8382389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_8382389
  · decide +kernel

theorem prime_10685300287 : Nat.Prime 10685300287 := by
  apply nodeValid_prime [2, 3, 31, 577, 99563] ⟨10685300287, 3, [(2, 1), (3, 1), (31, 1), (577, 1), (99563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_577
    · exact prime_99563
  · decide +kernel

theorem prime_11344133767 : Nat.Prime 11344133767 := by
  apply nodeValid_prime [2, 3, 7, 61, 337, 1877] ⟨11344133767, 7, [(2, 1), (3, 1), (7, 2), (61, 1), (337, 1), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_337
    · exact prime_1877
  · decide +kernel

theorem prime_13677328523 : Nat.Prime 13677328523 := by
  apply nodeValid_prime [2, 11, 13, 29, 126851] ⟨13677328523, 2, [(2, 1), (11, 1), (13, 2), (29, 1), (126851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_29
    · exact prime_126851
  · decide +kernel

theorem prime_18584011421 : Nat.Prime 18584011421 := by
  apply nodeValid_prime [2, 5, 13, 29, 163, 15121] ⟨18584011421, 3, [(2, 2), (5, 1), (13, 1), (29, 1), (163, 1), (15121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
    · exact prime_163
    · exact prime_15121
  · decide +kernel

theorem prime_29343109693 : Nat.Prime 29343109693 := by
  apply nodeValid_prime [2, 3, 13, 17, 851117] ⟨29343109693, 2, [(2, 2), (3, 1), (13, 2), (17, 1), (851117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_851117
  · decide +kernel

theorem prime_43689591161 : Nat.Prime 43689591161 := by
  apply nodeValid_prime [2, 5, 3313, 329683] ⟨43689591161, 3, [(2, 3), (5, 1), (3313, 1), (329683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3313
    · exact prime_329683
  · decide +kernel

theorem prime_87379182323 : Nat.Prime 87379182323 := by
  apply nodeValid_prime [2, 43689591161] ⟨87379182323, 2, [(2, 1), (43689591161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43689591161
  · decide +kernel

theorem prime_99382005467 : Nat.Prime 99382005467 := by
  apply nodeValid_prime [2, 39397, 1261289] ⟨99382005467, 2, [(2, 1), (39397, 1), (1261289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_39397
    · exact prime_1261289
  · decide +kernel

theorem prime_274435037011 : Nat.Prime 274435037011 := by
  apply nodeValid_prime [2, 3, 5, 107, 9499309] ⟨274435037011, 7, [(2, 1), (3, 3), (5, 1), (107, 1), (9499309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
    · exact prime_9499309
  · decide +kernel

theorem prime_349752608389 : Nat.Prime 349752608389 := by
  apply nodeValid_prime [2, 3, 29, 335012077] ⟨349752608389, 2, [(2, 2), (3, 2), (29, 1), (335012077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_335012077
  · decide +kernel

theorem prime_431815651537 : Nat.Prime 431815651537 := by
  apply nodeValid_prime [2, 3, 8996159407] ⟨431815651537, 5, [(2, 4), (3, 1), (8996159407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8996159407
  · decide +kernel

theorem prime_1294576157291 : Nat.Prime 1294576157291 := by
  apply nodeValid_prime [2, 5, 13, 9958278133] ⟨1294576157291, 2, [(2, 1), (5, 1), (13, 1), (9958278133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_9958278133
  · decide +kernel

theorem prime_1926235773043 : Nat.Prime 1926235773043 := by
  apply nodeValid_prime [2, 3, 7, 1553, 29531717] ⟨1926235773043, 3, [(2, 1), (3, 1), (7, 1), (1553, 1), (29531717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1553
    · exact prime_29531717
  · decide +kernel

theorem prime_3844684022213 : Nat.Prime 3844684022213 := by
  apply nodeValid_prime [2, 11, 87379182323] ⟨3844684022213, 2, [(2, 2), (11, 1), (87379182323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_87379182323
  · decide +kernel

theorem prime_3849874545581 : Nat.Prime 3849874545581 := by
  apply nodeValid_prime [2, 5, 7, 107, 1019, 252209] ⟨3849874545581, 3, [(2, 2), (5, 1), (7, 1), (107, 1), (1019, 1), (252209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_107
    · exact prime_1019
    · exact prime_252209
  · decide +kernel

theorem prime_7663456927253 : Nat.Prime 7663456927253 := by
  apply nodeValid_prime [2, 7, 17, 911, 2524651] ⟨7663456927253, 2, [(2, 2), (7, 2), (17, 1), (911, 1), (2524651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_911
    · exact prime_2524651
  · decide +kernel

theorem prime_7663456927279 : Nat.Prime 7663456927279 := by
  apply nodeValid_prime [2, 3, 37, 173, 269, 247259] ⟨7663456927279, 3, [(2, 1), (3, 2), (37, 1), (173, 1), (269, 1), (247259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_173
    · exact prime_269
    · exact prime_247259
  · decide +kernel

theorem prime_7663456949329 : Nat.Prime 7663456949329 := by
  apply nodeValid_prime [2, 3, 31, 572241409] ⟨7663456949329, 17, [(2, 4), (3, 3), (31, 1), (572241409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_572241409
  · decide +kernel

theorem prime_7668634204753 : Nat.Prime 7668634204753 := by
  apply nodeValid_prime [2, 3, 59, 61, 44391001] ⟨7668634204753, 10, [(2, 4), (3, 1), (59, 1), (61, 1), (44391001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_61
    · exact prime_44391001
  · decide +kernel

theorem prime_7668634206971 : Nat.Prime 7668634206971 := by
  apply nodeValid_prime [2, 5, 11, 99259, 702353] ⟨7668634206971, 2, [(2, 1), (5, 1), (11, 1), (99259, 1), (702353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_99259
    · exact prime_702353
  · decide +kernel

theorem prime_7668634426493 : Nat.Prime 7668634426493 := by
  apply nodeValid_prime [2, 13, 11344133767] ⟨7668634426493, 2, [(2, 2), (13, 2), (11344133767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_11344133767
  · decide +kernel

theorem prime_7673814121639 : Nat.Prime 7673814121639 := by
  apply nodeValid_prime [2, 3, 7, 3541, 7371197] ⟨7673814121639, 19, [(2, 1), (3, 1), (7, 2), (3541, 1), (7371197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3541
    · exact prime_7371197
  · decide +kernel

theorem prime_7673814122101 : Nat.Prime 7673814122101 := by
  apply nodeValid_prime [2, 3, 5, 7, 41, 53, 31729] ⟨7673814122101, 6, [(2, 2), (3, 1), (5, 2), (7, 1), (41, 1), (53, 2), (31729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_53
    · exact prime_31729
  · decide +kernel

theorem prime_7673814270247 : Nat.Prime 7673814270247 := by
  apply nodeValid_prime [2, 3, 1297, 986097953] ⟨7673814270247, 3, [(2, 1), (3, 1), (1297, 1), (986097953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1297
    · exact prime_986097953
  · decide +kernel

theorem prime_7678996465241 : Nat.Prime 7678996465241 := by
  apply nodeValid_prime [2, 5, 29, 89, 74380051] ⟨7678996465241, 3, [(2, 3), (5, 1), (29, 1), (89, 1), (74380051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_89
    · exact prime_74380051
  · decide +kernel

theorem prime_7678996465267 : Nat.Prime 7678996465267 := by
  apply nodeValid_prime [2, 3, 7, 83, 853, 860809] ⟨7678996465267, 3, [(2, 1), (3, 2), (7, 1), (83, 1), (853, 1), (860809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_853
    · exact prime_860809
  · decide +kernel

theorem prime_7678996490309 : Nat.Prime 7678996490309 := by
  apply nodeValid_prime [2, 11, 13, 37, 163, 2225969] ⟨7678996490309, 3, [(2, 2), (11, 1), (13, 1), (37, 1), (163, 1), (2225969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_37
    · exact prime_163
    · exact prime_2225969
  · decide +kernel

theorem prime_7684181036309 : Nat.Prime 7684181036309 := by
  apply nodeValid_prime [2, 7, 274435037011] ⟨7684181036309, 2, [(2, 2), (7, 1), (274435037011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_274435037011
  · decide +kernel

theorem prime_7684181038673 : Nat.Prime 7684181038673 := by
  apply nodeValid_prime [2, 2879, 166815323] ⟨7684181038673, 3, [(2, 4), (2879, 1), (166815323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2879
    · exact prime_166815323
  · decide +kernel

theorem prime_7684181076217 : Nat.Prime 7684181076217 := by
  apply nodeValid_prime [2, 3, 59, 5426681551] ⟨7684181076217, 5, [(2, 3), (3, 1), (59, 1), (5426681551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_5426681551
  · decide +kernel

theorem prime_7689368044427 : Nat.Prime 7689368044427 := by
  apply nodeValid_prime [2, 3844684022213] ⟨7689368044427, 2, [(2, 1), (3844684022213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3844684022213
  · decide +kernel

theorem prime_7689368117087 : Nat.Prime 7689368117087 := by
  apply nodeValid_prime [2, 79, 89, 546818953] ⟨7689368117087, 5, [(2, 1), (79, 1), (89, 1), (546818953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_89
    · exact prime_546818953
  · decide +kernel

theorem prime_7689368118121 : Nat.Prime 7689368118121 := by
  apply nodeValid_prime [2, 3, 5, 13, 4929082127] ⟨7689368118121, 11, [(2, 3), (3, 1), (5, 1), (13, 1), (4929082127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_4929082127
  · decide +kernel

theorem prime_7694557384559 : Nat.Prime 7694557384559 := by
  apply nodeValid_prime [2, 11, 349752608389] ⟨7694557384559, 11, [(2, 1), (11, 1), (349752608389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_349752608389
  · decide +kernel

theorem prime_7694557404509 : Nat.Prime 7694557404509 := by
  apply nodeValid_prime [2, 13, 107, 1382918297] ⟨7694557404509, 2, [(2, 2), (13, 1), (107, 1), (1382918297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_107
    · exact prime_1382918297
  · decide +kernel

theorem prime_7694557404913 : Nat.Prime 7694557404913 := by
  apply nodeValid_prime [2, 3, 7, 227, 2153, 15619] ⟨7694557404913, 5, [(2, 4), (3, 2), (7, 1), (227, 1), (2153, 1), (15619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_227
    · exact prime_2153
    · exact prime_15619
  · decide +kernel

theorem prime_7699748897741 : Nat.Prime 7699748897741 := by
  apply nodeValid_prime [2, 5, 37337, 10311151] ⟨7699748897741, 3, [(2, 2), (5, 1), (37337, 1), (10311151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37337
    · exact prime_10311151
  · decide +kernel

theorem prime_7699748898131 : Nat.Prime 7699748898131 := by
  apply nodeValid_prime [2, 5, 233, 3304613261] ⟨7699748898131, 2, [(2, 1), (5, 1), (233, 1), (3304613261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
    · exact prime_3304613261
  · decide +kernel

theorem prime_7699749091163 : Nat.Prime 7699749091163 := by
  apply nodeValid_prime [2, 3849874545581] ⟨7699749091163, 2, [(2, 1), (3849874545581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3849874545581
  · decide +kernel

theorem prime_7704943092173 : Nat.Prime 7704943092173 := by
  apply nodeValid_prime [2, 1926235773043] ⟨7704943092173, 2, [(2, 2), (1926235773043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1926235773043
  · decide +kernel

theorem prime_7704943092851 : Nat.Prime 7704943092851 := by
  apply nodeValid_prime [2, 5, 4021, 38323517] ⟨7704943092851, 2, [(2, 1), (5, 2), (4021, 1), (38323517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4021
    · exact prime_38323517
  · decide +kernel

theorem prime_7704943155587 : Nat.Prime 7704943155587 := by
  apply nodeValid_prime [2, 31, 11261, 11035723] ⟨7704943155587, 2, [(2, 1), (31, 1), (11261, 1), (11035723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_11261
    · exact prime_11035723
  · decide +kernel

theorem prime_7710139485427 : Nat.Prime 7710139485427 := by
  apply nodeValid_prime [2, 3, 7, 983, 3539, 52769] ⟨7710139485427, 2, [(2, 1), (3, 1), (7, 1), (983, 1), (3539, 1), (52769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_983
    · exact prime_3539
    · exact prime_52769
  · decide +kernel

theorem prime_7710139486219 : Nat.Prime 7710139486219 := by
  apply nodeValid_prime [2, 3, 13, 127, 761, 1022773] ⟨7710139486219, 3, [(2, 1), (3, 1), (13, 1), (127, 1), (761, 1), (1022773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_127
    · exact prime_761
    · exact prime_1022773
  · decide +kernel

theorem prime_7710139585063 : Nat.Prime 7710139585063 := by
  apply nodeValid_prime [2, 3, 2477, 172927367] ⟨7710139585063, 3, [(2, 1), (3, 2), (2477, 1), (172927367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2477
    · exact prime_172927367
  · decide +kernel

theorem prime_7715338388711 : Nat.Prime 7715338388711 := by
  apply nodeValid_prime [2, 5, 17, 47, 12577, 76777] ⟨7715338388711, 7, [(2, 1), (5, 1), (17, 1), (47, 1), (12577, 1), (76777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_47
    · exact prime_12577
    · exact prime_76777
  · decide +kernel

theorem prime_7715338412987 : Nat.Prime 7715338412987 := by
  apply nodeValid_prime [2, 17, 673, 337179373] ⟨7715338412987, 5, [(2, 1), (17, 1), (673, 1), (337179373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_673
    · exact prime_337179373
  · decide +kernel

theorem prime_7715338413487 : Nat.Prime 7715338413487 := by
  apply nodeValid_prime [2, 3, 11, 31, 193, 19538537] ⟨7715338413487, 3, [(2, 1), (3, 1), (11, 1), (31, 1), (193, 1), (19538537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_193
    · exact prime_19538537
  · decide +kernel

theorem prime_7720539494383 : Nat.Prime 7720539494383 := by
  apply nodeValid_prime [2, 3, 11, 13, 2999432593] ⟨7720539494383, 7, [(2, 1), (3, 2), (11, 1), (13, 1), (2999432593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_2999432593
  · decide +kernel

theorem prime_7720539494831 : Nat.Prime 7720539494831 := by
  apply nodeValid_prime [2, 5, 23, 37, 193, 349, 13469] ⟨7720539494831, 11, [(2, 1), (5, 1), (23, 1), (37, 1), (193, 1), (349, 1), (13469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_193
    · exact prime_349
    · exact prime_13469
  · decide +kernel

theorem prime_7720539566569 : Nat.Prime 7720539566569 := by
  apply nodeValid_prime [2, 3, 1823, 176461409] ⟨7720539566569, 13, [(2, 3), (3, 1), (1823, 1), (176461409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1823
    · exact prime_176461409
  · decide +kernel

theorem prime_7725743112749 : Nat.Prime 7725743112749 := by
  apply nodeValid_prime [2, 111409, 17336443] ⟨7725743112749, 2, [(2, 2), (111409, 1), (17336443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_111409
    · exact prime_17336443
  · decide +kernel

theorem prime_7725743115329 : Nat.Prime 7725743115329 := by
  apply nodeValid_prime [2, 7, 479, 36002009] ⟨7725743115329, 3, [(2, 6), (7, 1), (479, 1), (36002009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_479
    · exact prime_36002009
  · decide +kernel

theorem prime_7725743115913 : Nat.Prime 7725743115913 := by
  apply nodeValid_prime [2, 3, 33623, 3191327] ⟨7725743115913, 5, [(2, 3), (3, 2), (33623, 1), (3191327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33623
    · exact prime_3191327
  · decide +kernel

theorem prime_7730948751137 : Nat.Prime 7730948751137 := by
  apply nodeValid_prime [2, 13, 18584011421] ⟨7730948751137, 3, [(2, 5), (13, 1), (18584011421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_18584011421
  · decide +kernel

theorem prime_7730949024289 : Nat.Prime 7730949024289 := by
  apply nodeValid_prime [2, 3, 7, 37, 131, 263723] ⟨7730949024289, 22, [(2, 5), (3, 3), (7, 1), (37, 1), (131, 1), (263723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_131
    · exact prime_263723
  · decide +kernel

theorem prime_7736157308029 : Nat.Prime 7736157308029 := by
  apply nodeValid_prime [2, 3, 66377, 9712397] ⟨7736157308029, 2, [(2, 2), (3, 1), (66377, 1), (9712397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66377
    · exact prime_9712397
  · decide +kernel

theorem prime_7736157405497 : Nat.Prime 7736157405497 := by
  apply nodeValid_prime [2, 13, 228929, 324931] ⟨7736157405497, 3, [(2, 3), (13, 1), (228929, 1), (324931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_228929
    · exact prime_324931
  · decide +kernel

theorem prime_7736157407789 : Nat.Prime 7736157407789 := by
  apply nodeValid_prime [2, 181, 10685300287] ⟨7736157407789, 2, [(2, 2), (181, 1), (10685300287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_10685300287
  · decide +kernel

theorem prime_7741367943227 : Nat.Prime 7741367943227 := by
  apply nodeValid_prime [2, 1213, 3191000801] ⟨7741367943227, 2, [(2, 1), (1213, 1), (3191000801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1213
    · exact prime_3191000801
  · decide +kernel

theorem prime_7741367944019 : Nat.Prime 7741367944019 := by
  apply nodeValid_prime [2, 283, 13677328523] ⟨7741367944019, 2, [(2, 1), (283, 1), (13677328523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_13677328523
  · decide +kernel

theorem prime_7741367965021 : Nat.Prime 7741367965021 := by
  apply nodeValid_prime [2, 3, 5, 43, 71, 401, 105389] ⟨7741367965021, 2, [(2, 2), (3, 1), (5, 1), (43, 1), (71, 1), (401, 1), (105389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_71
    · exact prime_401
    · exact prime_105389
  · decide +kernel

theorem prime_7746580958617 : Nat.Prime 7746580958617 := by
  apply nodeValid_prime [2, 3, 32443, 3316321] ⟨7746580958617, 5, [(2, 3), (3, 2), (32443, 1), (3316321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32443
    · exact prime_3316321
  · decide +kernel

theorem prime_7746580958953 : Nat.Prime 7746580958953 := by
  apply nodeValid_prime [2, 3, 11, 29343109693] ⟨7746580958953, 5, [(2, 3), (3, 1), (11, 1), (29343109693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29343109693
  · decide +kernel

theorem prime_7746580989767 : Nat.Prime 7746580989767 := by
  apply nodeValid_prime [2, 349, 3463, 3204809] ⟨7746580989767, 5, [(2, 1), (349, 1), (3463, 1), (3204809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_349
    · exact prime_3463
    · exact prime_3204809
  · decide +kernel

theorem prime_7751796405343 : Nat.Prime 7751796405343 := by
  apply nodeValid_prime [2, 3, 11, 73, 146265829] ⟨7751796405343, 3, [(2, 1), (3, 1), (11, 2), (73, 1), (146265829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_146265829
  · decide +kernel

theorem prime_7751796426193 : Nat.Prime 7751796426193 := by
  apply nodeValid_prime [2, 3, 7, 13, 31, 57247699] ⟨7751796426193, 5, [(2, 4), (3, 1), (7, 1), (13, 1), (31, 1), (57247699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_57247699
  · decide +kernel

theorem prime_7751796426427 : Nat.Prime 7751796426427 := by
  apply nodeValid_prime [2, 3, 13, 99382005467] ⟨7751796426427, 11, [(2, 1), (3, 1), (13, 1), (99382005467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_99382005467
  · decide +kernel

theorem prime_7757014145611 : Nat.Prime 7757014145611 := by
  apply nodeValid_prime [2, 3, 5, 14029, 18430903] ⟨7757014145611, 10, [(2, 1), (3, 1), (5, 1), (14029, 1), (18430903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14029
    · exact prime_18430903
  · decide +kernel

theorem prime_7757014147879 : Nat.Prime 7757014147879 := by
  apply nodeValid_prime [2, 3, 71843, 17995291] ⟨7757014147879, 3, [(2, 1), (3, 1), (71843, 1), (17995291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71843
    · exact prime_17995291
  · decide +kernel

theorem prime_7757014193359 : Nat.Prime 7757014193359 := by
  apply nodeValid_prime [2, 3, 149, 2897, 2995081] ⟨7757014193359, 3, [(2, 1), (3, 1), (149, 1), (2897, 1), (2995081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_2897
    · exact prime_2995081
  · decide +kernel

theorem prime_7762234188413 : Nat.Prime 7762234188413 := by
  apply nodeValid_prime [2, 11, 683, 2339, 10039] ⟨7762234188413, 3, [(2, 2), (11, 2), (683, 1), (2339, 1), (10039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_683
    · exact prime_2339
    · exact prime_10039
  · decide +kernel

theorem prime_7762234189373 : Nat.Prime 7762234189373 := by
  apply nodeValid_prime [2, 13, 8443, 17680177] ⟨7762234189373, 2, [(2, 2), (13, 1), (8443, 1), (17680177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8443
    · exact prime_17680177
  · decide +kernel

theorem prime_7762234362689 : Nat.Prime 7762234362689 := by
  apply nodeValid_prime [2, 13, 83, 112404923] ⟨7762234362689, 3, [(2, 6), (13, 1), (83, 1), (112404923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_83
    · exact prime_112404923
  · decide +kernel

theorem prime_7767456918181 : Nat.Prime 7767456918181 := by
  apply nodeValid_prime [2, 3, 5, 599, 5297, 40801] ⟨7767456918181, 6, [(2, 2), (3, 1), (5, 1), (599, 1), (5297, 1), (40801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_599
    · exact prime_5297
    · exact prime_40801
  · decide +kernel

theorem prime_7767456943747 : Nat.Prime 7767456943747 := by
  apply nodeValid_prime [2, 3, 1294576157291] ⟨7767456943747, 2, [(2, 1), (3, 1), (1294576157291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1294576157291
  · decide +kernel

theorem prime_7767456943751 : Nat.Prime 7767456943751 := by
  apply nodeValid_prime [2, 5, 7, 37, 317, 15137] ⟨7767456943751, 7, [(2, 1), (5, 5), (7, 1), (37, 1), (317, 1), (15137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_317
    · exact prime_15137
  · decide +kernel

theorem prime_7772681727667 : Nat.Prime 7772681727667 := by
  apply nodeValid_prime [2, 3, 431815651537] ⟨7772681727667, 2, [(2, 1), (3, 2), (431815651537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431815651537
  · decide +kernel

theorem prime_7772681845807 : Nat.Prime 7772681845807 := by
  apply nodeValid_prime [2, 3, 347, 34673, 107671] ⟨7772681845807, 3, [(2, 1), (3, 1), (347, 1), (34673, 1), (107671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
    · exact prime_34673
    · exact prime_107671
  · decide +kernel

theorem prime_7777909146913 : Nat.Prime 7777909146913 := by
  apply nodeValid_prime [2, 3, 24413, 3318719] ⟨7777909146913, 5, [(2, 5), (3, 1), (24413, 1), (3318719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24413
    · exact prime_3318719
  · decide +kernel

theorem prime_7777909246487 : Nat.Prime 7777909246487 := by
  apply nodeValid_prime [2, 1303, 2984615981] ⟨7777909246487, 5, [(2, 1), (1303, 1), (2984615981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1303
    · exact prime_2984615981
  · decide +kernel

theorem prime_7777909247027 : Nat.Prime 7777909247027 := by
  apply nodeValid_prime [2, 23, 41, 100585951] ⟨7777909247027, 2, [(2, 1), (23, 1), (41, 2), (100585951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_41
    · exact prime_100585951
  · decide +kernel

theorem prime_7783138830463 : Nat.Prime 7783138830463 := by
  apply nodeValid_prime [2, 3, 37, 787, 1049, 42467] ⟨7783138830463, 6, [(2, 1), (3, 1), (37, 1), (787, 1), (1049, 1), (42467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_787
    · exact prime_1049
    · exact prime_42467
  · decide +kernel

theorem prime_7783138831417 : Nat.Prime 7783138831417 := by
  apply nodeValid_prime [2, 3, 13, 19, 4373, 300239] ⟨7783138831417, 5, [(2, 3), (3, 1), (13, 1), (19, 1), (4373, 1), (300239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_4373
    · exact prime_300239
  · decide +kernel

theorem prime_7783138839181 : Nat.Prime 7783138839181 := by
  apply nodeValid_prime [2, 3, 5, 113, 1147955581] ⟨7783138839181, 2, [(2, 2), (3, 1), (5, 1), (113, 1), (1147955581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_1147955581
  · decide +kernel

theorem prime_7788370769827 : Nat.Prime 7788370769827 := by
  apply nodeValid_prime [2, 3, 14387, 90224633] ⟨7788370769827, 2, [(2, 1), (3, 1), (14387, 1), (90224633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14387
    · exact prime_90224633
  · decide +kernel

theorem prime_7788370771633 : Nat.Prime 7788370771633 := by
  apply nodeValid_prime [2, 3, 11, 2819, 475691] ⟨7788370771633, 15, [(2, 4), (3, 1), (11, 2), (2819, 1), (475691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2819
    · exact prime_475691
  · decide +kernel

theorem prime_7788370908917 : Nat.Prime 7788370908917 := by
  apply nodeValid_prime [2, 13, 19, 606382039] ⟨7788370908917, 2, [(2, 2), (13, 2), (19, 1), (606382039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_606382039
  · decide +kernel

end Sude.Lucas.Generated
