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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6091 : Nat.Prime 6091 := by
  apply nodeValid_prime [2, 3, 5, 7, 29] ⟨6091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_6947 : Nat.Prime 6947 := by
  apply nodeValid_prime [2, 23, 151] ⟨6947, 2, [(2, 1), (23, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_151
  · decide +kernel

theorem prime_8237 : Nat.Prime 8237 := by
  apply nodeValid_prime [2, 29, 71] ⟨8237, 2, [(2, 2), (29, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_71
  · decide +kernel

theorem prime_8501 : Nat.Prime 8501 := by
  apply nodeValid_prime [2, 5, 17] ⟨8501, 7, [(2, 2), (5, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_8713 : Nat.Prime 8713 := by
  apply nodeValid_prime [2, 3, 11] ⟨8713, 5, [(2, 3), (3, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_10453 : Nat.Prime 10453 := by
  apply nodeValid_prime [2, 3, 13, 67] ⟨10453, 5, [(2, 2), (3, 1), (13, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_11801 : Nat.Prime 11801 := by
  apply nodeValid_prime [2, 5, 59] ⟨11801, 3, [(2, 3), (5, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_12391 : Nat.Prime 12391 := by
  apply nodeValid_prime [2, 3, 5, 7, 59] ⟨12391, 26, [(2, 1), (3, 1), (5, 1), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_12853 : Nat.Prime 12853 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨12853, 5, [(2, 2), (3, 3), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_14341 : Nat.Prime 14341 := by
  apply nodeValid_prime [2, 3, 5, 239] ⟨14341, 2, [(2, 2), (3, 1), (5, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239
  · decide +kernel

theorem prime_15077 : Nat.Prime 15077 := by
  apply nodeValid_prime [2, 3769] ⟨15077, 2, [(2, 2), (3769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3769
  · decide +kernel

theorem prime_15313 : Nat.Prime 15313 := by
  apply nodeValid_prime [2, 3, 11, 29] ⟨15313, 5, [(2, 4), (3, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_17981 : Nat.Prime 17981 := by
  apply nodeValid_prime [2, 5, 29, 31] ⟨17981, 2, [(2, 2), (5, 1), (29, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_31
  · decide +kernel

theorem prime_19081 : Nat.Prime 19081 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨19081, 17, [(2, 3), (3, 2), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_21211 : Nat.Prime 21211 := by
  apply nodeValid_prime [2, 3, 5, 7, 101] ⟨21211, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_101
  · decide +kernel

theorem prime_22157 : Nat.Prime 22157 := by
  apply nodeValid_prime [2, 29, 191] ⟨22157, 2, [(2, 2), (29, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_191
  · decide +kernel

theorem prime_22279 : Nat.Prime 22279 := by
  apply nodeValid_prime [2, 3, 47, 79] ⟨22279, 3, [(2, 1), (3, 1), (47, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_79
  · decide +kernel

theorem prime_23603 : Nat.Prime 23603 := by
  apply nodeValid_prime [2, 11801] ⟨23603, 2, [(2, 1), (11801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11801
  · decide +kernel

theorem prime_25111 : Nat.Prime 25111 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨25111, 3, [(2, 1), (3, 4), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_26681 : Nat.Prime 26681 := by
  apply nodeValid_prime [2, 5, 23, 29] ⟨26681, 6, [(2, 3), (5, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_29411 : Nat.Prime 29411 := by
  apply nodeValid_prime [2, 5, 17, 173] ⟨29411, 2, [(2, 1), (5, 1), (17, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_173
  · decide +kernel

theorem prime_37501 : Nat.Prime 37501 := by
  apply nodeValid_prime [2, 3, 5] ⟨37501, 2, [(2, 2), (3, 1), (5, 5)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_39511 : Nat.Prime 39511 := by
  apply nodeValid_prime [2, 3, 5, 439] ⟨39511, 3, [(2, 1), (3, 2), (5, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_42451 : Nat.Prime 42451 := by
  apply nodeValid_prime [2, 3, 5, 283] ⟨42451, 3, [(2, 1), (3, 1), (5, 2), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_283
  · decide +kernel

theorem prime_43889 : Nat.Prime 43889 := by
  apply nodeValid_prime [2, 13, 211] ⟨43889, 3, [(2, 4), (13, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_211
  · decide +kernel

theorem prime_44683 : Nat.Prime 44683 := by
  apply nodeValid_prime [2, 3, 11, 677] ⟨44683, 2, [(2, 1), (3, 1), (11, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_677
  · decide +kernel

theorem prime_47207 : Nat.Prime 47207 := by
  apply nodeValid_prime [2, 23603] ⟨47207, 5, [(2, 1), (23603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23603
  · decide +kernel

theorem prime_48157 : Nat.Prime 48157 := by
  apply nodeValid_prime [2, 3, 4013] ⟨48157, 5, [(2, 2), (3, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4013
  · decide +kernel

theorem prime_49993 : Nat.Prime 49993 := by
  apply nodeValid_prime [2, 3, 2083] ⟨49993, 5, [(2, 3), (3, 1), (2083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2083
  · decide +kernel

theorem prime_54601 : Nat.Prime 54601 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨54601, 22, [(2, 3), (3, 1), (5, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_56687 : Nat.Prime 56687 := by
  apply nodeValid_prime [2, 7, 4049] ⟨56687, 5, [(2, 1), (7, 1), (4049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4049
  · decide +kernel

theorem prime_68639 : Nat.Prime 68639 := by
  apply nodeValid_prime [2, 34319] ⟨68639, 7, [(2, 1), (34319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34319
  · decide +kernel

theorem prime_71257 : Nat.Prime 71257 := by
  apply nodeValid_prime [2, 3, 2969] ⟨71257, 5, [(2, 3), (3, 1), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2969
  · decide +kernel

theorem prime_76123 : Nat.Prime 76123 := by
  apply nodeValid_prime [2, 3, 4229] ⟨76123, 3, [(2, 1), (3, 2), (4229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4229
  · decide +kernel

theorem prime_78101 : Nat.Prime 78101 := by
  apply nodeValid_prime [2, 5, 11, 71] ⟨78101, 2, [(2, 2), (5, 2), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_79063 : Nat.Prime 79063 := by
  apply nodeValid_prime [2, 3, 13177] ⟨79063, 5, [(2, 1), (3, 1), (13177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13177
  · decide +kernel

theorem prime_84673 : Nat.Prime 84673 := by
  apply nodeValid_prime [2, 3, 7] ⟨84673, 10, [(2, 6), (3, 3), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_92941 : Nat.Prime 92941 := by
  apply nodeValid_prime [2, 3, 5, 1549] ⟨92941, 2, [(2, 2), (3, 1), (5, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1549
  · decide +kernel

theorem prime_96269 : Nat.Prime 96269 := by
  apply nodeValid_prime [2, 41, 587] ⟨96269, 2, [(2, 2), (41, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_587
  · decide +kernel

theorem prime_102499 : Nat.Prime 102499 := by
  apply nodeValid_prime [2, 3, 11, 1553] ⟨102499, 3, [(2, 1), (3, 1), (11, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1553
  · decide +kernel

theorem prime_110431 : Nat.Prime 110431 := by
  apply nodeValid_prime [2, 3, 5, 409] ⟨110431, 3, [(2, 1), (3, 3), (5, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_409
  · decide +kernel

theorem prime_112919 : Nat.Prime 112919 := by
  apply nodeValid_prime [2, 13, 43, 101] ⟨112919, 7, [(2, 1), (13, 1), (43, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_101
  · decide +kernel

theorem prime_117109 : Nat.Prime 117109 := by
  apply nodeValid_prime [2, 3, 3253] ⟨117109, 2, [(2, 2), (3, 2), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3253
  · decide +kernel

theorem prime_121889 : Nat.Prime 121889 := by
  apply nodeValid_prime [2, 13, 293] ⟨121889, 3, [(2, 5), (13, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_293
  · decide +kernel

theorem prime_137279 : Nat.Prime 137279 := by
  apply nodeValid_prime [2, 68639] ⟨137279, 7, [(2, 1), (68639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68639
  · decide +kernel

theorem prime_140221 : Nat.Prime 140221 := by
  apply nodeValid_prime [2, 3, 5, 19, 41] ⟨140221, 6, [(2, 2), (3, 2), (5, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_140893 : Nat.Prime 140893 := by
  apply nodeValid_prime [2, 3, 59, 199] ⟨140893, 2, [(2, 2), (3, 1), (59, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_199
  · decide +kernel

theorem prime_161221 : Nat.Prime 161221 := by
  apply nodeValid_prime [2, 3, 5, 2687] ⟨161221, 2, [(2, 2), (3, 1), (5, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2687
  · decide +kernel

theorem prime_162577 : Nat.Prime 162577 := by
  apply nodeValid_prime [2, 3, 1129] ⟨162577, 5, [(2, 4), (3, 2), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1129
  · decide +kernel

theorem prime_167023 : Nat.Prime 167023 := by
  apply nodeValid_prime [2, 3, 1031] ⟨167023, 5, [(2, 1), (3, 4), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1031
  · decide +kernel

theorem prime_177257 : Nat.Prime 177257 := by
  apply nodeValid_prime [2, 22157] ⟨177257, 3, [(2, 3), (22157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22157
  · decide +kernel

theorem prime_192539 : Nat.Prime 192539 := by
  apply nodeValid_prime [2, 96269] ⟨192539, 2, [(2, 1), (96269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_96269
  · decide +kernel

theorem prime_193861 : Nat.Prime 193861 := by
  apply nodeValid_prime [2, 3, 5, 359] ⟨193861, 2, [(2, 2), (3, 3), (5, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_359
  · decide +kernel

theorem prime_195427 : Nat.Prime 195427 := by
  apply nodeValid_prime [2, 3, 7, 11, 47] ⟨195427, 5, [(2, 1), (3, 3), (7, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_213449 : Nat.Prime 213449 := by
  apply nodeValid_prime [2, 26681] ⟨213449, 3, [(2, 3), (26681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26681
  · decide +kernel

theorem prime_214141 : Nat.Prime 214141 := by
  apply nodeValid_prime [2, 3, 5, 43, 83] ⟨214141, 6, [(2, 2), (3, 1), (5, 1), (43, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_83
  · decide +kernel

theorem prime_225839 : Nat.Prime 225839 := by
  apply nodeValid_prime [2, 112919] ⟨225839, 11, [(2, 1), (112919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_112919
  · decide +kernel

theorem prime_229849 : Nat.Prime 229849 := by
  apply nodeValid_prime [2, 3, 61, 157] ⟨229849, 23, [(2, 3), (3, 1), (61, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_157
  · decide +kernel

theorem prime_268063 : Nat.Prime 268063 := by
  apply nodeValid_prime [2, 3, 43, 1039] ⟨268063, 3, [(2, 1), (3, 1), (43, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1039
  · decide +kernel

theorem prime_280187 : Nat.Prime 280187 := by
  apply nodeValid_prime [2, 23, 6091] ⟨280187, 2, [(2, 1), (23, 1), (6091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_6091
  · decide +kernel

theorem prime_282767 : Nat.Prime 282767 := by
  apply nodeValid_prime [2, 11, 12853] ⟨282767, 5, [(2, 1), (11, 1), (12853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12853
  · decide +kernel

theorem prime_289841 : Nat.Prime 289841 := by
  apply nodeValid_prime [2, 5, 3623] ⟨289841, 6, [(2, 4), (5, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3623
  · decide +kernel

theorem prime_382649 : Nat.Prime 382649 := by
  apply nodeValid_prime [2, 7, 6833] ⟨382649, 6, [(2, 3), (7, 1), (6833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6833
  · decide +kernel

theorem prime_384143 : Nat.Prime 384143 := by
  apply nodeValid_prime [2, 11, 19, 919] ⟨384143, 5, [(2, 1), (11, 1), (19, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_919
  · decide +kernel

theorem prime_385079 : Nat.Prime 385079 := by
  apply nodeValid_prime [2, 192539] ⟨385079, 7, [(2, 1), (192539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_192539
  · decide +kernel

theorem prime_399241 : Nat.Prime 399241 := by
  apply nodeValid_prime [2, 3, 5, 1109] ⟨399241, 7, [(2, 3), (3, 2), (5, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1109
  · decide +kernel

theorem prime_423781 : Nat.Prime 423781 := by
  apply nodeValid_prime [2, 3, 5, 7, 1009] ⟨423781, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1009
  · decide +kernel

theorem prime_456109 : Nat.Prime 456109 := by
  apply nodeValid_prime [2, 3, 191, 199] ⟨456109, 2, [(2, 2), (3, 1), (191, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_199
  · decide +kernel

theorem prime_470429 : Nat.Prime 470429 := by
  apply nodeValid_prime [2, 7, 53, 317] ⟨470429, 2, [(2, 2), (7, 1), (53, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_317
  · decide +kernel

theorem prime_521041 : Nat.Prime 521041 := by
  apply nodeValid_prime [2, 3, 5, 13, 167] ⟨521041, 14, [(2, 4), (3, 1), (5, 1), (13, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_167
  · decide +kernel

theorem prime_561313 : Nat.Prime 561313 := by
  apply nodeValid_prime [2, 3, 1949] ⟨561313, 5, [(2, 5), (3, 2), (1949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1949
  · decide +kernel

theorem prime_572927 : Nat.Prime 572927 := by
  apply nodeValid_prime [2, 19, 15077] ⟨572927, 5, [(2, 1), (19, 1), (15077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_15077
  · decide +kernel

theorem prime_593951 : Nat.Prime 593951 := by
  apply nodeValid_prime [2, 5, 7, 1697] ⟨593951, 7, [(2, 1), (5, 2), (7, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1697
  · decide +kernel

theorem prime_692059 : Nat.Prime 692059 := by
  apply nodeValid_prime [2, 3, 115343] ⟨692059, 11, [(2, 1), (3, 1), (115343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115343
  · decide +kernel

theorem prime_755203 : Nat.Prime 755203 := by
  apply nodeValid_prime [2, 3, 7, 17981] ⟨755203, 2, [(2, 1), (3, 1), (7, 1), (17981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17981
  · decide +kernel

theorem prime_774073 : Nat.Prime 774073 := by
  apply nodeValid_prime [2, 3, 13, 827] ⟨774073, 5, [(2, 3), (3, 2), (13, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_827
  · decide +kernel

theorem prime_778163 : Nat.Prime 778163 := by
  apply nodeValid_prime [2, 7, 11, 31, 163] ⟨778163, 5, [(2, 1), (7, 1), (11, 1), (31, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_163
  · decide +kernel

theorem prime_1004671 : Nat.Prime 1004671 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨1004671, 3, [(2, 1), (3, 3), (5, 1), (61, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_1013813 : Nat.Prime 1013813 := by
  apply nodeValid_prime [2, 17, 877] ⟨1013813, 2, [(2, 2), (17, 2), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_877
  · decide +kernel

theorem prime_1027489 : Nat.Prime 1027489 := by
  apply nodeValid_prime [2, 3, 7, 11, 139] ⟨1027489, 23, [(2, 5), (3, 1), (7, 1), (11, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_139
  · decide +kernel

theorem prime_1325119 : Nat.Prime 1325119 := by
  apply nodeValid_prime [2, 3, 37, 47, 127] ⟨1325119, 3, [(2, 1), (3, 1), (37, 1), (47, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_47
    · exact prime_127
  · decide +kernel

theorem prime_1325173 : Nat.Prime 1325173 := by
  apply nodeValid_prime [2, 3, 110431] ⟨1325173, 6, [(2, 2), (3, 1), (110431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_110431
  · decide +kernel

theorem prime_1373887 : Nat.Prime 1373887 := by
  apply nodeValid_prime [2, 3, 127, 601] ⟨1373887, 3, [(2, 1), (3, 2), (127, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_601
  · decide +kernel

theorem prime_1556327 : Nat.Prime 1556327 := by
  apply nodeValid_prime [2, 778163] ⟨1556327, 5, [(2, 1), (778163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_778163
  · decide +kernel

theorem prime_1722857 : Nat.Prime 1722857 := by
  apply nodeValid_prime [2, 31, 6947] ⟨1722857, 3, [(2, 3), (31, 1), (6947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_6947
  · decide +kernel

theorem prime_1779247 : Nat.Prime 1779247 := by
  apply nodeValid_prime [2, 3, 7, 523] ⟨1779247, 3, [(2, 1), (3, 5), (7, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_523
  · decide +kernel

theorem prime_1812851 : Nat.Prime 1812851 := by
  apply nodeValid_prime [2, 5, 13, 2789] ⟨1812851, 2, [(2, 1), (5, 2), (13, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2789
  · decide +kernel

theorem prime_1871437 : Nat.Prime 1871437 := by
  apply nodeValid_prime [2, 3, 7, 22279] ⟨1871437, 5, [(2, 2), (3, 1), (7, 1), (22279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_22279
  · decide +kernel

theorem prime_2002667 : Nat.Prime 2002667 := by
  apply nodeValid_prime [2, 137, 7309] ⟨2002667, 2, [(2, 1), (137, 1), (7309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_7309
  · decide +kernel

theorem prime_2012167 : Nat.Prime 2012167 := by
  apply nodeValid_prime [2, 3, 13, 8599] ⟨2012167, 3, [(2, 1), (3, 2), (13, 1), (8599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_8599
  · decide +kernel

theorem prime_2012449 : Nat.Prime 2012449 := by
  apply nodeValid_prime [2, 3, 20963] ⟨2012449, 7, [(2, 5), (3, 1), (20963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20963
  · decide +kernel

theorem prime_2352881 : Nat.Prime 2352881 := by
  apply nodeValid_prime [2, 5, 29411] ⟨2352881, 6, [(2, 4), (5, 1), (29411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29411
  · decide +kernel

theorem prime_3605443 : Nat.Prime 3605443 := by
  apply nodeValid_prime [2, 3, 233, 2579] ⟨3605443, 2, [(2, 1), (3, 1), (233, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_2579
  · decide +kernel

theorem prime_3854717 : Nat.Prime 3854717 := by
  apply nodeValid_prime [2, 17, 56687] ⟨3854717, 2, [(2, 2), (17, 1), (56687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_56687
  · decide +kernel

theorem prime_3958397 : Nat.Prime 3958397 := by
  apply nodeValid_prime [2, 13, 76123] ⟨3958397, 2, [(2, 2), (13, 1), (76123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_76123
  · decide +kernel

theorem prime_4531517 : Nat.Prime 4531517 := by
  apply nodeValid_prime [2, 11, 181, 569] ⟨4531517, 2, [(2, 2), (11, 1), (181, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_181
    · exact prime_569
  · decide +kernel

theorem prime_5024647 : Nat.Prime 5024647 := by
  apply nodeValid_prime [2, 3, 11, 769] ⟨5024647, 6, [(2, 1), (3, 3), (11, 2), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_769
  · decide +kernel

theorem prime_5090467 : Nat.Prime 5090467 := by
  apply nodeValid_prime [2, 3, 103, 8237] ⟨5090467, 3, [(2, 1), (3, 1), (103, 1), (8237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_8237
  · decide +kernel

theorem prime_5401969 : Nat.Prime 5401969 := by
  apply nodeValid_prime [2, 3, 11, 13, 787] ⟨5401969, 7, [(2, 4), (3, 1), (11, 1), (13, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_787
  · decide +kernel

theorem prime_5495549 : Nat.Prime 5495549 := by
  apply nodeValid_prime [2, 1373887] ⟨5495549, 2, [(2, 2), (1373887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1373887
  · decide +kernel

theorem prime_6376471 : Nat.Prime 6376471 := by
  apply nodeValid_prime [2, 3, 5, 43, 4943] ⟨6376471, 3, [(2, 1), (3, 1), (5, 1), (43, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_4943
  · decide +kernel

theorem prime_6525703 : Nat.Prime 6525703 := by
  apply nodeValid_prime [2, 3, 19, 19081] ⟨6525703, 3, [(2, 1), (3, 2), (19, 1), (19081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_19081
  · decide +kernel

theorem prime_7485749 : Nat.Prime 7485749 := by
  apply nodeValid_prime [2, 1871437] ⟨7485749, 2, [(2, 2), (1871437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1871437
  · decide +kernel

theorem prime_11060029 : Nat.Prime 11060029 := by
  apply nodeValid_prime [2, 3, 7, 43889] ⟨11060029, 10, [(2, 2), (3, 2), (7, 1), (43889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43889
  · decide +kernel

theorem prime_11321263 : Nat.Prime 11321263 := by
  apply nodeValid_prime [2, 3, 31, 6763] ⟨11321263, 5, [(2, 1), (3, 3), (31, 1), (6763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_6763
  · decide +kernel

theorem prime_12450617 : Nat.Prime 12450617 := by
  apply nodeValid_prime [2, 1556327] ⟨12450617, 3, [(2, 3), (1556327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1556327
  · decide +kernel

theorem prime_12794827 : Nat.Prime 12794827 := by
  apply nodeValid_prime [2, 3, 11, 193861] ⟨12794827, 2, [(2, 1), (3, 1), (11, 1), (193861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193861
  · decide +kernel

theorem prime_23521451 : Nat.Prime 23521451 := by
  apply nodeValid_prime [2, 5, 470429] ⟨23521451, 2, [(2, 1), (5, 2), (470429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_470429
  · decide +kernel

theorem prime_26461453 : Nat.Prime 26461453 := by
  apply nodeValid_prime [2, 3, 17, 19, 6827] ⟨26461453, 2, [(2, 2), (3, 1), (17, 1), (19, 1), (6827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_6827
  · decide +kernel

theorem prime_31667177 : Nat.Prime 31667177 := by
  apply nodeValid_prime [2, 3958397] ⟨31667177, 3, [(2, 3), (3958397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3958397
  · decide +kernel

theorem prime_32489203 : Nat.Prime 32489203 := by
  apply nodeValid_prime [2, 3, 19, 23, 12391] ⟨32489203, 2, [(2, 1), (3, 1), (19, 1), (23, 1), (12391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_12391
  · decide +kernel

theorem prime_40053341 : Nat.Prime 40053341 := by
  apply nodeValid_prime [2, 5, 2002667] ⟨40053341, 2, [(2, 2), (5, 1), (2002667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2002667
  · decide +kernel

theorem prime_65407373 : Nat.Prime 65407373 := by
  apply nodeValid_prime [2, 61, 268063] ⟨65407373, 2, [(2, 2), (61, 1), (268063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_268063
  · decide +kernel

theorem prime_71628013 : Nat.Prime 71628013 := by
  apply nodeValid_prime [2, 3, 307, 6481] ⟨71628013, 2, [(2, 2), (3, 2), (307, 1), (6481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_6481
  · decide +kernel

theorem prime_73350293 : Nat.Prime 73350293 := by
  apply nodeValid_prime [2, 2543, 7211] ⟨73350293, 2, [(2, 2), (2543, 1), (7211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2543
    · exact prime_7211
  · decide +kernel

theorem prime_86220971 : Nat.Prime 86220971 := by
  apply nodeValid_prime [2, 5, 11, 71257] ⟨86220971, 2, [(2, 1), (5, 1), (11, 2), (71257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_71257
  · decide +kernel

theorem prime_139132481 : Nat.Prime 139132481 := by
  apply nodeValid_prime [2, 5, 131, 3319] ⟨139132481, 6, [(2, 6), (5, 1), (131, 1), (3319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_3319
  · decide +kernel

theorem prime_164480707 : Nat.Prime 164480707 := by
  apply nodeValid_prime [2, 3, 13, 78101] ⟨164480707, 3, [(2, 1), (3, 4), (13, 1), (78101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_78101
  · decide +kernel

theorem prime_190664213 : Nat.Prime 190664213 := by
  apply nodeValid_prime [2, 29, 131, 12547] ⟨190664213, 2, [(2, 2), (29, 1), (131, 1), (12547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_131
    · exact prime_12547
  · decide +kernel

theorem prime_237468983 : Nat.Prime 237468983 := by
  apply nodeValid_prime [2, 59, 2012449] ⟨237468983, 5, [(2, 1), (59, 1), (2012449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2012449
  · decide +kernel

theorem prime_255058841 : Nat.Prime 255058841 := by
  apply nodeValid_prime [2, 5, 6376471] ⟨255058841, 3, [(2, 3), (5, 1), (6376471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6376471
  · decide +kernel

theorem prime_329268509 : Nat.Prime 329268509 := by
  apply nodeValid_prime [2, 109, 755203] ⟨329268509, 2, [(2, 2), (109, 1), (755203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_755203
  · decide +kernel

theorem prime_348724087 : Nat.Prime 348724087 := by
  apply nodeValid_prime [2, 3, 1471, 39511] ⟨348724087, 3, [(2, 1), (3, 1), (1471, 1), (39511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1471
    · exact prime_39511
  · decide +kernel

theorem prime_404230447 : Nat.Prime 404230447 := by
  apply nodeValid_prime [2, 3, 7485749] ⟨404230447, 6, [(2, 1), (3, 3), (7485749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7485749
  · decide +kernel

theorem prime_610856041 : Nat.Prime 610856041 := by
  apply nodeValid_prime [2, 3, 5, 5090467] ⟨610856041, 14, [(2, 3), (3, 1), (5, 1), (5090467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5090467
  · decide +kernel

theorem prime_647878213 : Nat.Prime 647878213 := by
  apply nodeValid_prime [2, 3, 29, 73, 8501] ⟨647878213, 6, [(2, 2), (3, 2), (29, 1), (73, 1), (8501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_73
    · exact prime_8501
  · decide +kernel

theorem prime_777883537 : Nat.Prime 777883537 := by
  apply nodeValid_prime [2, 3, 5401969] ⟨777883537, 11, [(2, 4), (3, 2), (5401969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5401969
  · decide +kernel

theorem prime_981849373 : Nat.Prime 981849373 := by
  apply nodeValid_prime [2, 3, 7, 659, 17737] ⟨981849373, 2, [(2, 2), (3, 1), (7, 1), (659, 1), (17737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_659
    · exact prime_17737
  · decide +kernel

theorem prime_1354327531 : Nat.Prime 1354327531 := by
  apply nodeValid_prime [2, 3, 5, 157, 421, 683] ⟨1354327531, 3, [(2, 1), (3, 1), (5, 1), (157, 1), (421, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
    · exact prime_421
    · exact prime_683
  · decide +kernel

theorem prime_1429246057 : Nat.Prime 1429246057 := by
  apply nodeValid_prime [2, 3, 7, 83, 102499] ⟨1429246057, 13, [(2, 3), (3, 1), (7, 1), (83, 1), (102499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_102499
  · decide +kernel

theorem prime_1907107619 : Nat.Prime 1907107619 := by
  apply nodeValid_prime [2, 13, 73350293] ⟨1907107619, 2, [(2, 1), (13, 1), (73350293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73350293
  · decide +kernel

theorem prime_3569220073 : Nat.Prime 3569220073 := by
  apply nodeValid_prime [2, 3, 11, 19, 79063] ⟨3569220073, 10, [(2, 3), (3, 3), (11, 1), (19, 1), (79063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_79063
  · decide +kernel

theorem prime_4055257127 : Nat.Prime 4055257127 := by
  apply nodeValid_prime [2, 31, 65407373] ⟨4055257127, 5, [(2, 1), (31, 1), (65407373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_65407373
  · decide +kernel

theorem prime_4405182937 : Nat.Prime 4405182937 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 140221] ⟨4405182937, 15, [(2, 3), (3, 1), (7, 1), (11, 1), (17, 1), (140221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_140221
  · decide +kernel

theorem prime_16266905741 : Nat.Prime 16266905741 := by
  apply nodeValid_prime [2, 5, 211, 3854717] ⟨16266905741, 2, [(2, 2), (5, 1), (211, 1), (3854717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
    · exact prime_3854717
  · decide +kernel

theorem prime_16312871459 : Nat.Prime 16312871459 := by
  apply nodeValid_prime [2, 13, 17, 19, 163, 701] ⟨16312871459, 2, [(2, 1), (13, 1), (17, 2), (19, 1), (163, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_163
    · exact prime_701
  · decide +kernel

theorem prime_65159510089 : Nat.Prime 65159510089 := by
  apply nodeValid_prime [2, 3, 107, 1657, 15313] ⟨65159510089, 13, [(2, 3), (3, 1), (107, 1), (1657, 1), (15313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_1657
    · exact prime_15313
  · decide +kernel

theorem prime_66269015269 : Nat.Prime 66269015269 := by
  apply nodeValid_prime [2, 3, 14341, 385079] ⟨66269015269, 6, [(2, 2), (3, 1), (14341, 1), (385079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14341
    · exact prime_385079
  · decide +kernel

theorem prime_97326172499 : Nat.Prime 97326172499 := by
  apply nodeValid_prime [2, 121889, 399241] ⟨97326172499, 2, [(2, 1), (121889, 1), (399241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_121889
    · exact prime_399241
  · decide +kernel

theorem prime_194652342097 : Nat.Prime 194652342097 := by
  apply nodeValid_prime [2, 3, 4055257127] ⟨194652342097, 5, [(2, 4), (3, 1), (4055257127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4055257127
  · decide +kernel

theorem prime_194927481283 : Nat.Prime 194927481283 := by
  apply nodeValid_prime [2, 3, 619, 5021, 10453] ⟨194927481283, 2, [(2, 1), (3, 1), (619, 1), (5021, 1), (10453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
    · exact prime_5021
    · exact prime_10453
  · decide +kernel

theorem prime_195202868893 : Nat.Prime 195202868893 := by
  apply nodeValid_prime [2, 3, 16266905741] ⟨195202868893, 2, [(2, 2), (3, 1), (16266905741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16266905741
  · decide +kernel

theorem prime_772028200511 : Nat.Prime 772028200511 := by
  apply nodeValid_prime [2, 5, 7, 41, 2297, 117109] ⟨772028200511, 7, [(2, 1), (5, 1), (7, 1), (41, 1), (2297, 1), (117109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_2297
    · exact prime_117109
  · decide +kernel

theorem prime_772028200919 : Nat.Prime 772028200919 := by
  apply nodeValid_prime [2, 13, 49993, 593951] ⟨772028200919, 19, [(2, 1), (13, 1), (49993, 1), (593951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_49993
    · exact prime_593951
  · decide +kernel

theorem prime_772028234561 : Nat.Prime 772028234561 := by
  apply nodeValid_prime [2, 5, 11, 109, 2012167] ⟨772028234561, 3, [(2, 6), (5, 1), (11, 1), (109, 1), (2012167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_109
    · exact prime_2012167
  · decide +kernel

theorem prime_773122459133 : Nat.Prime 773122459133 := by
  apply nodeValid_prime [2, 587, 329268509] ⟨773122459133, 2, [(2, 2), (587, 1), (329268509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_587
    · exact prime_329268509
  · decide +kernel

theorem prime_773122459279 : Nat.Prime 773122459279 := by
  apply nodeValid_prime [2, 3, 13, 313, 31667177] ⟨773122459279, 3, [(2, 1), (3, 1), (13, 1), (313, 1), (31667177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_313
    · exact prime_31667177
  · decide +kernel

theorem prime_773122465289 : Nat.Prime 773122465289 := by
  apply nodeValid_prime [2, 43, 2237, 1004671] ⟨773122465289, 3, [(2, 3), (43, 1), (2237, 1), (1004671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2237
    · exact prime_1004671
  · decide +kernel

theorem prime_774217707491 : Nat.Prime 774217707491 := by
  apply nodeValid_prime [2, 5, 2383, 32489203] ⟨774217707491, 2, [(2, 1), (5, 1), (2383, 1), (32489203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2383
    · exact prime_32489203
  · decide +kernel

theorem prime_774217708349 : Nat.Prime 774217708349 := by
  apply nodeValid_prime [2, 7, 5503, 5024647] ⟨774217708349, 2, [(2, 2), (7, 1), (5503, 1), (5024647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5503
    · exact prime_5024647
  · decide +kernel

theorem prime_774217742603 : Nat.Prime 774217742603 := by
  apply nodeValid_prime [2, 29, 47207, 282767] ⟨774217742603, 2, [(2, 1), (29, 1), (47207, 1), (282767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_47207
    · exact prime_282767
  · decide +kernel

theorem prime_775313997239 : Nat.Prime 775313997239 := by
  apply nodeValid_prime [2, 11, 29, 683, 1779247] ⟨775313997239, 11, [(2, 1), (11, 1), (29, 1), (683, 1), (1779247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_683
    · exact prime_1779247
  · decide +kernel

theorem prime_775313997347 : Nat.Prime 775313997347 := by
  apply nodeValid_prime [2, 7, 137, 404230447] ⟨775313997347, 2, [(2, 1), (7, 1), (137, 1), (404230447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_404230447
  · decide +kernel

theorem prime_775314074329 : Nat.Prime 775314074329 := by
  apply nodeValid_prime [2, 3, 19, 233, 1409, 5179] ⟨775314074329, 13, [(2, 3), (3, 1), (19, 1), (233, 1), (1409, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_233
    · exact prime_1409
    · exact prime_5179
  · decide +kernel

theorem prime_776411446423 : Nat.Prime 776411446423 := by
  apply nodeValid_prime [2, 3, 19, 53, 569, 225839] ⟨776411446423, 5, [(2, 1), (3, 1), (19, 1), (53, 1), (569, 1), (225839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
    · exact prime_569
    · exact prime_225839
  · decide +kernel

theorem prime_776411446879 : Nat.Prime 776411446879 := by
  apply nodeValid_prime [2, 3, 19, 41, 131, 140893] ⟨776411446879, 12, [(2, 1), (3, 3), (19, 1), (41, 1), (131, 1), (140893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_131
    · exact prime_140893
  · decide +kernel

theorem prime_776411451983 : Nat.Prime 776411451983 := by
  apply nodeValid_prime [2, 214141, 1812851] ⟨776411451983, 5, [(2, 1), (214141, 1), (1812851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_214141
    · exact prime_1812851
  · decide +kernel

theorem prime_777509855009 : Nat.Prime 777509855009 := by
  apply nodeValid_prime [2, 17, 1429246057] ⟨777509855009, 3, [(2, 5), (17, 1), (1429246057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1429246057
  · decide +kernel

theorem prime_777509855723 : Nat.Prime 777509855723 := by
  apply nodeValid_prime [2, 17, 181, 277, 456109] ⟨777509855723, 5, [(2, 1), (17, 1), (181, 1), (277, 1), (456109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_181
    · exact prime_277
    · exact prime_456109
  · decide +kernel

theorem prime_777509884121 : Nat.Prime 777509884121 := by
  apply nodeValid_prime [2, 5, 25111, 774073] ⟨777509884121, 3, [(2, 3), (5, 1), (25111, 1), (774073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25111
    · exact prime_774073
  · decide +kernel

theorem prime_778609368389 : Nat.Prime 778609368389 := by
  apply nodeValid_prime [2, 194652342097] ⟨778609368389, 2, [(2, 2), (194652342097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_194652342097
  · decide +kernel

theorem prime_778609379993 : Nat.Prime 778609379993 := by
  apply nodeValid_prime [2, 97326172499] ⟨778609379993, 3, [(2, 3), (97326172499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_97326172499
  · decide +kernel

theorem prime_778609382321 : Nat.Prime 778609382321 := by
  apply nodeValid_prime [2, 5, 7, 11, 23, 5495549] ⟨778609382321, 3, [(2, 4), (5, 1), (7, 1), (11, 1), (23, 1), (5495549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_5495549
  · decide +kernel

theorem prime_779709897881 : Nat.Prime 779709897881 := by
  apply nodeValid_prime [2, 5, 120907, 161221] ⟨779709897881, 3, [(2, 3), (5, 1), (120907, 1), (161221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_120907
    · exact prime_161221
  · decide +kernel

theorem prime_779709924443 : Nat.Prime 779709924443 := by
  apply nodeValid_prime [2, 101, 349, 11060029] ⟨779709924443, 2, [(2, 1), (101, 1), (349, 1), (11060029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_349
    · exact prime_11060029
  · decide +kernel

theorem prime_779709925133 : Nat.Prime 779709925133 := by
  apply nodeValid_prime [2, 194927481283] ⟨779709925133, 2, [(2, 2), (194927481283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_194927481283
  · decide +kernel

theorem prime_780811474913 : Nat.Prime 780811474913 := by
  apply nodeValid_prime [2, 7, 181, 431, 44683] ⟨780811474913, 3, [(2, 5), (7, 1), (181, 1), (431, 1), (44683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_181
    · exact prime_431
    · exact prime_44683
  · decide +kernel

theorem prime_780811475573 : Nat.Prime 780811475573 := by
  apply nodeValid_prime [2, 195202868893] ⟨780811475573, 2, [(2, 2), (195202868893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_195202868893
  · decide +kernel

theorem prime_780811483373 : Nat.Prime 780811483373 := by
  apply nodeValid_prime [2, 23, 61, 139132481] ⟨780811483373, 2, [(2, 2), (23, 1), (61, 1), (139132481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_61
    · exact prime_139132481
  · decide +kernel

theorem prime_781914119683 : Nat.Prime 781914119683 := by
  apply nodeValid_prime [2, 3, 97, 571, 2352881] ⟨781914119683, 2, [(2, 1), (3, 1), (97, 1), (571, 1), (2352881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_571
    · exact prime_2352881
  · decide +kernel

theorem prime_781914121069 : Nat.Prime 781914121069 := by
  apply nodeValid_prime [2, 3, 65159510089] ⟨781914121069, 2, [(2, 2), (3, 1), (65159510089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_65159510089
  · decide +kernel

theorem prime_781914123791 : Nat.Prime 781914123791 := by
  apply nodeValid_prime [2, 5, 41, 1907107619] ⟨781914123791, 11, [(2, 1), (5, 1), (41, 1), (1907107619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_1907107619
  · decide +kernel

theorem prime_783017822747 : Nat.Prime 783017822747 := by
  apply nodeValid_prime [2, 37, 827, 12794827] ⟨783017822747, 2, [(2, 1), (37, 1), (827, 1), (12794827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_827
    · exact prime_12794827
  · decide +kernel

theorem prime_783017830033 : Nat.Prime 783017830033 := by
  apply nodeValid_prime [2, 3, 16312871459] ⟨783017830033, 7, [(2, 4), (3, 1), (16312871459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16312871459
  · decide +kernel

theorem prime_783017832217 : Nat.Prime 783017832217 := by
  apply nodeValid_prime [2, 3, 29, 653, 1722857] ⟨783017832217, 5, [(2, 3), (3, 1), (29, 1), (653, 1), (1722857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_653
    · exact prime_1722857
  · decide +kernel

theorem prime_784122562787 : Nat.Prime 784122562787 := by
  apply nodeValid_prime [2, 89, 4405182937] ⟨784122562787, 2, [(2, 1), (89, 1), (4405182937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_4405182937
  · decide +kernel

theorem prime_784122563453 : Nat.Prime 784122563453 := by
  apply nodeValid_prime [2, 41, 431, 523, 21211] ⟨784122563453, 2, [(2, 2), (41, 1), (431, 1), (523, 1), (21211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_431
    · exact prime_523
    · exact prime_21211
  · decide +kernel

theorem prime_784122581867 : Nat.Prime 784122581867 := by
  apply nodeValid_prime [2, 13, 127, 237468983] ⟨784122581867, 2, [(2, 1), (13, 1), (127, 1), (237468983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_127
    · exact prime_237468983
  · decide +kernel

theorem prime_785228394157 : Nat.Prime 785228394157 := by
  apply nodeValid_prime [2, 3, 101, 647878213] ⟨785228394157, 2, [(2, 2), (3, 1), (101, 1), (647878213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_647878213
  · decide +kernel

theorem prime_785228416061 : Nat.Prime 785228416061 := by
  apply nodeValid_prime [2, 5, 11, 3569220073] ⟨785228416061, 3, [(2, 2), (5, 1), (11, 1), (3569220073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3569220073
  · decide +kernel

theorem prime_785228416069 : Nat.Prime 785228416069 := by
  apply nodeValid_prime [2, 3, 19, 23, 113, 1325119] ⟨785228416069, 6, [(2, 2), (3, 1), (19, 1), (23, 1), (113, 1), (1325119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_113
    · exact prime_1325119
  · decide +kernel

theorem prime_786335255521 : Nat.Prime 786335255521 := by
  apply nodeValid_prime [2, 3, 5, 19, 86220971] ⟨786335255521, 11, [(2, 5), (3, 1), (5, 1), (19, 1), (86220971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_86220971
  · decide +kernel

theorem prime_786335276723 : Nat.Prime 786335276723 := by
  apply nodeValid_prime [2, 382649, 1027489] ⟨786335276723, 2, [(2, 1), (382649, 1), (1027489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_382649
    · exact prime_1027489
  · decide +kernel

theorem prime_786335277643 : Nat.Prime 786335277643 := by
  apply nodeValid_prime [2, 3, 251527, 521041] ⟨786335277643, 2, [(2, 1), (3, 1), (251527, 1), (521041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251527
    · exact prime_521041
  · decide +kernel

theorem prime_787443172973 : Nat.Prime 787443172973 := by
  apply nodeValid_prime [2, 54601, 3605443] ⟨787443172973, 2, [(2, 2), (54601, 1), (3605443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_54601
    · exact prime_3605443
  · decide +kernel

theorem prime_787443197147 : Nat.Prime 787443197147 := by
  apply nodeValid_prime [2, 401, 981849373] ⟨787443197147, 2, [(2, 1), (401, 1), (981849373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_401
    · exact prime_981849373
  · decide +kernel

theorem prime_787443199691 : Nat.Prime 787443199691 := by
  apply nodeValid_prime [2, 5, 7, 59, 190664213] ⟨787443199691, 2, [(2, 1), (5, 1), (7, 1), (59, 1), (190664213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_190664213
  · decide +kernel

theorem prime_788552127497 : Nat.Prime 788552127497 := by
  apply nodeValid_prime [2, 7, 89, 4219, 37501] ⟨788552127497, 3, [(2, 3), (7, 1), (89, 1), (4219, 1), (37501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_4219
    · exact prime_37501
  · decide +kernel

theorem prime_788552128687 : Nat.Prime 788552128687 := by
  apply nodeValid_prime [2, 3, 7, 113, 593, 280187] ⟨788552128687, 3, [(2, 1), (3, 1), (7, 1), (113, 1), (593, 1), (280187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
    · exact prime_593
    · exact prime_280187
  · decide +kernel

theorem prime_788552144689 : Nat.Prime 788552144689 := by
  apply nodeValid_prime [2, 3, 7, 11, 23, 1325173] ⟨788552144689, 31, [(2, 4), (3, 1), (7, 2), (11, 1), (23, 1), (1325173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_1325173
  · decide +kernel

theorem prime_789662152421 : Nat.Prime 789662152421 := by
  apply nodeValid_prime [2, 5, 8713, 4531517] ⟨789662152421, 2, [(2, 2), (5, 1), (8713, 1), (4531517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8713
    · exact prime_4531517
  · decide +kernel

theorem prime_789662152973 : Nat.Prime 789662152973 := by
  apply nodeValid_prime [2, 7, 11, 109, 23521451] ⟨789662152973, 2, [(2, 2), (7, 1), (11, 1), (109, 1), (23521451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_109
    · exact prime_23521451
  · decide +kernel

theorem prime_789662171737 : Nat.Prime 789662171737 := by
  apply nodeValid_prime [2, 3, 43, 255058841] ⟨789662171737, 5, [(2, 3), (3, 2), (43, 1), (255058841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_255058841
  · decide +kernel

theorem prime_790773256177 : Nat.Prime 790773256177 := by
  apply nodeValid_prime [2, 3, 92941, 177257] ⟨790773256177, 5, [(2, 4), (3, 1), (92941, 1), (177257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_92941
    · exact prime_177257
  · decide +kernel

theorem prime_790773263521 : Nat.Prime 790773263521 := by
  apply nodeValid_prime [2, 3, 5, 23, 71628013] ⟨790773263521, 7, [(2, 5), (3, 1), (5, 1), (23, 1), (71628013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_71628013
  · decide +kernel

theorem prime_790773263897 : Nat.Prime 790773263897 := by
  apply nodeValid_prime [2, 7, 11, 2287, 561313] ⟨790773263897, 3, [(2, 3), (7, 1), (11, 1), (2287, 1), (561313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_2287
    · exact prime_561313
  · decide +kernel

theorem prime_791885400203 : Nat.Prime 791885400203 := by
  apply nodeValid_prime [2, 13, 19, 11677, 137279] ⟨791885400203, 5, [(2, 1), (13, 1), (19, 1), (11677, 1), (137279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_11677
    · exact prime_137279
  · decide +kernel

theorem prime_791885440667 : Nat.Prime 791885440667 := by
  apply nodeValid_prime [2, 509, 777883537] ⟨791885440667, 2, [(2, 1), (509, 1), (777883537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_777883537
  · decide +kernel

theorem prime_791885442479 : Nat.Prime 791885442479 := by
  apply nodeValid_prime [2, 13, 1151, 26461453] ⟨791885442479, 17, [(2, 1), (13, 1), (1151, 1), (26461453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1151
    · exact prime_26461453
  · decide +kernel

theorem prime_792998573387 : Nat.Prime 792998573387 := by
  apply nodeValid_prime [2, 572927, 692059] ⟨792998573387, 2, [(2, 1), (572927, 1), (692059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_572927
    · exact prime_692059
  · decide +kernel

theorem prime_792998573839 : Nat.Prime 792998573839 := by
  apply nodeValid_prime [2, 3, 379, 348724087] ⟨792998573839, 6, [(2, 1), (3, 1), (379, 1), (348724087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_348724087
  · decide +kernel

theorem prime_792998599499 : Nat.Prime 792998599499 := by
  apply nodeValid_prime [2, 7, 195427, 289841] ⟨792998599499, 2, [(2, 1), (7, 1), (195427, 1), (289841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_195427
    · exact prime_289841
  · decide +kernel

theorem prime_794112853301 : Nat.Prime 794112853301 := by
  apply nodeValid_prime [2, 5, 13, 610856041] ⟨794112853301, 2, [(2, 2), (5, 2), (13, 1), (610856041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_610856041
  · decide +kernel

theorem prime_794112853397 : Nat.Prime 794112853397 := by
  apply nodeValid_prime [2, 17, 71, 164480707] ⟨794112853397, 2, [(2, 2), (17, 1), (71, 1), (164480707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_164480707
  · decide +kernel

theorem prime_794112857777 : Nat.Prime 794112857777 := by
  apply nodeValid_prime [2, 7, 42451, 167023] ⟨794112857777, 3, [(2, 4), (7, 1), (42451, 1), (167023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_42451
    · exact prime_167023
  · decide +kernel

theorem prime_795228155647 : Nat.Prime 795228155647 := by
  apply nodeValid_prime [2, 3, 23, 509, 11321263] ⟨795228155647, 6, [(2, 1), (3, 1), (23, 1), (509, 1), (11321263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_509
    · exact prime_11321263
  · decide +kernel

theorem prime_795228155789 : Nat.Prime 795228155789 := by
  apply nodeValid_prime [2, 11, 84673, 213449] ⟨795228155789, 2, [(2, 2), (11, 1), (84673, 1), (213449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_84673
    · exact prime_213449
  · decide +kernel

theorem prime_795228183229 : Nat.Prime 795228183229 := by
  apply nodeValid_prime [2, 3, 66269015269] ⟨795228183229, 10, [(2, 2), (3, 1), (66269015269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66269015269
  · decide +kernel

theorem prime_796344573007 : Nat.Prime 796344573007 := by
  apply nodeValid_prime [2, 3, 41, 53, 384143] ⟨796344573007, 5, [(2, 1), (3, 2), (41, 1), (53, 2), (384143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_53
    · exact prime_384143
  · decide +kernel

theorem prime_796344588229 : Nat.Prime 796344588229 := by
  apply nodeValid_prime [2, 3, 7, 1354327531] ⟨796344588229, 10, [(2, 2), (3, 1), (7, 2), (1354327531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1354327531
  · decide +kernel

theorem prime_796344588497 : Nat.Prime 796344588497 := by
  apply nodeValid_prime [2, 29, 263, 6525703] ⟨796344588497, 3, [(2, 4), (29, 1), (263, 1), (6525703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_263
    · exact prime_6525703
  · decide +kernel

theorem prime_797462018851 : Nat.Prime 797462018851 := by
  apply nodeValid_prime [2, 3, 5, 7, 61, 12450617] ⟨797462018851, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (61, 1), (12450617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_12450617
  · decide +kernel

theorem prime_797462019311 : Nat.Prime 797462019311 := by
  apply nodeValid_prime [2, 5, 11, 181, 40053341] ⟨797462019311, 11, [(2, 1), (5, 1), (11, 1), (181, 1), (40053341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_181
    · exact prime_40053341
  · decide +kernel

theorem prime_797462024897 : Nat.Prime 797462024897 := by
  apply nodeValid_prime [2, 23, 2357, 229849] ⟨797462024897, 3, [(2, 6), (23, 1), (2357, 1), (229849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2357
    · exact prime_229849
  · decide +kernel

theorem prime_798580500079 : Nat.Prime 798580500079 := by
  apply nodeValid_prime [2, 3, 17, 48157, 162577] ⟨798580500079, 3, [(2, 1), (3, 1), (17, 1), (48157, 1), (162577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_48157
    · exact prime_162577
  · decide +kernel

theorem prime_798580500101 : Nat.Prime 798580500101 := by
  apply nodeValid_prime [2, 5, 7877, 1013813] ⟨798580500101, 2, [(2, 2), (5, 2), (7877, 1), (1013813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7877
    · exact prime_1013813
  · decide +kernel

theorem prime_798580544459 : Nat.Prime 798580544459 := by
  apply nodeValid_prime [2, 47, 20047, 423781] ⟨798580544459, 2, [(2, 1), (47, 1), (20047, 1), (423781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_20047
    · exact prime_423781
  · decide +kernel

end Sude.Lucas.Generated
