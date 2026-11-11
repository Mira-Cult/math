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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0104

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_13099 : Nat.Prime 13099 := by
  apply nodeValid_prime [2, 3, 37, 59] ⟨13099, 3, [(2, 1), (3, 1), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_17987 : Nat.Prime 17987 := by
  apply nodeValid_prime [2, 17, 23] ⟨17987, 5, [(2, 1), (17, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_18341 : Nat.Prime 18341 := by
  apply nodeValid_prime [2, 5, 7, 131] ⟨18341, 3, [(2, 2), (5, 1), (7, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_131
  · decide +kernel

theorem prime_19301 : Nat.Prime 19301 := by
  apply nodeValid_prime [2, 5, 193] ⟨19301, 2, [(2, 2), (5, 2), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
  · decide +kernel

theorem prime_19373 : Nat.Prime 19373 := by
  apply nodeValid_prime [2, 29, 167] ⟨19373, 2, [(2, 2), (29, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_167
  · decide +kernel

theorem prime_24749 : Nat.Prime 24749 := by
  apply nodeValid_prime [2, 23, 269] ⟨24749, 2, [(2, 2), (23, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_269
  · decide +kernel

theorem prime_30841 : Nat.Prime 30841 := by
  apply nodeValid_prime [2, 3, 5, 257] ⟨30841, 7, [(2, 3), (3, 1), (5, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
  · decide +kernel

theorem prime_39461 : Nat.Prime 39461 := by
  apply nodeValid_prime [2, 5, 1973] ⟨39461, 2, [(2, 2), (5, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1973
  · decide +kernel

theorem prime_42943 : Nat.Prime 42943 := by
  apply nodeValid_prime [2, 3, 17, 421] ⟨42943, 3, [(2, 1), (3, 1), (17, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_421
  · decide +kernel

theorem prime_45053 : Nat.Prime 45053 := by
  apply nodeValid_prime [2, 7, 1609] ⟨45053, 2, [(2, 2), (7, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1609
  · decide +kernel

theorem prime_49499 : Nat.Prime 49499 := by
  apply nodeValid_prime [2, 24749] ⟨49499, 2, [(2, 1), (24749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24749
  · decide +kernel

theorem prime_53161 : Nat.Prime 53161 := by
  apply nodeValid_prime [2, 3, 5, 443] ⟨53161, 14, [(2, 3), (3, 1), (5, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_443
  · decide +kernel

theorem prime_56377 : Nat.Prime 56377 := by
  apply nodeValid_prime [2, 3, 29] ⟨56377, 5, [(2, 3), (3, 5), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_60013 : Nat.Prime 60013 := by
  apply nodeValid_prime [2, 3, 1667] ⟨60013, 6, [(2, 2), (3, 2), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1667
  · decide +kernel

theorem prime_61057 : Nat.Prime 61057 := by
  apply nodeValid_prime [2, 3, 53] ⟨61057, 5, [(2, 7), (3, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
  · decide +kernel

theorem prime_62423 : Nat.Prime 62423 := by
  apply nodeValid_prime [2, 23, 59] ⟨62423, 5, [(2, 1), (23, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_68963 : Nat.Prime 68963 := by
  apply nodeValid_prime [2, 29, 41] ⟨68963, 2, [(2, 1), (29, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_41
  · decide +kernel

theorem prime_76387 : Nat.Prime 76387 := by
  apply nodeValid_prime [2, 3, 29, 439] ⟨76387, 3, [(2, 1), (3, 1), (29, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_439
  · decide +kernel

theorem prime_90107 : Nat.Prime 90107 := by
  apply nodeValid_prime [2, 45053] ⟨90107, 2, [(2, 1), (45053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45053
  · decide +kernel

theorem prime_92791 : Nat.Prime 92791 := by
  apply nodeValid_prime [2, 3, 5, 1031] ⟨92791, 6, [(2, 1), (3, 2), (5, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1031
  · decide +kernel

theorem prime_99013 : Nat.Prime 99013 := by
  apply nodeValid_prime [2, 3, 37, 223] ⟨99013, 6, [(2, 2), (3, 1), (37, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_223
  · decide +kernel

theorem prime_100183 : Nat.Prime 100183 := by
  apply nodeValid_prime [2, 3, 59, 283] ⟨100183, 3, [(2, 1), (3, 1), (59, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_283
  · decide +kernel

theorem prime_103307 : Nat.Prime 103307 := by
  apply nodeValid_prime [2, 7, 47, 157] ⟨103307, 2, [(2, 1), (7, 1), (47, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_157
  · decide +kernel

theorem prime_106391 : Nat.Prime 106391 := by
  apply nodeValid_prime [2, 5, 10639] ⟨106391, 23, [(2, 1), (5, 1), (10639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10639
  · decide +kernel

theorem prime_106823 : Nat.Prime 106823 := by
  apply nodeValid_prime [2, 53411] ⟨106823, 5, [(2, 1), (53411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53411
  · decide +kernel

theorem prime_121697 : Nat.Prime 121697 := by
  apply nodeValid_prime [2, 3803] ⟨121697, 3, [(2, 5), (3803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3803
  · decide +kernel

theorem prime_123733 : Nat.Prime 123733 := by
  apply nodeValid_prime [2, 3, 7, 491] ⟨123733, 6, [(2, 2), (3, 2), (7, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_491
  · decide +kernel

theorem prime_138319 : Nat.Prime 138319 := by
  apply nodeValid_prime [2, 3, 23053] ⟨138319, 3, [(2, 1), (3, 1), (23053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23053
  · decide +kernel

theorem prime_147793 : Nat.Prime 147793 := by
  apply nodeValid_prime [2, 3, 3079] ⟨147793, 5, [(2, 4), (3, 1), (3079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3079
  · decide +kernel

theorem prime_152311 : Nat.Prime 152311 := by
  apply nodeValid_prime [2, 3, 5, 5077] ⟨152311, 12, [(2, 1), (3, 1), (5, 1), (5077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5077
  · decide +kernel

theorem prime_164581 : Nat.Prime 164581 := by
  apply nodeValid_prime [2, 3, 5, 13, 211] ⟨164581, 10, [(2, 2), (3, 1), (5, 1), (13, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_211
  · decide +kernel

theorem prime_177019 : Nat.Prime 177019 := by
  apply nodeValid_prime [2, 3, 163, 181] ⟨177019, 2, [(2, 1), (3, 1), (163, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_181
  · decide +kernel

theorem prime_179909 : Nat.Prime 179909 := by
  apply nodeValid_prime [2, 41, 1097] ⟨179909, 2, [(2, 2), (41, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1097
  · decide +kernel

theorem prime_188011 : Nat.Prime 188011 := by
  apply nodeValid_prime [2, 3, 5, 2089] ⟨188011, 3, [(2, 1), (3, 2), (5, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2089
  · decide +kernel

theorem prime_191459 : Nat.Prime 191459 := by
  apply nodeValid_prime [2, 29, 3301] ⟨191459, 2, [(2, 1), (29, 1), (3301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3301
  · decide +kernel

theorem prime_194981 : Nat.Prime 194981 := by
  apply nodeValid_prime [2, 5, 9749] ⟨194981, 2, [(2, 2), (5, 1), (9749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9749
  · decide +kernel

theorem prime_229763 : Nat.Prime 229763 := by
  apply nodeValid_prime [2, 13, 8837] ⟨229763, 2, [(2, 1), (13, 1), (8837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8837
  · decide +kernel

theorem prime_239539 : Nat.Prime 239539 := by
  apply nodeValid_prime [2, 3, 13, 37, 83] ⟨239539, 3, [(2, 1), (3, 1), (13, 1), (37, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_83
  · decide +kernel

theorem prime_248903 : Nat.Prime 248903 := by
  apply nodeValid_prime [2, 97, 1283] ⟨248903, 5, [(2, 1), (97, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1283
  · decide +kernel

theorem prime_286289 : Nat.Prime 286289 := by
  apply nodeValid_prime [2, 29, 617] ⟨286289, 3, [(2, 4), (29, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_617
  · decide +kernel

theorem prime_288467 : Nat.Prime 288467 := by
  apply nodeValid_prime [2, 23, 6271] ⟨288467, 2, [(2, 1), (23, 1), (6271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_6271
  · decide +kernel

theorem prime_309317 : Nat.Prime 309317 := by
  apply nodeValid_prime [2, 7, 11047] ⟨309317, 2, [(2, 2), (7, 1), (11047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11047
  · decide +kernel

theorem prime_330061 : Nat.Prime 330061 := by
  apply nodeValid_prime [2, 3, 5, 5501] ⟨330061, 2, [(2, 2), (3, 1), (5, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5501
  · decide +kernel

theorem prime_334363 : Nat.Prime 334363 := by
  apply nodeValid_prime [2, 3, 7, 19, 419] ⟨334363, 5, [(2, 1), (3, 1), (7, 1), (19, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_419
  · decide +kernel

theorem prime_338669 : Nat.Prime 338669 := by
  apply nodeValid_prime [2, 11, 43, 179] ⟨338669, 3, [(2, 2), (11, 1), (43, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_179
  · decide +kernel

theorem prime_341863 : Nat.Prime 341863 := by
  apply nodeValid_prime [2, 3, 227, 251] ⟨341863, 3, [(2, 1), (3, 1), (227, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_251
  · decide +kernel

theorem prime_402769 : Nat.Prime 402769 := by
  apply nodeValid_prime [2, 3, 2797] ⟨402769, 14, [(2, 4), (3, 2), (2797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2797
  · decide +kernel

theorem prime_466777 : Nat.Prime 466777 := by
  apply nodeValid_prime [2, 3, 2161] ⟨466777, 5, [(2, 3), (3, 3), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2161
  · decide +kernel

theorem prime_514757 : Nat.Prime 514757 := by
  apply nodeValid_prime [2, 11, 11699] ⟨514757, 2, [(2, 2), (11, 1), (11699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11699
  · decide +kernel

theorem prime_531611 : Nat.Prime 531611 := by
  apply nodeValid_prime [2, 5, 53161] ⟨531611, 2, [(2, 1), (5, 1), (53161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53161
  · decide +kernel

theorem prime_634757 : Nat.Prime 634757 := by
  apply nodeValid_prime [2, 31, 5119] ⟨634757, 2, [(2, 2), (31, 1), (5119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_5119
  · decide +kernel

theorem prime_642403 : Nat.Prime 642403 := by
  apply nodeValid_prime [2, 3, 89, 401] ⟨642403, 2, [(2, 1), (3, 2), (89, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_401
  · decide +kernel

theorem prime_669649 : Nat.Prime 669649 := by
  apply nodeValid_prime [2, 3, 7, 1993] ⟨669649, 11, [(2, 4), (3, 1), (7, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1993
  · decide +kernel

theorem prime_766531 : Nat.Prime 766531 := by
  apply nodeValid_prime [2, 3, 5, 17, 167] ⟨766531, 31, [(2, 1), (3, 3), (5, 1), (17, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_167
  · decide +kernel

theorem prime_841237 : Nat.Prime 841237 := by
  apply nodeValid_prime [2, 3, 11, 6373] ⟨841237, 2, [(2, 2), (3, 1), (11, 1), (6373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6373
  · decide +kernel

theorem prime_1378579 : Nat.Prime 1378579 := by
  apply nodeValid_prime [2, 3, 229763] ⟨1378579, 2, [(2, 1), (3, 1), (229763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229763
  · decide +kernel

theorem prime_1520107 : Nat.Prime 1520107 := by
  apply nodeValid_prime [2, 3, 7, 17, 2129] ⟨1520107, 2, [(2, 1), (3, 1), (7, 1), (17, 1), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_2129
  · decide +kernel

theorem prime_1605691 : Nat.Prime 1605691 := by
  apply nodeValid_prime [2, 3, 5, 19, 313] ⟨1605691, 2, [(2, 1), (3, 3), (5, 1), (19, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_313
  · decide +kernel

theorem prime_2342783 : Nat.Prime 2342783 := by
  apply nodeValid_prime [2, 13, 90107] ⟨2342783, 5, [(2, 1), (13, 1), (90107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_90107
  · decide +kernel

theorem prime_2518181 : Nat.Prime 2518181 := by
  apply nodeValid_prime [2, 5, 7, 17987] ⟨2518181, 2, [(2, 2), (5, 1), (7, 1), (17987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17987
  · decide +kernel

theorem prime_2792509 : Nat.Prime 2792509 := by
  apply nodeValid_prime [2, 3, 232709] ⟨2792509, 2, [(2, 2), (3, 1), (232709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_232709
  · decide +kernel

theorem prime_3272119 : Nat.Prime 3272119 := by
  apply nodeValid_prime [2, 3, 23, 131, 181] ⟨3272119, 3, [(2, 1), (3, 1), (23, 1), (131, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_131
    · exact prime_181
  · decide +kernel

theorem prime_3273233 : Nat.Prime 3273233 := by
  apply nodeValid_prime [2, 149, 1373] ⟨3273233, 3, [(2, 4), (149, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_1373
  · decide +kernel

theorem prime_4038539 : Nat.Prime 4038539 := by
  apply nodeValid_prime [2, 7, 288467] ⟨4038539, 2, [(2, 1), (7, 1), (288467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_288467
  · decide +kernel

theorem prime_4503731 : Nat.Prime 4503731 := by
  apply nodeValid_prime [2, 5, 7, 11, 5849] ⟨4503731, 2, [(2, 1), (5, 1), (7, 1), (11, 1), (5849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_5849
  · decide +kernel

theorem prime_4583239 : Nat.Prime 4583239 := by
  apply nodeValid_prime [2, 3, 11, 59, 107] ⟨4583239, 3, [(2, 1), (3, 1), (11, 2), (59, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_107
  · decide +kernel

theorem prime_4901257 : Nat.Prime 4901257 := by
  apply nodeValid_prime [2, 3, 22691] ⟨4901257, 5, [(2, 3), (3, 3), (22691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22691
  · decide +kernel

theorem prime_4955519 : Nat.Prime 4955519 := by
  apply nodeValid_prime [2, 61, 151, 269] ⟨4955519, 7, [(2, 1), (61, 1), (151, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_151
    · exact prime_269
  · decide +kernel

theorem prime_5051009 : Nat.Prime 5051009 := by
  apply nodeValid_prime [2, 39461] ⟨5051009, 3, [(2, 7), (39461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39461
  · decide +kernel

theorem prime_5272447 : Nat.Prime 5272447 := by
  apply nodeValid_prime [2, 3, 503, 1747] ⟨5272447, 3, [(2, 1), (3, 1), (503, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
    · exact prime_1747
  · decide +kernel

theorem prime_5397001 : Nat.Prime 5397001 := by
  apply nodeValid_prime [2, 3, 5, 7, 257] ⟨5397001, 23, [(2, 3), (3, 1), (5, 3), (7, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_257
  · decide +kernel

theorem prime_5809399 : Nat.Prime 5809399 := by
  apply nodeValid_prime [2, 3, 7, 138319] ⟨5809399, 6, [(2, 1), (3, 1), (7, 1), (138319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_138319
  · decide +kernel

theorem prime_6964829 : Nat.Prime 6964829 := by
  apply nodeValid_prime [2, 13, 10303] ⟨6964829, 2, [(2, 2), (13, 2), (10303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10303
  · decide +kernel

theorem prime_7920173 : Nat.Prime 7920173 := by
  apply nodeValid_prime [2, 13, 152311] ⟨7920173, 2, [(2, 2), (13, 1), (152311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_152311
  · decide +kernel

theorem prime_8077079 : Nat.Prime 8077079 := by
  apply nodeValid_prime [2, 4038539] ⟨8077079, 17, [(2, 1), (4038539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4038539
  · decide +kernel

theorem prime_8661311 : Nat.Prime 8661311 := by
  apply nodeValid_prime [2, 5, 7, 123733] ⟨8661311, 7, [(2, 1), (5, 1), (7, 1), (123733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_123733
  · decide +kernel

theorem prime_11287807 : Nat.Prime 11287807 := by
  apply nodeValid_prime [2, 3, 61, 30841] ⟨11287807, 3, [(2, 1), (3, 1), (61, 1), (30841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_30841
  · decide +kernel

theorem prime_12767903 : Nat.Prime 12767903 := by
  apply nodeValid_prime [2, 7, 839, 1087] ⟨12767903, 5, [(2, 1), (7, 1), (839, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_839
    · exact prime_1087
  · decide +kernel

theorem prime_20599603 : Nat.Prime 20599603 := by
  apply nodeValid_prime [2, 3, 37, 92791] ⟨20599603, 2, [(2, 1), (3, 1), (37, 1), (92791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_92791
  · decide +kernel

theorem prime_22352861 : Nat.Prime 22352861 := by
  apply nodeValid_prime [2, 5, 31, 1163] ⟨22352861, 2, [(2, 2), (5, 1), (31, 2), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1163
  · decide +kernel

theorem prime_23237597 : Nat.Prime 23237597 := by
  apply nodeValid_prime [2, 5809399] ⟨23237597, 2, [(2, 2), (5809399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5809399
  · decide +kernel

theorem prime_31737851 : Nat.Prime 31737851 := by
  apply nodeValid_prime [2, 5, 634757] ⟨31737851, 2, [(2, 1), (5, 2), (634757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_634757
  · decide +kernel

theorem prime_42025001 : Nat.Prime 42025001 := by
  apply nodeValid_prime [2, 5, 41] ⟨42025001, 3, [(2, 3), (5, 5), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_44705723 : Nat.Prime 44705723 := by
  apply nodeValid_prime [2, 22352861] ⟨44705723, 2, [(2, 1), (22352861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22352861
  · decide +kernel

theorem prime_53078329 : Nat.Prime 53078329 := by
  apply nodeValid_prime [2, 3, 101, 811] ⟨53078329, 11, [(2, 3), (3, 4), (101, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_811
  · decide +kernel

theorem prime_63475703 : Nat.Prime 63475703 := by
  apply nodeValid_prime [2, 31737851] ⟨63475703, 5, [(2, 1), (31737851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31737851
  · decide +kernel

theorem prime_63876889 : Nat.Prime 63876889 := by
  apply nodeValid_prime [2, 3, 17, 23, 2269] ⟨63876889, 7, [(2, 3), (3, 2), (17, 1), (23, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_2269
  · decide +kernel

theorem prime_81957899 : Nat.Prime 81957899 := by
  apply nodeValid_prime [2, 11, 338669] ⟨81957899, 2, [(2, 1), (11, 2), (338669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_338669
  · decide +kernel

theorem prime_140822447 : Nat.Prime 140822447 := by
  apply nodeValid_prime [2, 1021, 68963] ⟨140822447, 5, [(2, 1), (1021, 1), (68963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1021
    · exact prime_68963
  · decide +kernel

theorem prime_151877857 : Nat.Prime 151877857 := by
  apply nodeValid_prime [2, 3, 13, 121697] ⟨151877857, 5, [(2, 5), (3, 1), (13, 1), (121697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_121697
  · decide +kernel

theorem prime_182779739 : Nat.Prime 182779739 := by
  apply nodeValid_prime [2, 859, 106391] ⟨182779739, 2, [(2, 1), (859, 1), (106391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_859
    · exact prime_106391
  · decide +kernel

theorem prime_213707623 : Nat.Prime 213707623 := by
  apply nodeValid_prime [2, 3, 67, 531611] ⟨213707623, 3, [(2, 1), (3, 1), (67, 1), (531611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_531611
  · decide +kernel

theorem prime_242287631 : Nat.Prime 242287631 := by
  apply nodeValid_prime [2, 5, 13, 31, 59, 1019] ⟨242287631, 11, [(2, 1), (5, 1), (13, 1), (31, 1), (59, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_59
    · exact prime_1019
  · decide +kernel

theorem prime_257028463 : Nat.Prime 257028463 := by
  apply nodeValid_prime [2, 3, 223, 64033] ⟨257028463, 5, [(2, 1), (3, 2), (223, 1), (64033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_64033
  · decide +kernel

theorem prime_265830893 : Nat.Prime 265830893 := by
  apply nodeValid_prime [2, 79, 841237] ⟨265830893, 2, [(2, 2), (79, 1), (841237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_841237
  · decide +kernel

theorem prime_284478343 : Nat.Prime 284478343 := by
  apply nodeValid_prime [2, 3, 29, 56377] ⟨284478343, 6, [(2, 1), (3, 1), (29, 2), (56377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_56377
  · decide +kernel

theorem prime_301286339 : Nat.Prime 301286339 := by
  apply nodeValid_prime [2, 23, 37, 177019] ⟨301286339, 2, [(2, 1), (23, 1), (37, 1), (177019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_177019
  · decide +kernel

theorem prime_349459813 : Nat.Prime 349459813 := by
  apply nodeValid_prime [2, 3, 13, 248903] ⟨349459813, 2, [(2, 2), (3, 3), (13, 1), (248903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_248903
  · decide +kernel

theorem prime_365559479 : Nat.Prime 365559479 := by
  apply nodeValid_prime [2, 182779739] ⟨365559479, 19, [(2, 1), (182779739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_182779739
  · decide +kernel

theorem prime_484575263 : Nat.Prime 484575263 := by
  apply nodeValid_prime [2, 242287631] ⟨484575263, 5, [(2, 1), (242287631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_242287631
  · decide +kernel

theorem prime_760336609 : Nat.Prime 760336609 := by
  apply nodeValid_prime [2, 3, 7920173] ⟨760336609, 23, [(2, 5), (3, 1), (7920173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7920173
  · decide +kernel

theorem prime_1427503513 : Nat.Prime 1427503513 := by
  apply nodeValid_prime [2, 3, 37, 797, 2017] ⟨1427503513, 5, [(2, 3), (3, 1), (37, 1), (797, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_797
    · exact prime_2017
  · decide +kernel

theorem prime_2376246101 : Nat.Prime 2376246101 := by
  apply nodeValid_prime [2, 5, 31, 766531] ⟨2376246101, 2, [(2, 2), (5, 2), (31, 1), (766531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_766531
  · decide +kernel

theorem prime_2589846617 : Nat.Prime 2589846617 := by
  apply nodeValid_prime [2, 7, 281, 164581] ⟨2589846617, 3, [(2, 3), (7, 1), (281, 1), (164581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_281
    · exact prime_164581
  · decide +kernel

theorem prime_2682343381 : Nat.Prime 2682343381 := by
  apply nodeValid_prime [2, 3, 5, 44705723] ⟨2682343381, 6, [(2, 2), (3, 1), (5, 1), (44705723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_44705723
  · decide +kernel

theorem prime_2788073551 : Nat.Prime 2788073551 := by
  apply nodeValid_prime [2, 3, 5, 283, 21893] ⟨2788073551, 3, [(2, 1), (3, 2), (5, 2), (283, 1), (21893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_283
    · exact prime_21893
  · decide +kernel

theorem prime_3345838609 : Nat.Prime 3345838609 := by
  apply nodeValid_prime [2, 3, 7, 619, 16087] ⟨3345838609, 23, [(2, 4), (3, 1), (7, 1), (619, 1), (16087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_619
    · exact prime_16087
  · decide +kernel

theorem prime_3424276073 : Nat.Prime 3424276073 := by
  apply nodeValid_prime [2, 7, 131, 466777] ⟨3424276073, 3, [(2, 3), (7, 1), (131, 1), (466777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_466777
  · decide +kernel

theorem prime_3495345991 : Nat.Prime 3495345991 := by
  apply nodeValid_prime [2, 3, 5, 353, 330061] ⟨3495345991, 3, [(2, 1), (3, 1), (5, 1), (353, 1), (330061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
    · exact prime_330061
  · decide +kernel

theorem prime_6143519801 : Nat.Prime 6143519801 := by
  apply nodeValid_prime [2, 5, 11, 2792509] ⟨6143519801, 6, [(2, 3), (5, 2), (11, 1), (2792509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2792509
  · decide +kernel

theorem prime_19783915321 : Nat.Prime 19783915321 := by
  apply nodeValid_prime [2, 3, 5, 13, 41, 309317] ⟨19783915321, 19, [(2, 3), (3, 1), (5, 1), (13, 1), (41, 1), (309317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_309317
  · decide +kernel

theorem prime_19913484011 : Nat.Prime 19913484011 := by
  apply nodeValid_prime [2, 5, 7, 284478343] ⟨19913484011, 2, [(2, 1), (5, 1), (7, 1), (284478343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_284478343
  · decide +kernel

theorem prime_21504308953 : Nat.Prime 21504308953 := by
  apply nodeValid_prime [2, 3, 7, 997, 18341] ⟨21504308953, 10, [(2, 3), (3, 1), (7, 2), (997, 1), (18341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_997
    · exact prime_18341
  · decide +kernel

theorem prime_24188547143 : Nat.Prime 24188547143 := by
  apply nodeValid_prime [2, 181, 349, 191459] ⟨24188547143, 5, [(2, 1), (181, 1), (349, 1), (191459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_349
    · exact prime_191459
  · decide +kernel

theorem prime_36861118807 : Nat.Prime 36861118807 := by
  apply nodeValid_prime [2, 3, 6143519801] ⟨36861118807, 5, [(2, 1), (3, 1), (6143519801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6143519801
  · decide +kernel

theorem prime_39826968023 : Nat.Prime 39826968023 := by
  apply nodeValid_prime [2, 19913484011] ⟨39826968023, 5, [(2, 1), (19913484011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19913484011
  · decide +kernel

theorem prime_45376984141 : Nat.Prime 45376984141 := by
  apply nodeValid_prime [2, 3, 5, 67, 11287807] ⟨45376984141, 2, [(2, 2), (3, 1), (5, 1), (67, 1), (11287807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_11287807
  · decide +kernel

theorem prime_88820059201 : Nat.Prime 88820059201 := by
  apply nodeValid_prime [2, 3, 5, 31, 137, 4357] ⟨88820059201, 7, [(2, 6), (3, 1), (5, 2), (31, 1), (137, 1), (4357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_137
    · exact prime_4357
  · decide +kernel

theorem prime_108507837457 : Nat.Prime 108507837457 := by
  apply nodeValid_prime [2, 3, 17, 5881, 7537] ⟨108507837457, 5, [(2, 4), (3, 2), (17, 1), (5881, 1), (7537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_5881
    · exact prime_7537
  · decide +kernel

theorem prime_183204050273 : Nat.Prime 183204050273 := by
  apply nodeValid_prime [2, 661, 8661311] ⟨183204050273, 3, [(2, 5), (661, 1), (8661311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_661
    · exact prime_8661311
  · decide +kernel

theorem prime_206893750961 : Nat.Prime 206893750961 := by
  apply nodeValid_prime [2, 5, 13, 79, 2518181] ⟨206893750961, 3, [(2, 4), (5, 1), (13, 1), (79, 1), (2518181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_79
    · exact prime_2518181
  · decide +kernel

theorem prime_306913263961 : Nat.Prime 306913263961 := by
  apply nodeValid_prime [2, 3, 5, 37, 89, 179, 4339] ⟨306913263961, 11, [(2, 3), (3, 1), (5, 1), (37, 1), (89, 1), (179, 1), (4339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_89
    · exact prime_179
    · exact prime_4339
  · decide +kernel

theorem prime_457225353077 : Nat.Prime 457225353077 := by
  apply nodeValid_prime [2, 334363, 341863] ⟨457225353077, 2, [(2, 2), (334363, 1), (341863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_334363
    · exact prime_341863
  · decide +kernel

theorem prime_611203801781 : Nat.Prime 611203801781 := by
  apply nodeValid_prime [2, 5, 11, 13, 213707623] ⟨611203801781, 2, [(2, 2), (5, 1), (11, 1), (13, 1), (213707623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_213707623
  · decide +kernel

theorem prime_618566596643 : Nat.Prime 618566596643 := by
  apply nodeValid_prime [2, 23, 31, 41, 293, 36109] ⟨618566596643, 2, [(2, 1), (23, 1), (31, 1), (41, 1), (293, 1), (36109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_41
    · exact prime_293
    · exact prime_36109
  · decide +kernel

theorem prime_619623310981 : Nat.Prime 619623310981 := by
  apply nodeValid_prime [2, 3, 5, 2293, 4503731] ⟨619623310981, 2, [(2, 2), (3, 1), (5, 1), (2293, 1), (4503731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2293
    · exact prime_4503731
  · decide +kernel

theorem prime_3654666503339 : Nat.Prime 3654666503339 := by
  apply nodeValid_prime [2, 769, 2376246101] ⟨3654666503339, 2, [(2, 1), (769, 1), (2376246101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_769
    · exact prime_2376246101
  · decide +kernel

theorem prime_3654666632209 : Nat.Prime 3654666632209 := by
  apply nodeValid_prime [2, 3, 929, 81957899] ⟨3654666632209, 11, [(2, 4), (3, 1), (929, 1), (81957899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
    · exact prime_81957899
  · decide +kernel

theorem prime_3654666633547 : Nat.Prime 3654666633547 := by
  apply nodeValid_prime [2, 3, 419, 484575263] ⟨3654666633547, 2, [(2, 1), (3, 2), (419, 1), (484575263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419
    · exact prime_484575263
  · decide +kernel

theorem prime_3657802823879 : Nat.Prime 3657802823879 := by
  apply nodeValid_prime [2, 7, 23, 233, 6964829] ⟨3657802823879, 7, [(2, 1), (7, 2), (23, 1), (233, 1), (6964829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_233
    · exact prime_6964829
  · decide +kernel

theorem prime_3657802824617 : Nat.Prime 3657802824617 := by
  apply nodeValid_prime [2, 457225353077] ⟨3657802824617, 3, [(2, 3), (457225353077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_457225353077
  · decide +kernel

theorem prime_3657802853501 : Nat.Prime 3657802853501 := by
  apply nodeValid_prime [2, 5, 49499, 147793] ⟨3657802853501, 3, [(2, 2), (5, 3), (49499, 1), (147793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49499
    · exact prime_147793
  · decide +kernel

theorem prime_3660941000989 : Nat.Prime 3660941000989 := by
  apply nodeValid_prime [2, 3, 97, 349459813] ⟨3660941000989, 6, [(2, 2), (3, 3), (97, 1), (349459813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_349459813
  · decide +kernel

theorem prime_3660941017147 : Nat.Prime 3660941017147 := by
  apply nodeValid_prime [2, 3, 7, 17257, 5051009] ⟨3660941017147, 3, [(2, 1), (3, 1), (7, 1), (17257, 1), (5051009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17257
    · exact prime_5051009
  · decide +kernel

theorem prime_3664081005461 : Nat.Prime 3664081005461 := by
  apply nodeValid_prime [2, 5, 183204050273] ⟨3664081005461, 11, [(2, 2), (5, 1), (183204050273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_183204050273
  · decide +kernel

theorem prime_3664081058117 : Nat.Prime 3664081058117 := by
  apply nodeValid_prime [2, 23, 39826968023] ⟨3664081058117, 2, [(2, 2), (23, 1), (39826968023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_39826968023
  · decide +kernel

theorem prime_3664081058447 : Nat.Prime 3664081058447 := by
  apply nodeValid_prime [2, 683, 2682343381] ⟨3664081058447, 5, [(2, 1), (683, 1), (2682343381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_683
    · exact prime_2682343381
  · decide +kernel

theorem prime_3667222809673 : Nat.Prime 3667222809673 := by
  apply nodeValid_prime [2, 3, 59, 2589846617] ⟨3667222809673, 5, [(2, 3), (3, 1), (59, 1), (2589846617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2589846617
  · decide +kernel

theorem prime_3667222810687 : Nat.Prime 3667222810687 := by
  apply nodeValid_prime [2, 3, 611203801781] ⟨3667222810687, 3, [(2, 1), (3, 1), (611203801781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_611203801781
  · decide +kernel

theorem prime_3667222814533 : Nat.Prime 3667222814533 := by
  apply nodeValid_prime [2, 3, 83, 743, 4955519] ⟨3667222814533, 2, [(2, 2), (3, 1), (83, 1), (743, 1), (4955519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_743
    · exact prime_4955519
  · decide +kernel

theorem prime_3670366441207 : Nat.Prime 3670366441207 := by
  apply nodeValid_prime [2, 3, 2267, 7307, 36929] ⟨3670366441207, 3, [(2, 1), (3, 1), (2267, 1), (7307, 1), (36929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2267
    · exact prime_7307
    · exact prime_36929
  · decide +kernel

theorem prime_3670366450351 : Nat.Prime 3670366450351 := by
  apply nodeValid_prime [2, 3, 5, 461, 53078329] ⟨3670366450351, 6, [(2, 1), (3, 1), (5, 2), (461, 1), (53078329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_461
    · exact prime_53078329
  · decide +kernel

theorem prime_3670366451641 : Nat.Prime 3670366451641 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 257028463] ⟨3670366451641, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (17, 1), (257028463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_257028463
  · decide +kernel

theorem prime_3673511857397 : Nat.Prime 3673511857397 := by
  apply nodeValid_prime [2, 17, 23059, 2342783] ⟨3673511857397, 2, [(2, 2), (17, 1), (23059, 1), (2342783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23059
    · exact prime_2342783
  · decide +kernel

theorem prime_3673511857699 : Nat.Prime 3673511857699 := by
  apply nodeValid_prime [2, 3, 402769, 1520107] ⟨3673511857699, 2, [(2, 1), (3, 1), (402769, 1), (1520107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_402769
    · exact prime_1520107
  · decide +kernel

theorem prime_3673511890891 : Nat.Prime 3673511890891 := by
  apply nodeValid_prime [2, 3, 5, 26717, 4583239] ⟨3673511890891, 3, [(2, 1), (3, 1), (5, 1), (26717, 1), (4583239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_26717
    · exact prime_4583239
  · decide +kernel

theorem prime_3676659162257 : Nat.Prime 3676659162257 := by
  apply nodeValid_prime [2, 17, 89, 151877857] ⟨3676659162257, 3, [(2, 4), (17, 1), (89, 1), (151877857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_89
    · exact prime_151877857
  · decide +kernel

theorem prime_3676659164369 : Nat.Prime 3676659164369 := by
  apply nodeValid_prime [2, 19, 31, 283, 1378579] ⟨3676659164369, 6, [(2, 4), (19, 1), (31, 1), (283, 1), (1378579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_283
    · exact prime_1378579
  · decide +kernel

theorem prime_3676659165737 : Nat.Prime 3676659165737 := by
  apply nodeValid_prime [2, 19, 24188547143] ⟨3676659165737, 3, [(2, 3), (19, 1), (24188547143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_24188547143
  · decide +kernel

theorem prime_3679808249707 : Nat.Prime 3679808249707 := by
  apply nodeValid_prime [2, 3, 31, 19783915321] ⟨3679808249707, 2, [(2, 1), (3, 1), (31, 1), (19783915321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_19783915321
  · decide +kernel

theorem prime_3679808309371 : Nat.Prime 3679808309371 := by
  apply nodeValid_prime [2, 3, 5, 61057, 669649] ⟨3679808309371, 3, [(2, 1), (3, 2), (5, 1), (61057, 1), (669649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61057
    · exact prime_669649
  · decide +kernel

theorem prime_3679808310781 : Nat.Prime 3679808310781 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 43, 1049, 10223] ⟨3679808310781, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (43, 1), (1049, 1), (10223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_43
    · exact prime_1049
    · exact prime_10223
  · decide +kernel

theorem prime_3682959062611 : Nat.Prime 3682959062611 := by
  apply nodeValid_prime [2, 3, 5, 97, 6491, 194981] ⟨3682959062611, 2, [(2, 1), (3, 1), (5, 1), (97, 1), (6491, 1), (194981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_6491
    · exact prime_194981
  · decide +kernel

theorem prime_3682959063541 : Nat.Prime 3682959063541 := by
  apply nodeValid_prime [2, 3, 5, 43, 1427503513] ⟨3682959063541, 10, [(2, 2), (3, 1), (5, 1), (43, 1), (1427503513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_1427503513
  · decide +kernel

theorem prime_3682959167533 : Nat.Prime 3682959167533 := by
  apply nodeValid_prime [2, 3, 306913263961] ⟨3682959167533, 2, [(2, 2), (3, 1), (306913263961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_306913263961
  · decide +kernel

theorem prime_3686111880433 : Nat.Prime 3686111880433 := by
  apply nodeValid_prime [2, 3, 101, 760336609] ⟨3686111880433, 5, [(2, 4), (3, 1), (101, 1), (760336609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_760336609
  · decide +kernel

theorem prime_3686111880701 : Nat.Prime 3686111880701 := by
  apply nodeValid_prime [2, 5, 36861118807] ⟨3686111880701, 3, [(2, 2), (5, 2), (36861118807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_36861118807
  · decide +kernel

theorem prime_3686111908961 : Nat.Prime 3686111908961 := by
  apply nodeValid_prime [2, 5, 13, 293, 971, 6229] ⟨3686111908961, 6, [(2, 5), (5, 1), (13, 1), (293, 1), (971, 1), (6229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_293
    · exact prime_971
    · exact prime_6229
  · decide +kernel

theorem prime_3689266466507 : Nat.Prime 3689266466507 := by
  apply nodeValid_prime [2, 13099, 140822447] ⟨3689266466507, 2, [(2, 1), (13099, 1), (140822447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13099
    · exact prime_140822447
  · decide +kernel

theorem prime_3689266467149 : Nat.Prime 3689266467149 := by
  apply nodeValid_prime [2, 23, 62423, 642403] ⟨3689266467149, 2, [(2, 2), (23, 1), (62423, 1), (642403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_62423
    · exact prime_642403
  · decide +kernel

theorem prime_3689266473539 : Nat.Prime 3689266473539 := by
  apply nodeValid_prime [2, 17, 108507837457] ⟨3689266473539, 2, [(2, 1), (17, 1), (108507837457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_108507837457
  · decide +kernel

theorem prime_3692422857379 : Nat.Prime 3692422857379 := by
  apply nodeValid_prime [2, 3, 188011, 3273233] ⟨3692422857379, 2, [(2, 1), (3, 1), (188011, 1), (3273233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_188011
    · exact prime_3273233
  · decide +kernel

theorem prime_3692422997467 : Nat.Prime 3692422997467 := by
  apply nodeValid_prime [2, 3, 7, 233, 733, 514757] ⟨3692422997467, 3, [(2, 1), (3, 1), (7, 1), (233, 1), (733, 1), (514757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_233
    · exact prime_733
    · exact prime_514757
  · decide +kernel

theorem prime_3692422998163 : Nat.Prime 3692422998163 := by
  apply nodeValid_prime [2, 3, 191, 199, 5397001] ⟨3692422998163, 2, [(2, 1), (3, 2), (191, 1), (199, 1), (5397001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_199
    · exact prime_5397001
  · decide +kernel

theorem prime_3695581074487 : Nat.Prime 3695581074487 := by
  apply nodeValid_prime [2, 3, 7, 331, 265830893] ⟨3695581074487, 11, [(2, 1), (3, 1), (7, 1), (331, 1), (265830893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_331
    · exact prime_265830893
  · decide +kernel

theorem prime_3695581159999 : Nat.Prime 3695581159999 := by
  apply nodeValid_prime [2, 3, 7, 13, 5197, 100183] ⟨3695581159999, 3, [(2, 1), (3, 1), (7, 1), (13, 2), (5197, 1), (100183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_5197
    · exact prime_100183
  · decide +kernel

theorem prime_3698741117063 : Nat.Prime 3698741117063 := by
  apply nodeValid_prime [2, 17, 5281, 20599603] ⟨3698741117063, 5, [(2, 1), (17, 1), (5281, 1), (20599603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_5281
    · exact prime_20599603
  · decide +kernel

theorem prime_3698741139631 : Nat.Prime 3698741139631 := by
  apply nodeValid_prime [2, 3, 5, 1129, 2543, 42943] ⟨3698741139631, 6, [(2, 1), (3, 1), (5, 1), (1129, 1), (2543, 1), (42943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1129
    · exact prime_2543
    · exact prime_42943
  · decide +kernel

theorem prime_3698741139917 : Nat.Prime 3698741139917 := by
  apply nodeValid_prime [2, 43, 21504308953] ⟨3698741139917, 2, [(2, 2), (43, 1), (21504308953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_21504308953
  · decide +kernel

theorem prime_3701902994651 : Nat.Prime 3701902994651 := by
  apply nodeValid_prime [2, 5, 7, 99013, 106823] ⟨3701902994651, 2, [(2, 1), (5, 2), (7, 1), (99013, 1), (106823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_99013
    · exact prime_106823
  · decide +kernel

theorem prime_3701902998961 : Nat.Prime 3701902998961 := by
  apply nodeValid_prime [2, 3, 5, 63475703] ⟨3701902998961, 7, [(2, 4), (3, 6), (5, 1), (63475703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_63475703
  · decide +kernel

theorem prime_3701903001439 : Nat.Prime 3701903001439 := by
  apply nodeValid_prime [2, 3, 76387, 8077079] ⟨3701903001439, 3, [(2, 1), (3, 1), (76387, 1), (8077079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76387
    · exact prime_8077079
  · decide +kernel

theorem prime_3705066710987 : Nat.Prime 3705066710987 := by
  apply nodeValid_prime [2, 541, 3424276073] ⟨3705066710987, 2, [(2, 1), (541, 1), (3424276073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_541
    · exact prime_3424276073
  · decide +kernel

theorem prime_3705066750461 : Nat.Prime 3705066750461 := by
  apply nodeValid_prime [2, 5, 53, 3495345991] ⟨3705066750461, 2, [(2, 2), (5, 1), (53, 1), (3495345991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_3495345991
  · decide +kernel

theorem prime_3705066750569 : Nat.Prime 3705066750569 := by
  apply nodeValid_prime [2, 683, 11299, 60013] ⟨3705066750569, 3, [(2, 3), (683, 1), (11299, 1), (60013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_683
    · exact prime_11299
    · exact prime_60013
  · decide +kernel

theorem prime_3708232231117 : Nat.Prime 3708232231117 := by
  apply nodeValid_prime [2, 3, 7, 9007, 4901257] ⟨3708232231117, 2, [(2, 2), (3, 1), (7, 1), (9007, 1), (4901257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9007
    · exact prime_4901257
  · decide +kernel

theorem prime_3708232231471 : Nat.Prime 3708232231471 := by
  apply nodeValid_prime [2, 3, 5, 13, 173, 2837, 19373] ⟨3708232231471, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (173, 1), (2837, 1), (19373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_173
    · exact prime_2837
    · exact prime_19373
  · decide +kernel

theorem prime_3708232260413 : Nat.Prime 3708232260413 := by
  apply nodeValid_prime [2, 17, 181, 301286339] ⟨3708232260413, 2, [(2, 2), (17, 1), (181, 1), (301286339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_181
    · exact prime_301286339
  · decide +kernel

theorem prime_3711399579847 : Nat.Prime 3711399579847 := by
  apply nodeValid_prime [2, 3, 7, 769, 12767903] ⟨3711399579847, 6, [(2, 1), (3, 3), (7, 1), (769, 1), (12767903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_769
    · exact prime_12767903
  · decide +kernel

theorem prime_3711399579859 : Nat.Prime 3711399579859 := by
  apply nodeValid_prime [2, 3, 618566596643] ⟨3711399579859, 3, [(2, 1), (3, 1), (618566596643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_618566596643
  · decide +kernel

theorem prime_3711399636559 : Nat.Prime 3711399636559 := by
  apply nodeValid_prime [2, 3, 47, 45971, 286289] ⟨3711399636559, 3, [(2, 1), (3, 1), (47, 1), (45971, 1), (286289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_45971
    · exact prime_286289
  · decide +kernel

theorem prime_3714568849129 : Nat.Prime 3714568849129 := by
  apply nodeValid_prime [2, 3, 2423, 63876889] ⟨3714568849129, 11, [(2, 3), (3, 1), (2423, 1), (63876889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2423
    · exact prime_63876889
  · decide +kernel

theorem prime_3714568889189 : Nat.Prime 3714568889189 := by
  apply nodeValid_prime [2, 59, 89, 983, 179909] ⟨3714568889189, 2, [(2, 2), (59, 1), (89, 1), (983, 1), (179909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_89
    · exact prime_983
    · exact prime_179909
  · decide +kernel

theorem prime_3714568889429 : Nat.Prime 3714568889429 := by
  apply nodeValid_prime [2, 1187, 7573, 103307] ⟨3714568889429, 2, [(2, 2), (1187, 1), (7573, 1), (103307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1187
    · exact prime_7573
    · exact prime_103307
  · decide +kernel

theorem prime_3717739865887 : Nat.Prime 3717739865887 := by
  apply nodeValid_prime [2, 3, 619623310981] ⟨3717739865887, 5, [(2, 1), (3, 1), (619623310981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619623310981
  · decide +kernel

theorem prime_3717739868233 : Nat.Prime 3717739868233 := by
  apply nodeValid_prime [2, 3, 13, 41, 181, 1605691] ⟨3717739868233, 5, [(2, 3), (3, 1), (13, 1), (41, 1), (181, 1), (1605691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_181
    · exact prime_1605691
  · decide +kernel

theorem prime_3717739901431 : Nat.Prime 3717739901431 := by
  apply nodeValid_prime [2, 3, 5, 113, 365559479] ⟨3717739901431, 3, [(2, 1), (3, 2), (5, 1), (113, 1), (365559479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_365559479
  · decide +kernel

theorem prime_3720912699563 : Nat.Prime 3720912699563 := by
  apply nodeValid_prime [2, 41, 45376984141] ⟨3720912699563, 2, [(2, 1), (41, 1), (45376984141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_45376984141
  · decide +kernel

theorem prime_3720912789421 : Nat.Prime 3720912789421 := by
  apply nodeValid_prime [2, 3, 5, 31, 19301, 34549] ⟨3720912789421, 2, [(2, 2), (3, 2), (5, 1), (31, 1), (19301, 1), (34549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_19301
    · exact prime_34549
  · decide +kernel

theorem prime_3724087488617 : Nat.Prime 3724087488617 := by
  apply nodeValid_prime [2, 11, 19, 53, 42025001] ⟨3724087488617, 3, [(2, 3), (11, 1), (19, 1), (53, 1), (42025001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_53
    · exact prime_42025001
  · decide +kernel

theorem prime_3724087489511 : Nat.Prime 3724087489511 := by
  apply nodeValid_prime [2, 5, 23, 37, 83, 5272447] ⟨3724087489511, 7, [(2, 1), (5, 1), (23, 1), (37, 1), (83, 1), (5272447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_83
    · exact prime_5272447
  · decide +kernel

theorem prime_3724087517299 : Nat.Prime 3724087517299 := by
  apply nodeValid_prime [2, 3, 206893750961] ⟨3724087517299, 2, [(2, 1), (3, 2), (206893750961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_206893750961
  · decide +kernel

theorem prime_3727264083607 : Nat.Prime 3727264083607 := by
  apply nodeValid_prime [2, 3, 7, 19, 67, 23237597] ⟨3727264083607, 5, [(2, 1), (3, 2), (7, 1), (19, 1), (67, 1), (23237597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_67
    · exact prime_23237597
  · decide +kernel

theorem prime_3727264208663 : Nat.Prime 3727264208663 := by
  apply nodeValid_prime [2, 23, 24763, 3272119] ⟨3727264208663, 5, [(2, 1), (23, 1), (24763, 1), (3272119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_24763
    · exact prime_3272119
  · decide +kernel

theorem prime_3727264210427 : Nat.Prime 3727264210427 := by
  apply nodeValid_prime [2, 557, 3345838609] ⟨3727264210427, 2, [(2, 1), (557, 1), (3345838609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_557
    · exact prime_3345838609
  · decide +kernel

theorem prime_3730442411239 : Nat.Prime 3730442411239 := by
  apply nodeValid_prime [2, 3, 223, 2788073551] ⟨3730442411239, 6, [(2, 1), (3, 1), (223, 1), (2788073551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_2788073551
  · decide +kernel

theorem prime_3730442411537 : Nat.Prime 3730442411537 := by
  apply nodeValid_prime [2, 71, 13709, 239539] ⟨3730442411537, 3, [(2, 4), (71, 1), (13709, 1), (239539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_13709
    · exact prime_239539
  · decide +kernel

theorem prime_3730442486443 : Nat.Prime 3730442486443 := by
  apply nodeValid_prime [2, 3, 7, 88820059201] ⟨3730442486443, 2, [(2, 1), (3, 1), (7, 1), (88820059201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_88820059201
  · decide +kernel

end Sude.Lucas.Generated
