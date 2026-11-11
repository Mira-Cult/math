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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1087 : Nat.Prime 1087 := by
  apply nodeValid_prime [2, 3, 181] ⟨1087, 3, [(2, 1), (3, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel

theorem prime_1249 : Nat.Prime 1249 := by
  apply nodeValid_prime [2, 3, 13] ⟨1249, 7, [(2, 5), (3, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_1493 : Nat.Prime 1493 := by
  apply nodeValid_prime [2, 373] ⟨1493, 2, [(2, 2), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_373
  · decide +kernel

theorem prime_1787 : Nat.Prime 1787 := by
  apply nodeValid_prime [2, 19, 47] ⟨1787, 2, [(2, 1), (19, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_2267 : Nat.Prime 2267 := by
  apply nodeValid_prime [2, 11, 103] ⟨2267, 2, [(2, 1), (11, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_103
  · decide +kernel

theorem prime_2609 : Nat.Prime 2609 := by
  apply nodeValid_prime [2, 163] ⟨2609, 3, [(2, 4), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163
  · decide +kernel

theorem prime_2789 : Nat.Prime 2789 := by
  apply nodeValid_prime [2, 17, 41] ⟨2789, 2, [(2, 2), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_3307 : Nat.Prime 3307 := by
  apply nodeValid_prime [2, 3, 19, 29] ⟨3307, 2, [(2, 1), (3, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_3413 : Nat.Prime 3413 := by
  apply nodeValid_prime [2, 853] ⟨3413, 2, [(2, 2), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_853
  · decide +kernel

theorem prime_3671 : Nat.Prime 3671 := by
  apply nodeValid_prime [2, 5, 367] ⟨3671, 13, [(2, 1), (5, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_367
  · decide +kernel

theorem prime_3677 : Nat.Prime 3677 := by
  apply nodeValid_prime [2, 919] ⟨3677, 2, [(2, 2), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_919
  · decide +kernel

theorem prime_4001 : Nat.Prime 4001 := by
  apply nodeValid_prime [2, 5] ⟨4001, 3, [(2, 5), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_5351 : Nat.Prime 5351 := by
  apply nodeValid_prime [2, 5, 107] ⟨5351, 11, [(2, 1), (5, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_5407 : Nat.Prime 5407 := by
  apply nodeValid_prime [2, 3, 17, 53] ⟨5407, 3, [(2, 1), (3, 1), (17, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_53
  · decide +kernel

theorem prime_5591 : Nat.Prime 5591 := by
  apply nodeValid_prime [2, 5, 13, 43] ⟨5591, 11, [(2, 1), (5, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_5801 : Nat.Prime 5801 := by
  apply nodeValid_prime [2, 5, 29] ⟨5801, 3, [(2, 3), (5, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_6113 : Nat.Prime 6113 := by
  apply nodeValid_prime [2, 191] ⟨6113, 3, [(2, 5), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_191
  · decide +kernel

theorem prime_6421 : Nat.Prime 6421 := by
  apply nodeValid_prime [2, 3, 5, 107] ⟨6421, 6, [(2, 2), (3, 1), (5, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_6793 : Nat.Prime 6793 := by
  apply nodeValid_prime [2, 3, 283] ⟨6793, 10, [(2, 3), (3, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
  · decide +kernel

theorem prime_6827 : Nat.Prime 6827 := by
  apply nodeValid_prime [2, 3413] ⟨6827, 2, [(2, 1), (3413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3413
  · decide +kernel

theorem prime_7027 : Nat.Prime 7027 := by
  apply nodeValid_prime [2, 3, 1171] ⟨7027, 2, [(2, 1), (3, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1171
  · decide +kernel

theorem prime_9833 : Nat.Prime 9833 := by
  apply nodeValid_prime [2, 1229] ⟨9833, 3, [(2, 3), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1229
  · decide +kernel

theorem prime_10691 : Nat.Prime 10691 := by
  apply nodeValid_prime [2, 5, 1069] ⟨10691, 2, [(2, 1), (5, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1069
  · decide +kernel

theorem prime_12227 : Nat.Prime 12227 := by
  apply nodeValid_prime [2, 6113] ⟨12227, 2, [(2, 1), (6113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6113
  · decide +kernel

theorem prime_14153 : Nat.Prime 14153 := by
  apply nodeValid_prime [2, 29, 61] ⟨14153, 3, [(2, 3), (29, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_61
  · decide +kernel

theorem prime_14389 : Nat.Prime 14389 := by
  apply nodeValid_prime [2, 3, 11, 109] ⟨14389, 2, [(2, 2), (3, 1), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_14783 : Nat.Prime 14783 := by
  apply nodeValid_prime [2, 19, 389] ⟨14783, 5, [(2, 1), (19, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_389
  · decide +kernel

theorem prime_16253 : Nat.Prime 16253 := by
  apply nodeValid_prime [2, 17, 239] ⟨16253, 2, [(2, 2), (17, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_239
  · decide +kernel

theorem prime_16607 : Nat.Prime 16607 := by
  apply nodeValid_prime [2, 19, 23] ⟨16607, 5, [(2, 1), (19, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_18211 : Nat.Prime 18211 := by
  apply nodeValid_prime [2, 3, 5, 607] ⟨18211, 7, [(2, 1), (3, 1), (5, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_607
  · decide +kernel

theorem prime_18229 : Nat.Prime 18229 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨18229, 2, [(2, 2), (3, 1), (7, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_18427 : Nat.Prime 18427 := by
  apply nodeValid_prime [2, 3, 37, 83] ⟨18427, 2, [(2, 1), (3, 1), (37, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_83
  · decide +kernel

theorem prime_20051 : Nat.Prime 20051 := by
  apply nodeValid_prime [2, 5, 401] ⟨20051, 2, [(2, 1), (5, 2), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_401
  · decide +kernel

theorem prime_20089 : Nat.Prime 20089 := by
  apply nodeValid_prime [2, 3, 31] ⟨20089, 7, [(2, 3), (3, 4), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_20117 : Nat.Prime 20117 := by
  apply nodeValid_prime [2, 47, 107] ⟨20117, 2, [(2, 2), (47, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_107
  · decide +kernel

theorem prime_22003 : Nat.Prime 22003 := by
  apply nodeValid_prime [2, 3, 19, 193] ⟨22003, 2, [(2, 1), (3, 1), (19, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_193
  · decide +kernel

theorem prime_22483 : Nat.Prime 22483 := by
  apply nodeValid_prime [2, 3, 1249] ⟨22483, 2, [(2, 1), (3, 2), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1249
  · decide +kernel

theorem prime_23761 : Nat.Prime 23761 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨23761, 7, [(2, 4), (3, 3), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_26249 : Nat.Prime 26249 := by
  apply nodeValid_prime [2, 17, 193] ⟨26249, 3, [(2, 3), (17, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_193
  · decide +kernel

theorem prime_26423 : Nat.Prime 26423 := by
  apply nodeValid_prime [2, 11, 1201] ⟨26423, 5, [(2, 1), (11, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1201
  · decide +kernel

theorem prime_28759 : Nat.Prime 28759 := by
  apply nodeValid_prime [2, 3, 4793] ⟨28759, 3, [(2, 1), (3, 1), (4793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4793
  · decide +kernel

theorem prime_29723 : Nat.Prime 29723 := by
  apply nodeValid_prime [2, 7, 11, 193] ⟨29723, 2, [(2, 1), (7, 1), (11, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_193
  · decide +kernel

theorem prime_31019 : Nat.Prime 31019 := by
  apply nodeValid_prime [2, 13, 1193] ⟨31019, 2, [(2, 1), (13, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1193
  · decide +kernel

theorem prime_31849 : Nat.Prime 31849 := by
  apply nodeValid_prime [2, 3, 1327] ⟨31849, 14, [(2, 3), (3, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1327
  · decide +kernel

theorem prime_32443 : Nat.Prime 32443 := by
  apply nodeValid_prime [2, 3, 5407] ⟨32443, 2, [(2, 1), (3, 1), (5407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5407
  · decide +kernel

theorem prime_32507 : Nat.Prime 32507 := by
  apply nodeValid_prime [2, 16253] ⟨32507, 2, [(2, 1), (16253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16253
  · decide +kernel

theorem prime_34259 : Nat.Prime 34259 := by
  apply nodeValid_prime [2, 7, 2447] ⟨34259, 2, [(2, 1), (7, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2447
  · decide +kernel

theorem prime_41603 : Nat.Prime 41603 := by
  apply nodeValid_prime [2, 11, 31, 61] ⟨41603, 2, [(2, 1), (11, 1), (31, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_61
  · decide +kernel

theorem prime_71947 : Nat.Prime 71947 := by
  apply nodeValid_prime [2, 3, 7, 571] ⟨71947, 2, [(2, 1), (3, 2), (7, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_571
  · decide +kernel

theorem prime_74297 : Nat.Prime 74297 := by
  apply nodeValid_prime [2, 37, 251] ⟨74297, 3, [(2, 3), (37, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_251
  · decide +kernel

theorem prime_76423 : Nat.Prime 76423 := by
  apply nodeValid_prime [2, 3, 47, 271] ⟨76423, 5, [(2, 1), (3, 1), (47, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_271
  · decide +kernel

theorem prime_87973 : Nat.Prime 87973 := by
  apply nodeValid_prime [2, 3, 7331] ⟨87973, 2, [(2, 2), (3, 1), (7331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7331
  · decide +kernel

theorem prime_98899 : Nat.Prime 98899 := by
  apply nodeValid_prime [2, 3, 53, 311] ⟨98899, 2, [(2, 1), (3, 1), (53, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_311
  · decide +kernel

theorem prime_101363 : Nat.Prime 101363 := by
  apply nodeValid_prime [2, 59, 859] ⟨101363, 2, [(2, 1), (59, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_859
  · decide +kernel

theorem prime_102679 : Nat.Prime 102679 := by
  apply nodeValid_prime [2, 3, 109, 157] ⟨102679, 3, [(2, 1), (3, 1), (109, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_157
  · decide +kernel

theorem prime_110563 : Nat.Prime 110563 := by
  apply nodeValid_prime [2, 3, 18427] ⟨110563, 2, [(2, 1), (3, 1), (18427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18427
  · decide +kernel

theorem prime_115987 : Nat.Prime 115987 := by
  apply nodeValid_prime [2, 3, 13, 1487] ⟨115987, 2, [(2, 1), (3, 1), (13, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1487
  · decide +kernel

theorem prime_132019 : Nat.Prime 132019 := by
  apply nodeValid_prime [2, 3, 22003] ⟨132019, 3, [(2, 1), (3, 1), (22003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22003
  · decide +kernel

theorem prime_132857 : Nat.Prime 132857 := by
  apply nodeValid_prime [2, 16607] ⟨132857, 3, [(2, 3), (16607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16607
  · decide +kernel

theorem prime_142453 : Nat.Prime 142453 := by
  apply nodeValid_prime [2, 3, 1319] ⟨142453, 2, [(2, 2), (3, 3), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1319
  · decide +kernel

theorem prime_149623 : Nat.Prime 149623 := by
  apply nodeValid_prime [2, 3, 11, 2267] ⟨149623, 3, [(2, 1), (3, 1), (11, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2267
  · decide +kernel

theorem prime_171179 : Nat.Prime 171179 := by
  apply nodeValid_prime [2, 7, 12227] ⟨171179, 2, [(2, 1), (7, 1), (12227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12227
  · decide +kernel

theorem prime_178817 : Nat.Prime 178817 := by
  apply nodeValid_prime [2, 11, 127] ⟨178817, 3, [(2, 7), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_195043 : Nat.Prime 195043 := by
  apply nodeValid_prime [2, 3, 32507] ⟨195043, 2, [(2, 1), (3, 1), (32507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32507
  · decide +kernel

theorem prime_294991 : Nat.Prime 294991 := by
  apply nodeValid_prime [2, 3, 5, 9833] ⟨294991, 6, [(2, 1), (3, 1), (5, 1), (9833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9833
  · decide +kernel

theorem prime_300499 : Nat.Prime 300499 := by
  apply nodeValid_prime [2, 3, 11, 29, 157] ⟨300499, 3, [(2, 1), (3, 1), (11, 1), (29, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_157
  · decide +kernel

theorem prime_335957 : Nat.Prime 335957 := by
  apply nodeValid_prime [2, 47, 1787] ⟨335957, 2, [(2, 2), (47, 1), (1787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1787
  · decide +kernel

theorem prime_342359 : Nat.Prime 342359 := by
  apply nodeValid_prime [2, 171179] ⟨342359, 19, [(2, 1), (171179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_171179
  · decide +kernel

theorem prime_360977 : Nat.Prime 360977 := by
  apply nodeValid_prime [2, 7, 11, 293] ⟨360977, 3, [(2, 4), (7, 1), (11, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_293
  · decide +kernel

theorem prime_401039 : Nat.Prime 401039 := by
  apply nodeValid_prime [2, 11, 18229] ⟨401039, 7, [(2, 1), (11, 1), (18229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_18229
  · decide +kernel

theorem prime_434267 : Nat.Prime 434267 := by
  apply nodeValid_prime [2, 7, 31019] ⟨434267, 6, [(2, 1), (7, 1), (31019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31019
  · decide +kernel

theorem prime_571673 : Nat.Prime 571673 := by
  apply nodeValid_prime [2, 19, 3761] ⟨571673, 3, [(2, 3), (19, 1), (3761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3761
  · decide +kernel

theorem prime_616589 : Nat.Prime 616589 := by
  apply nodeValid_prime [2, 7, 19, 61] ⟨616589, 2, [(2, 2), (7, 1), (19, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_678763 : Nat.Prime 678763 := by
  apply nodeValid_prime [2, 3, 7, 5387] ⟨678763, 2, [(2, 1), (3, 2), (7, 1), (5387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5387
  · decide +kernel

theorem prime_791933 : Nat.Prime 791933 := by
  apply nodeValid_prime [2, 29, 6827] ⟨791933, 3, [(2, 2), (29, 1), (6827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_6827
  · decide +kernel

theorem prime_793229 : Nat.Prime 793229 := by
  apply nodeValid_prime [2, 31, 6397] ⟨793229, 2, [(2, 2), (31, 1), (6397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_6397
  · decide +kernel

theorem prime_950737 : Nat.Prime 950737 := by
  apply nodeValid_prime [2, 3, 29, 683] ⟨950737, 5, [(2, 4), (3, 1), (29, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_683
  · decide +kernel

theorem prime_954757 : Nat.Prime 954757 := by
  apply nodeValid_prime [2, 3, 11, 2411] ⟨954757, 2, [(2, 2), (3, 2), (11, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2411
  · decide +kernel

theorem prime_1024433 : Nat.Prime 1024433 := by
  apply nodeValid_prime [2, 43, 1489] ⟨1024433, 3, [(2, 4), (43, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1489
  · decide +kernel

theorem prime_1143347 : Nat.Prime 1143347 := by
  apply nodeValid_prime [2, 571673] ⟨1143347, 2, [(2, 1), (571673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_571673
  · decide +kernel

theorem prime_1193707 : Nat.Prime 1193707 := by
  apply nodeValid_prime [2, 3, 17, 47, 83] ⟨1193707, 2, [(2, 1), (3, 2), (17, 1), (47, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_47
    · exact prime_83
  · decide +kernel

theorem prime_1233179 : Nat.Prime 1233179 := by
  apply nodeValid_prime [2, 616589] ⟨1233179, 2, [(2, 1), (616589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_616589
  · decide +kernel

theorem prime_1358251 : Nat.Prime 1358251 := by
  apply nodeValid_prime [2, 3, 5, 1811] ⟨1358251, 2, [(2, 1), (3, 1), (5, 3), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1811
  · decide +kernel

theorem prime_2048419 : Nat.Prime 2048419 := by
  apply nodeValid_prime [2, 3, 31, 3671] ⟨2048419, 7, [(2, 1), (3, 2), (31, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3671
  · decide +kernel

theorem prime_2056993 : Nat.Prime 2056993 := by
  apply nodeValid_prime [2, 3, 7, 3061] ⟨2056993, 5, [(2, 5), (3, 1), (7, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3061
  · decide +kernel

theorem prime_2156683 : Nat.Prime 2156683 := by
  apply nodeValid_prime [2, 3, 11, 41, 797] ⟨2156683, 11, [(2, 1), (3, 1), (11, 1), (41, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_797
  · decide +kernel

theorem prime_3665377 : Nat.Prime 3665377 := by
  apply nodeValid_prime [2, 3, 11, 13, 89] ⟨3665377, 10, [(2, 5), (3, 2), (11, 1), (13, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_89
  · decide +kernel

theorem prime_4314913 : Nat.Prime 4314913 := by
  apply nodeValid_prime [2, 3, 7, 6421] ⟨4314913, 5, [(2, 5), (3, 1), (7, 1), (6421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6421
  · decide +kernel

theorem prime_4391503 : Nat.Prime 4391503 := by
  apply nodeValid_prime [2, 3, 241, 3037] ⟨4391503, 3, [(2, 1), (3, 1), (241, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_3037
  · decide +kernel

theorem prime_4747153 : Nat.Prime 4747153 := by
  apply nodeValid_prime [2, 3, 98899] ⟨4747153, 10, [(2, 4), (3, 1), (98899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_98899
  · decide +kernel

theorem prime_4774829 : Nat.Prime 4774829 := by
  apply nodeValid_prime [2, 1193707] ⟨4774829, 2, [(2, 2), (1193707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1193707
  · decide +kernel

theorem prime_4776953 : Nat.Prime 4776953 := by
  apply nodeValid_prime [2, 181, 3299] ⟨4776953, 3, [(2, 3), (181, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_3299
  · decide +kernel

theorem prime_4993627 : Nat.Prime 4993627 := by
  apply nodeValid_prime [2, 3, 11, 29, 2609] ⟨4993627, 3, [(2, 1), (3, 1), (11, 1), (29, 1), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_2609
  · decide +kernel

theorem prime_5498401 : Nat.Prime 5498401 := by
  apply nodeValid_prime [2, 3, 5, 29, 79] ⟨5498401, 7, [(2, 5), (3, 1), (5, 2), (29, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_79
  · decide +kernel

theorem prime_5556169 : Nat.Prime 5556169 := by
  apply nodeValid_prime [2, 3, 29, 887] ⟨5556169, 7, [(2, 3), (3, 3), (29, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_887
  · decide +kernel

theorem prime_6512039 : Nat.Prime 6512039 := by
  apply nodeValid_prime [2, 13, 47, 73] ⟨6512039, 7, [(2, 1), (13, 1), (47, 1), (73, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_73
  · decide +kernel

theorem prime_7021549 : Nat.Prime 7021549 := by
  apply nodeValid_prime [2, 3, 195043] ⟨7021549, 2, [(2, 2), (3, 2), (195043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_195043
  · decide +kernel

theorem prime_7074047 : Nat.Prime 7074047 := by
  apply nodeValid_prime [2, 7, 439, 1151] ⟨7074047, 5, [(2, 1), (7, 1), (439, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_439
    · exact prime_1151
  · decide +kernel

theorem prime_7739687 : Nat.Prime 7739687 := by
  apply nodeValid_prime [2, 193, 20051] ⟨7739687, 5, [(2, 1), (193, 1), (20051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_20051
  · decide +kernel

theorem prime_7844567 : Nat.Prime 7844567 := by
  apply nodeValid_prime [2, 733, 5351] ⟨7844567, 5, [(2, 1), (733, 1), (5351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_733
    · exact prime_5351
  · decide +kernel

theorem prime_12218821 : Nat.Prime 12218821 := by
  apply nodeValid_prime [2, 3, 5, 41, 4967] ⟨12218821, 2, [(2, 2), (3, 1), (5, 1), (41, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_4967
  · decide +kernel

theorem prime_12772901 : Nat.Prime 12772901 := by
  apply nodeValid_prime [2, 5, 7, 71, 257] ⟨12772901, 2, [(2, 2), (5, 2), (7, 1), (71, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_257
  · decide +kernel

theorem prime_15884641 : Nat.Prime 15884641 := by
  apply nodeValid_prime [2, 3, 5, 3677] ⟨15884641, 7, [(2, 5), (3, 3), (5, 1), (3677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3677
  · decide +kernel

theorem prime_17114689 : Nat.Prime 17114689 := by
  apply nodeValid_prime [2, 3, 43, 691] ⟨17114689, 13, [(2, 6), (3, 2), (43, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_691
  · decide +kernel

theorem prime_34506929 : Nat.Prime 34506929 := by
  apply nodeValid_prime [2, 2156683] ⟨34506929, 3, [(2, 4), (2156683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2156683
  · decide +kernel

theorem prime_43915031 : Nat.Prime 43915031 := by
  apply nodeValid_prime [2, 5, 4391503] ⟨43915031, 23, [(2, 1), (5, 1), (4391503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4391503
  · decide +kernel

theorem prime_59529863 : Nat.Prime 59529863 := by
  apply nodeValid_prime [2, 7, 733, 5801] ⟨59529863, 5, [(2, 1), (7, 1), (733, 1), (5801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_733
    · exact prime_5801
  · decide +kernel

theorem prime_60230801 : Nat.Prime 60230801 := by
  apply nodeValid_prime [2, 5, 7, 439] ⟨60230801, 6, [(2, 4), (5, 2), (7, 3), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_439
  · decide +kernel

theorem prime_82279721 : Nat.Prime 82279721 := by
  apply nodeValid_prime [2, 5, 2056993] ⟨82279721, 3, [(2, 3), (5, 1), (2056993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2056993
  · decide +kernel

theorem prime_95307847 : Nat.Prime 95307847 := by
  apply nodeValid_prime [2, 3, 15884641] ⟨95307847, 3, [(2, 1), (3, 1), (15884641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15884641
  · decide +kernel

theorem prime_119622673 : Nat.Prime 119622673 := by
  apply nodeValid_prime [2, 3, 13, 63901] ⟨119622673, 10, [(2, 4), (3, 2), (13, 1), (63901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_63901
  · decide +kernel

theorem prime_140363651 : Nat.Prime 140363651 := by
  apply nodeValid_prime [2, 5, 7, 401039] ⟨140363651, 2, [(2, 1), (5, 2), (7, 1), (401039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_401039
  · decide +kernel

theorem prime_170832587 : Nat.Prime 170832587 := by
  apply nodeValid_prime [2, 647, 132019] ⟨170832587, 2, [(2, 1), (647, 1), (132019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_647
    · exact prime_132019
  · decide +kernel

theorem prime_193654567 : Nat.Prime 193654567 := by
  apply nodeValid_prime [2, 3, 7, 89, 2467] ⟨193654567, 3, [(2, 1), (3, 2), (7, 2), (89, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_2467
  · decide +kernel

theorem prime_212221411 : Nat.Prime 212221411 := by
  apply nodeValid_prime [2, 3, 5, 7074047] ⟨212221411, 2, [(2, 1), (3, 1), (5, 1), (7074047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7074047
  · decide +kernel

theorem prime_317621627 : Nat.Prime 317621627 := by
  apply nodeValid_prime [2, 7, 229, 14153] ⟨317621627, 5, [(2, 1), (7, 2), (229, 1), (14153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_229
    · exact prime_14153
  · decide +kernel

theorem prime_353822867 : Nat.Prime 353822867 := by
  apply nodeValid_prime [2, 41, 4314913] ⟨353822867, 2, [(2, 1), (41, 1), (4314913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_4314913
  · decide +kernel

theorem prime_355594817 : Nat.Prime 355594817 := by
  apply nodeValid_prime [2, 5556169] ⟨355594817, 3, [(2, 6), (5556169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5556169
  · decide +kernel

theorem prime_428265029 : Nat.Prime 428265029 := by
  apply nodeValid_prime [2, 113, 919, 1031] ⟨428265029, 2, [(2, 2), (113, 1), (919, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_919
    · exact prime_1031
  · decide +kernel

theorem prime_486034993 : Nat.Prime 486034993 := by
  apply nodeValid_prime [2, 3, 41, 3049] ⟨486034993, 5, [(2, 4), (3, 5), (41, 1), (3049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_3049
  · decide +kernel

theorem prime_496844401 : Nat.Prime 496844401 := by
  apply nodeValid_prime [2, 3, 5, 13, 31849] ⟨496844401, 23, [(2, 4), (3, 1), (5, 2), (13, 1), (31849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_31849
  · decide +kernel

theorem prime_619943377 : Nat.Prime 619943377 := by
  apply nodeValid_prime [2, 3, 13, 76423] ⟨619943377, 5, [(2, 4), (3, 1), (13, 2), (76423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_76423
  · decide +kernel

theorem prime_643758851 : Nat.Prime 643758851 := by
  apply nodeValid_prime [2, 5, 7, 101, 18211] ⟨643758851, 2, [(2, 1), (5, 2), (7, 1), (101, 1), (18211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_101
    · exact prime_18211
  · decide +kernel

theorem prime_913555913 : Nat.Prime 913555913 := by
  apply nodeValid_prime [2, 29, 53, 74297] ⟨913555913, 3, [(2, 3), (29, 1), (53, 1), (74297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_53
    · exact prime_74297
  · decide +kernel

theorem prime_929243261 : Nat.Prime 929243261 := by
  apply nodeValid_prime [2, 5, 11, 19, 131, 1697] ⟨929243261, 2, [(2, 2), (5, 1), (11, 1), (19, 1), (131, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_131
    · exact prime_1697
  · decide +kernel

theorem prime_1256418703 : Nat.Prime 1256418703 := by
  apply nodeValid_prime [2, 3, 7, 11, 14389] ⟨1256418703, 6, [(2, 1), (3, 4), (7, 2), (11, 1), (14389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_14389
  · decide +kernel

theorem prime_1287517703 : Nat.Prime 1287517703 := by
  apply nodeValid_prime [2, 643758851] ⟨1287517703, 5, [(2, 1), (643758851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_643758851
  · decide +kernel

theorem prime_1440128749 : Nat.Prime 1440128749 := by
  apply nodeValid_prime [2, 3, 29, 61, 179, 379] ⟨1440128749, 2, [(2, 2), (3, 1), (29, 1), (61, 1), (179, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_61
    · exact prime_179
    · exact prime_379
  · decide +kernel

theorem prime_1508798927 : Nat.Prime 1508798927 := by
  apply nodeValid_prime [2, 17, 1493, 29723] ⟨1508798927, 5, [(2, 1), (17, 1), (1493, 1), (29723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1493
    · exact prime_29723
  · decide +kernel

theorem prime_1756731689 : Nat.Prime 1756731689 := by
  apply nodeValid_prime [2, 9767, 22483] ⟨1756731689, 3, [(2, 3), (9767, 1), (22483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9767
    · exact prime_22483
  · decide +kernel

theorem prime_3513463379 : Nat.Prime 3513463379 := by
  apply nodeValid_prime [2, 1756731689] ⟨3513463379, 2, [(2, 1), (1756731689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1756731689
  · decide +kernel

theorem prime_9720579839 : Nat.Prime 9720579839 := by
  apply nodeValid_prime [2, 17, 23, 37, 335957] ⟨9720579839, 11, [(2, 1), (17, 1), (23, 1), (37, 1), (335957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_37
    · exact prime_335957
  · decide +kernel

theorem prime_13461627617 : Nat.Prime 13461627617 := by
  apply nodeValid_prime [2, 17, 241, 102679] ⟨13461627617, 3, [(2, 5), (17, 1), (241, 1), (102679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_241
    · exact prime_102679
  · decide +kernel

theorem prime_13733757743 : Nat.Prime 13733757743 := by
  apply nodeValid_prime [2, 199, 34506929] ⟨13733757743, 5, [(2, 1), (199, 1), (34506929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_34506929
  · decide +kernel

theorem prime_16165208953 : Nat.Prime 16165208953 := by
  apply nodeValid_prime [2, 3, 47, 4776953] ⟨16165208953, 5, [(2, 3), (3, 2), (47, 1), (4776953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_4776953
  · decide +kernel

theorem prime_16525189763 : Nat.Prime 16525189763 := by
  apply nodeValid_prime [2, 17, 486034993] ⟨16525189763, 5, [(2, 1), (17, 1), (486034993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_486034993
  · decide +kernel

theorem prime_19312626313 : Nat.Prime 19312626313 := by
  apply nodeValid_prime [2, 3, 7, 12772901] ⟨19312626313, 5, [(2, 3), (3, 3), (7, 1), (12772901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12772901
  · decide +kernel

theorem prime_19441159609 : Nat.Prime 19441159609 := by
  apply nodeValid_prime [2, 3, 13, 17, 3665377] ⟨19441159609, 19, [(2, 3), (3, 1), (13, 1), (17, 1), (3665377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_3665377
  · decide +kernel

theorem prime_31903584397 : Nat.Prime 31903584397 := by
  apply nodeValid_prime [2, 3, 47, 643, 87973] ⟨31903584397, 7, [(2, 2), (3, 1), (47, 1), (643, 1), (87973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_643
    · exact prime_87973
  · decide +kernel

theorem prime_48817921609 : Nat.Prime 48817921609 := by
  apply nodeValid_prime [2, 3, 331, 2048419] ⟨48817921609, 17, [(2, 3), (3, 2), (331, 1), (2048419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
    · exact prime_2048419
  · decide +kernel

theorem prime_49033584043 : Nat.Prime 49033584043 := by
  apply nodeValid_prime [2, 3, 103, 163, 677, 719] ⟨49033584043, 2, [(2, 1), (3, 1), (103, 1), (163, 1), (677, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_163
    · exact prime_677
    · exact prime_719
  · decide +kernel

theorem prime_188462786609 : Nat.Prime 188462786609 := by
  apply nodeValid_prime [2, 19, 619943377] ⟨188462786609, 3, [(2, 4), (19, 1), (619943377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_619943377
  · decide +kernel

theorem prime_188462786639 : Nat.Prime 188462786639 := by
  apply nodeValid_prime [2, 7, 13461627617] ⟨188462786639, 7, [(2, 1), (7, 1), (13461627617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13461627617
  · decide +kernel

theorem prime_188462805451 : Nat.Prime 188462805451 := by
  apply nodeValid_prime [2, 3, 5, 1256418703] ⟨188462805451, 3, [(2, 1), (3, 1), (5, 2), (1256418703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1256418703
  · decide +kernel

theorem prime_188883561073 : Nat.Prime 188883561073 := by
  apply nodeValid_prime [2, 3, 3191, 1233179] ⟨188883561073, 5, [(2, 4), (3, 1), (3191, 1), (1233179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3191
    · exact prime_1233179
  · decide +kernel

theorem prime_188883563117 : Nat.Prime 188883563117 := by
  apply nodeValid_prime [2, 19, 59, 97, 434267] ⟨188883563117, 2, [(2, 2), (19, 1), (59, 1), (97, 1), (434267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59
    · exact prime_97
    · exact prime_434267
  · decide +kernel

theorem prime_188883567577 : Nat.Prime 188883567577 := by
  apply nodeValid_prime [2, 3, 11, 419, 7027] ⟨188883567577, 5, [(2, 3), (3, 6), (11, 1), (419, 1), (7027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_419
    · exact prime_7027
  · decide +kernel

theorem prime_189304964341 : Nat.Prime 189304964341 := by
  apply nodeValid_prime [2, 3, 5, 53, 59529863] ⟨189304964341, 2, [(2, 2), (3, 1), (5, 1), (53, 1), (59529863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_59529863
  · decide +kernel

theorem prime_189304973731 : Nat.Prime 189304973731 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 6512039] ⟨189304973731, 14, [(2, 1), (3, 2), (5, 1), (17, 1), (19, 1), (6512039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_6512039
  · decide +kernel

theorem prime_189304974071 : Nat.Prime 189304974071 := by
  apply nodeValid_prime [2, 5, 17, 1087, 1024433] ⟨189304974071, 13, [(2, 1), (5, 1), (17, 1), (1087, 1), (1024433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1087
    · exact prime_1024433
  · decide +kernel

theorem prime_189727001543 : Nat.Prime 189727001543 := by
  apply nodeValid_prime [2, 13, 29, 853, 294991] ⟨189727001543, 5, [(2, 1), (13, 1), (29, 1), (853, 1), (294991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_853
    · exact prime_294991
  · decide +kernel

theorem prime_189727022467 : Nat.Prime 189727022467 := by
  apply nodeValid_prime [2, 3, 3513463379] ⟨189727022467, 2, [(2, 1), (3, 3), (3513463379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3513463379
  · decide +kernel

theorem prime_189727023151 : Nat.Prime 189727023151 := by
  apply nodeValid_prime [2, 3, 5, 7, 60230801] ⟨189727023151, 6, [(2, 1), (3, 2), (5, 2), (7, 1), (60230801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_60230801
  · decide +kernel

theorem prime_190149672877 : Nat.Prime 190149672877 := by
  apply nodeValid_prime [2, 3, 37, 428265029] ⟨190149672877, 5, [(2, 2), (3, 1), (37, 1), (428265029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_428265029
  · decide +kernel

theorem prime_190149706193 : Nat.Prime 190149706193 := by
  apply nodeValid_prime [2, 41, 1621, 178817] ⟨190149706193, 3, [(2, 4), (41, 1), (1621, 1), (178817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1621
    · exact prime_178817
  · decide +kernel

theorem prime_190149706997 : Nat.Prime 190149706997 := by
  apply nodeValid_prime [2, 31, 1129, 1358251] ⟨190149706997, 2, [(2, 2), (31, 1), (1129, 1), (1358251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1129
    · exact prime_1358251
  · decide +kernel

theorem prime_190572975049 : Nat.Prime 190572975049 := by
  apply nodeValid_prime [2, 3, 1663, 4774829] ⟨190572975049, 19, [(2, 3), (3, 1), (1663, 1), (4774829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1663
    · exact prime_4774829
  · decide +kernel

theorem prime_190572976201 : Nat.Prime 190572976201 := by
  apply nodeValid_prime [2, 3, 5, 317621627] ⟨190572976201, 14, [(2, 3), (3, 1), (5, 2), (317621627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_317621627
  · decide +kernel

theorem prime_190572980971 : Nat.Prime 190572980971 := by
  apply nodeValid_prime [2, 3, 5, 43, 5591, 26423] ⟨190572980971, 7, [(2, 1), (3, 1), (5, 1), (43, 1), (5591, 1), (26423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_5591
    · exact prime_26423
  · decide +kernel

theorem prime_190996925389 : Nat.Prime 190996925389 := by
  apply nodeValid_prime [2, 3, 167, 95307847] ⟨190996925389, 6, [(2, 2), (3, 1), (167, 1), (95307847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_95307847
  · decide +kernel

theorem prime_190996952771 : Nat.Prime 190996952771 := by
  apply nodeValid_prime [2, 5, 13, 53, 239, 115987] ⟨190996952771, 2, [(2, 1), (5, 1), (13, 1), (53, 1), (239, 1), (115987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_53
    · exact prime_239
    · exact prime_115987
  · decide +kernel

theorem prime_190996953803 : Nat.Prime 190996953803 := by
  apply nodeValid_prime [2, 20117, 4747153] ⟨190996953803, 2, [(2, 1), (20117, 1), (4747153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_20117
    · exact prime_4747153
  · decide +kernel

theorem prime_191421468839 : Nat.Prime 191421468839 := by
  apply nodeValid_prime [2, 43, 317, 7021549] ⟨191421468839, 17, [(2, 1), (43, 1), (317, 1), (7021549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_317
    · exact prime_7021549
  · decide +kernel

theorem prime_191421468989 : Nat.Prime 191421468989 := by
  apply nodeValid_prime [2, 71, 2243, 300499] ⟨191421468989, 2, [(2, 2), (71, 1), (2243, 1), (300499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2243
    · exact prime_300499
  · decide +kernel

theorem prime_191421506383 : Nat.Prime 191421506383 := by
  apply nodeValid_prime [2, 3, 31903584397] ⟨191421506383, 3, [(2, 1), (3, 1), (31903584397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31903584397
  · decide +kernel

theorem prime_191846730553 : Nat.Prime 191846730553 := by
  apply nodeValid_prime [2, 3, 1019, 7844567] ⟨191846730553, 5, [(2, 3), (3, 1), (1019, 1), (7844567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1019
    · exact prime_7844567
  · decide +kernel

theorem prime_191846741699 : Nat.Prime 191846741699 := by
  apply nodeValid_prime [2, 1009, 4001, 23761] ⟨191846741699, 2, [(2, 1), (1009, 1), (4001, 1), (23761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1009
    · exact prime_4001
    · exact prime_23761
  · decide +kernel

theorem prime_191846741731 : Nat.Prime 191846741731 := by
  apply nodeValid_prime [2, 3, 5, 7, 913555913] ⟨191846741731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (913555913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_913555913
  · decide +kernel

theorem prime_192272598367 : Nat.Prime 192272598367 := by
  apply nodeValid_prime [2, 3, 151, 212221411] ⟨192272598367, 3, [(2, 1), (3, 1), (151, 1), (212221411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_212221411
  · decide +kernel

theorem prime_192272608351 : Nat.Prime 192272608351 := by
  apply nodeValid_prime [2, 3, 5, 83, 179, 28759] ⟨192272608351, 3, [(2, 1), (3, 2), (5, 2), (83, 1), (179, 1), (28759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_179
    · exact prime_28759
  · decide +kernel

theorem prime_192272608403 : Nat.Prime 192272608403 := by
  apply nodeValid_prime [2, 7, 13733757743] ⟨192272608403, 2, [(2, 1), (7, 1), (13733757743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13733757743
  · decide +kernel

theorem prime_192699106583 : Nat.Prime 192699106583 := by
  apply nodeValid_prime [2, 1171, 82279721] ⟨192699106583, 5, [(2, 1), (1171, 1), (82279721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1171
    · exact prime_82279721
  · decide +kernel

theorem prime_192699156029 : Nat.Prime 192699156029 := by
  apply nodeValid_prime [2, 1097, 43915031] ⟨192699156029, 2, [(2, 2), (1097, 1), (43915031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1097
    · exact prime_43915031
  · decide +kernel

theorem prime_192699158137 : Nat.Prime 192699158137 := by
  apply nodeValid_prime [2, 3, 47, 170832587] ⟨192699158137, 11, [(2, 3), (3, 1), (47, 1), (170832587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_170832587
  · decide +kernel

theorem prime_193126262657 : Nat.Prime 193126262657 := by
  apply nodeValid_prime [2, 1508798927] ⟨193126262657, 3, [(2, 7), (1508798927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1508798927
  · decide +kernel

theorem prime_193126263131 : Nat.Prime 193126263131 := by
  apply nodeValid_prime [2, 5, 19312626313] ⟨193126263131, 2, [(2, 1), (5, 1), (19312626313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19312626313
  · decide +kernel

theorem prime_193126265201 : Nat.Prime 193126265201 := by
  apply nodeValid_prime [2, 5, 11, 157, 263, 1063] ⟨193126265201, 3, [(2, 4), (5, 2), (11, 1), (157, 1), (263, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_157
    · exact prime_263
    · exact prime_1063
  · decide +kernel

theorem prime_193554067583 : Nat.Prime 193554067583 := by
  apply nodeValid_prime [2, 101363, 954757] ⟨193554067583, 5, [(2, 1), (101363, 1), (954757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101363
    · exact prime_954757
  · decide +kernel

theorem prime_193554092497 : Nat.Prime 193554092497 := by
  apply nodeValid_prime [2, 3, 521, 7739687] ⟨193554092497, 7, [(2, 4), (3, 1), (521, 1), (7739687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_7739687
  · decide +kernel

theorem prime_193554094483 : Nat.Prime 193554094483 := by
  apply nodeValid_prime [2, 3, 7, 5261, 32443] ⟨193554094483, 2, [(2, 1), (3, 4), (7, 1), (5261, 1), (32443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5261
    · exact prime_32443
  · decide +kernel

theorem prime_193982507437 : Nat.Prime 193982507437 := by
  apply nodeValid_prime [2, 3, 16165208953] ⟨193982507437, 2, [(2, 2), (3, 1), (16165208953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16165208953
  · decide +kernel

theorem prime_193982565493 : Nat.Prime 193982565493 := by
  apply nodeValid_prime [2, 3, 6793, 793229] ⟨193982565493, 2, [(2, 2), (3, 2), (6793, 1), (793229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6793
    · exact prime_793229
  · decide +kernel

theorem prime_193982565683 : Nat.Prime 193982565683 := by
  apply nodeValid_prime [2, 691, 140363651] ⟨193982565683, 2, [(2, 1), (691, 1), (140363651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_691
    · exact prime_140363651
  · decide +kernel

theorem prime_194411592127 : Nat.Prime 194411592127 := by
  apply nodeValid_prime [2, 3, 127, 199, 142453] ⟨194411592127, 3, [(2, 1), (3, 3), (127, 1), (199, 1), (142453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_199
    · exact prime_142453
  · decide +kernel

theorem prime_194411596091 : Nat.Prime 194411596091 := by
  apply nodeValid_prime [2, 5, 19441159609] ⟨194411596091, 2, [(2, 1), (5, 1), (19441159609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19441159609
  · decide +kernel

theorem prime_194411596781 : Nat.Prime 194411596781 := by
  apply nodeValid_prime [2, 5, 9720579839] ⟨194411596781, 2, [(2, 2), (5, 1), (9720579839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9720579839
  · decide +kernel

theorem prime_194841319667 : Nat.Prime 194841319667 := by
  apply nodeValid_prime [2, 7, 17, 67, 12218821] ⟨194841319667, 2, [(2, 1), (7, 1), (17, 1), (67, 1), (12218821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_67
    · exact prime_12218821
  · decide +kernel

theorem prime_194841337837 : Nat.Prime 194841337837 := by
  apply nodeValid_prime [2, 3, 2953, 5498401] ⟨194841337837, 2, [(2, 2), (3, 1), (2953, 1), (5498401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2953
    · exact prime_5498401
  · decide +kernel

theorem prime_194841338287 : Nat.Prime 194841338287 := by
  apply nodeValid_prime [2, 3, 7, 929, 4993627] ⟨194841338287, 3, [(2, 1), (3, 1), (7, 1), (929, 1), (4993627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_929
    · exact prime_4993627
  · decide +kernel

theorem prime_195271670933 : Nat.Prime 195271670933 := by
  apply nodeValid_prime [2, 13, 197, 1783, 10691] ⟨195271670933, 2, [(2, 2), (13, 1), (197, 1), (1783, 1), (10691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_197
    · exact prime_1783
    · exact prime_10691
  · decide +kernel

theorem prime_195271671409 : Nat.Prime 195271671409 := by
  apply nodeValid_prime [2, 3, 11, 467, 791933] ⟨195271671409, 14, [(2, 4), (3, 1), (11, 1), (467, 1), (791933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_467
    · exact prime_791933
  · decide +kernel

theorem prime_195271686437 : Nat.Prime 195271686437 := by
  apply nodeValid_prime [2, 48817921609] ⟨195271686437, 2, [(2, 2), (48817921609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48817921609
  · decide +kernel

theorem prime_195702690857 : Nat.Prime 195702690857 := by
  apply nodeValid_prime [2, 19, 1287517703] ⟨195702690857, 3, [(2, 3), (19, 1), (1287517703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1287517703
  · decide +kernel

theorem prime_195702691439 : Nat.Prime 195702691439 := by
  apply nodeValid_prime [2, 227, 18947, 22751] ⟨195702691439, 13, [(2, 1), (227, 1), (18947, 1), (22751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_18947
    · exact prime_22751
  · decide +kernel

theorem prime_195702693029 : Nat.Prime 195702693029 := by
  apply nodeValid_prime [2, 409, 119622673] ⟨195702693029, 2, [(2, 2), (409, 1), (119622673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_119622673
  · decide +kernel

theorem prime_196134335941 : Nat.Prime 196134335941 := by
  apply nodeValid_prime [2, 3, 5, 191, 17114689] ⟨196134335941, 2, [(2, 2), (3, 1), (5, 1), (191, 1), (17114689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
    · exact prime_17114689
  · decide +kernel

theorem prime_196134336173 : Nat.Prime 196134336173 := by
  apply nodeValid_prime [2, 49033584043] ⟨196134336173, 2, [(2, 2), (49033584043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49033584043
  · decide +kernel

theorem prime_196134339481 : Nat.Prime 196134339481 := by
  apply nodeValid_prime [2, 3, 5, 14783, 110563] ⟨196134339481, 35, [(2, 3), (3, 1), (5, 1), (14783, 1), (110563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14783
    · exact prime_110563
  · decide +kernel

theorem prime_196566633853 : Nat.Prime 196566633853 := by
  apply nodeValid_prime [2, 3, 19, 29, 67, 577, 769] ⟨196566633853, 2, [(2, 2), (3, 1), (19, 1), (29, 1), (67, 1), (577, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_67
    · exact prime_577
    · exact prime_769
  · decide +kernel

theorem prime_196566686461 : Nat.Prime 196566686461 := by
  apply nodeValid_prime [2, 3, 5, 26249, 41603] ⟨196566686461, 2, [(2, 2), (3, 2), (5, 1), (26249, 1), (41603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_26249
    · exact prime_41603
  · decide +kernel

theorem prime_196566686489 : Nat.Prime 196566686489 := by
  apply nodeValid_prime [2, 17, 20089, 71947] ⟨196566686489, 3, [(2, 3), (17, 1), (20089, 1), (71947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_20089
    · exact prime_71947
  · decide +kernel

theorem prime_196999528619 : Nat.Prime 196999528619 := by
  apply nodeValid_prime [2, 277, 355594817] ⟨196999528619, 2, [(2, 1), (277, 1), (355594817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_355594817
  · decide +kernel

theorem prime_196999531063 : Nat.Prime 196999531063 := by
  apply nodeValid_prime [2, 3, 29, 3307, 342359] ⟨196999531063, 3, [(2, 1), (3, 1), (29, 1), (3307, 1), (342359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_3307
    · exact prime_342359
  · decide +kernel

theorem prime_196999571333 : Nat.Prime 196999571333 := by
  apply nodeValid_prime [2, 53, 929243261] ⟨196999571333, 2, [(2, 2), (53, 1), (929243261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_929243261
  · decide +kernel

theorem prime_197433151337 : Nat.Prime 197433151337 := by
  apply nodeValid_prime [2, 103, 353, 678763] ⟨197433151337, 3, [(2, 3), (103, 1), (353, 1), (678763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_353
    · exact prime_678763
  · decide +kernel

theorem prime_197433159787 : Nat.Prime 197433159787 := by
  apply nodeValid_prime [2, 3, 31, 353822867] ⟨197433159787, 2, [(2, 1), (3, 2), (31, 1), (353822867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_353822867
  · decide +kernel

theorem prime_197433159961 : Nat.Prime 197433159961 := by
  apply nodeValid_prime [2, 3, 5, 1439, 1143347] ⟨197433159961, 17, [(2, 3), (3, 1), (5, 1), (1439, 1), (1143347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1439
    · exact prime_1143347
  · decide +kernel

theorem prime_197867376689 : Nat.Prime 197867376689 := by
  apply nodeValid_prime [2, 34259, 360977] ⟨197867376689, 3, [(2, 4), (34259, 1), (360977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_34259
    · exact prime_360977
  · decide +kernel

theorem prime_197867384383 : Nat.Prime 197867384383 := by
  apply nodeValid_prime [2, 3, 89, 2789, 132857] ⟨197867384383, 3, [(2, 1), (3, 1), (89, 1), (2789, 1), (132857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_2789
    · exact prime_132857
  · decide +kernel

theorem prime_197867384441 : Nat.Prime 197867384441 := by
  apply nodeValid_prime [2, 5, 11, 43, 950737] ⟨197867384441, 15, [(2, 3), (5, 1), (11, 2), (43, 1), (950737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_950737
  · decide +kernel

theorem prime_198302244559 : Nat.Prime 198302244559 := by
  apply nodeValid_prime [2, 3, 11, 43, 467, 149623] ⟨198302244559, 6, [(2, 1), (3, 1), (11, 1), (43, 1), (467, 1), (149623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_467
    · exact prime_149623
  · decide +kernel

theorem prime_198302276609 : Nat.Prime 198302276609 := by
  apply nodeValid_prime [2, 193654567] ⟨198302276609, 3, [(2, 10), (193654567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193654567
  · decide +kernel

theorem prime_198302277157 : Nat.Prime 198302277157 := by
  apply nodeValid_prime [2, 3, 16525189763] ⟨198302277157, 6, [(2, 2), (3, 1), (16525189763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16525189763
  · decide +kernel

theorem prime_198737760401 : Nat.Prime 198737760401 := by
  apply nodeValid_prime [2, 5, 496844401] ⟨198737760401, 3, [(2, 4), (5, 2), (496844401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_496844401
  · decide +kernel

theorem prime_198737766791 : Nat.Prime 198737766791 := by
  apply nodeValid_prime [2, 5, 17, 43, 227, 229, 523] ⟨198737766791, 13, [(2, 1), (5, 1), (17, 1), (43, 1), (227, 1), (229, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_43
    · exact prime_227
    · exact prime_229
    · exact prime_523
  · decide +kernel

theorem prime_198737767363 : Nat.Prime 198737767363 := by
  apply nodeValid_prime [2, 3, 23, 1440128749] ⟨198737767363, 3, [(2, 1), (3, 1), (23, 1), (1440128749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1440128749
  · decide +kernel

end Sude.Lucas.Generated
