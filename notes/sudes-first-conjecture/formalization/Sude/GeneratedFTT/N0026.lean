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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2659 : Nat.Prime 2659 := by
  apply nodeValid_prime [2, 3, 443] ⟨2659, 2, [(2, 1), (3, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_443
  · decide +kernel

theorem prime_3853 : Nat.Prime 3853 := by
  apply nodeValid_prime [2, 3, 107] ⟨3853, 2, [(2, 2), (3, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
  · decide +kernel

theorem prime_6263 : Nat.Prime 6263 := by
  apply nodeValid_prime [2, 31, 101] ⟨6263, 5, [(2, 1), (31, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_101
  · decide +kernel

theorem prime_6301 : Nat.Prime 6301 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨6301, 10, [(2, 2), (3, 2), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_6343 : Nat.Prime 6343 := by
  apply nodeValid_prime [2, 3, 7, 151] ⟨6343, 3, [(2, 1), (3, 1), (7, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
  · decide +kernel

theorem prime_6481 : Nat.Prime 6481 := by
  apply nodeValid_prime [2, 3, 5] ⟨6481, 7, [(2, 4), (3, 4), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_6673 : Nat.Prime 6673 := by
  apply nodeValid_prime [2, 3, 139] ⟨6673, 5, [(2, 4), (3, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_7211 : Nat.Prime 7211 := by
  apply nodeValid_prime [2, 5, 7, 103] ⟨7211, 2, [(2, 1), (5, 1), (7, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_7691 : Nat.Prime 7691 := by
  apply nodeValid_prime [2, 5, 769] ⟨7691, 2, [(2, 1), (5, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_769
  · decide +kernel

theorem prime_8117 : Nat.Prime 8117 := by
  apply nodeValid_prime [2, 2029] ⟨8117, 2, [(2, 2), (2029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2029
  · decide +kernel

theorem prime_8123 : Nat.Prime 8123 := by
  apply nodeValid_prime [2, 31, 131] ⟨8123, 2, [(2, 1), (31, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_131
  · decide +kernel

theorem prime_9109 : Nat.Prime 9109 := by
  apply nodeValid_prime [2, 3, 11, 23] ⟨9109, 10, [(2, 2), (3, 2), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_9293 : Nat.Prime 9293 := by
  apply nodeValid_prime [2, 23, 101] ⟨9293, 2, [(2, 2), (23, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_101
  · decide +kernel

theorem prime_9467 : Nat.Prime 9467 := by
  apply nodeValid_prime [2, 4733] ⟨9467, 2, [(2, 1), (4733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4733
  · decide +kernel

theorem prime_10459 : Nat.Prime 10459 := by
  apply nodeValid_prime [2, 3, 7, 83] ⟨10459, 2, [(2, 1), (3, 2), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_10631 : Nat.Prime 10631 := by
  apply nodeValid_prime [2, 5, 1063] ⟨10631, 11, [(2, 1), (5, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1063
  · decide +kernel

theorem prime_10723 : Nat.Prime 10723 := by
  apply nodeValid_prime [2, 3, 1787] ⟨10723, 2, [(2, 1), (3, 1), (1787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1787
  · decide +kernel

theorem prime_11677 : Nat.Prime 11677 := by
  apply nodeValid_prime [2, 3, 7, 139] ⟨11677, 2, [(2, 2), (3, 1), (7, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_13127 : Nat.Prime 13127 := by
  apply nodeValid_prime [2, 6563] ⟨13127, 5, [(2, 1), (6563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6563
  · decide +kernel

theorem prime_13147 : Nat.Prime 13147 := by
  apply nodeValid_prime [2, 3, 7, 313] ⟨13147, 2, [(2, 1), (3, 1), (7, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_313
  · decide +kernel

theorem prime_13241 : Nat.Prime 13241 := by
  apply nodeValid_prime [2, 5, 331] ⟨13241, 3, [(2, 3), (5, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_331
  · decide +kernel

theorem prime_14249 : Nat.Prime 14249 := by
  apply nodeValid_prime [2, 13, 137] ⟨14249, 3, [(2, 3), (13, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_137
  · decide +kernel

theorem prime_16339 : Nat.Prime 16339 := by
  apply nodeValid_prime [2, 3, 7, 389] ⟨16339, 2, [(2, 1), (3, 1), (7, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_389
  · decide +kernel

theorem prime_16481 : Nat.Prime 16481 := by
  apply nodeValid_prime [2, 5, 103] ⟨16481, 6, [(2, 5), (5, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_19267 : Nat.Prime 19267 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨19267, 3, [(2, 1), (3, 1), (13, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_19387 : Nat.Prime 19387 := by
  apply nodeValid_prime [2, 3, 359] ⟨19387, 2, [(2, 1), (3, 3), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
  · decide +kernel

theorem prime_23053 : Nat.Prime 23053 := by
  apply nodeValid_prime [2, 3, 17, 113] ⟨23053, 2, [(2, 2), (3, 1), (17, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_113
  · decide +kernel

theorem prime_23297 : Nat.Prime 23297 := by
  apply nodeValid_prime [2, 7, 13] ⟨23297, 3, [(2, 8), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_26693 : Nat.Prime 26693 := by
  apply nodeValid_prime [2, 6673] ⟨26693, 2, [(2, 2), (6673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6673
  · decide +kernel

theorem prime_29027 : Nat.Prime 29027 := by
  apply nodeValid_prime [2, 23, 631] ⟨29027, 2, [(2, 1), (23, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_631
  · decide +kernel

theorem prime_29473 : Nat.Prime 29473 := by
  apply nodeValid_prime [2, 3, 307] ⟨29473, 5, [(2, 5), (3, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
  · decide +kernel

theorem prime_34141 : Nat.Prime 34141 := by
  apply nodeValid_prime [2, 3, 5, 569] ⟨34141, 2, [(2, 2), (3, 1), (5, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_569
  · decide +kernel

theorem prime_39103 : Nat.Prime 39103 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨39103, 5, [(2, 1), (3, 1), (7, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_42901 : Nat.Prime 42901 := by
  apply nodeValid_prime [2, 3, 5, 11, 13] ⟨42901, 6, [(2, 2), (3, 1), (5, 2), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_47293 : Nat.Prime 47293 := by
  apply nodeValid_prime [2, 3, 7, 563] ⟨47293, 6, [(2, 2), (3, 1), (7, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_563
  · decide +kernel

theorem prime_58511 : Nat.Prime 58511 := by
  apply nodeValid_prime [2, 5, 5851] ⟨58511, 13, [(2, 1), (5, 1), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5851
  · decide +kernel

theorem prime_61297 : Nat.Prime 61297 := by
  apply nodeValid_prime [2, 3, 1277] ⟨61297, 7, [(2, 4), (3, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1277
  · decide +kernel

theorem prime_64237 : Nat.Prime 64237 := by
  apply nodeValid_prime [2, 3, 53, 101] ⟨64237, 2, [(2, 2), (3, 1), (53, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_101
  · decide +kernel

theorem prime_64811 : Nat.Prime 64811 := by
  apply nodeValid_prime [2, 5, 6481] ⟨64811, 2, [(2, 1), (5, 1), (6481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6481
  · decide +kernel

theorem prime_85369 : Nat.Prime 85369 := by
  apply nodeValid_prime [2, 3, 3557] ⟨85369, 17, [(2, 3), (3, 1), (3557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3557
  · decide +kernel

theorem prime_98017 : Nat.Prime 98017 := by
  apply nodeValid_prime [2, 3, 1021] ⟨98017, 7, [(2, 5), (3, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
  · decide +kernel

theorem prime_103801 : Nat.Prime 103801 := by
  apply nodeValid_prime [2, 3, 5, 173] ⟨103801, 14, [(2, 3), (3, 1), (5, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_120817 : Nat.Prime 120817 := by
  apply nodeValid_prime [2, 3, 839] ⟨120817, 10, [(2, 4), (3, 2), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_839
  · decide +kernel

theorem prime_125539 : Nat.Prime 125539 := by
  apply nodeValid_prime [2, 3, 7, 61] ⟨125539, 3, [(2, 1), (3, 1), (7, 3), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_128449 : Nat.Prime 128449 := by
  apply nodeValid_prime [2, 3, 223] ⟨128449, 11, [(2, 6), (3, 2), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
  · decide +kernel

theorem prime_135719 : Nat.Prime 135719 := by
  apply nodeValid_prime [2, 11, 31, 199] ⟨135719, 31, [(2, 1), (11, 1), (31, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_199
  · decide +kernel

theorem prime_143609 : Nat.Prime 143609 := by
  apply nodeValid_prime [2, 29, 619] ⟨143609, 3, [(2, 3), (29, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_619
  · decide +kernel

theorem prime_143719 : Nat.Prime 143719 := by
  apply nodeValid_prime [2, 3, 17, 1409] ⟨143719, 6, [(2, 1), (3, 1), (17, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1409
  · decide +kernel

theorem prime_158243 : Nat.Prime 158243 := by
  apply nodeValid_prime [2, 7, 89, 127] ⟨158243, 2, [(2, 1), (7, 1), (89, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_127
  · decide +kernel

theorem prime_169313 : Nat.Prime 169313 := by
  apply nodeValid_prime [2, 11, 13, 37] ⟨169313, 3, [(2, 5), (11, 1), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_217121 : Nat.Prime 217121 := by
  apply nodeValid_prime [2, 5, 23, 59] ⟨217121, 3, [(2, 5), (5, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_223049 : Nat.Prime 223049 := by
  apply nodeValid_prime [2, 7, 569] ⟨223049, 3, [(2, 3), (7, 2), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_569
  · decide +kernel

theorem prime_236287 : Nat.Prime 236287 := by
  apply nodeValid_prime [2, 3, 13127] ⟨236287, 3, [(2, 1), (3, 2), (13127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13127
  · decide +kernel

theorem prime_241333 : Nat.Prime 241333 := by
  apply nodeValid_prime [2, 3, 7, 13, 17] ⟨241333, 14, [(2, 2), (3, 1), (7, 1), (13, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_250169 : Nat.Prime 250169 := by
  apply nodeValid_prime [2, 31271] ⟨250169, 3, [(2, 3), (31271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31271
  · decide +kernel

theorem prime_258659 : Nat.Prime 258659 := by
  apply nodeValid_prime [2, 23, 5623] ⟨258659, 2, [(2, 1), (23, 1), (5623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_5623
  · decide +kernel

theorem prime_265567 : Nat.Prime 265567 := by
  apply nodeValid_prime [2, 3, 7, 6323] ⟨265567, 5, [(2, 1), (3, 1), (7, 1), (6323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6323
  · decide +kernel

theorem prime_274019 : Nat.Prime 274019 := by
  apply nodeValid_prime [2, 19, 7211] ⟨274019, 2, [(2, 1), (19, 1), (7211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_7211
  · decide +kernel

theorem prime_287219 : Nat.Prime 287219 := by
  apply nodeValid_prime [2, 143609] ⟨287219, 2, [(2, 1), (143609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_143609
  · decide +kernel

theorem prime_310333 : Nat.Prime 310333 := by
  apply nodeValid_prime [2, 3, 11, 2351] ⟨310333, 5, [(2, 2), (3, 1), (11, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2351
  · decide +kernel

theorem prime_340409 : Nat.Prime 340409 := by
  apply nodeValid_prime [2, 17, 2503] ⟨340409, 3, [(2, 3), (17, 1), (2503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2503
  · decide +kernel

theorem prime_353677 : Nat.Prime 353677 := by
  apply nodeValid_prime [2, 3, 29473] ⟨353677, 2, [(2, 2), (3, 1), (29473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29473
  · decide +kernel

theorem prime_379283 : Nat.Prime 379283 := by
  apply nodeValid_prime [2, 71, 2671] ⟨379283, 2, [(2, 1), (71, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2671
  · decide +kernel

theorem prime_391031 : Nat.Prime 391031 := by
  apply nodeValid_prime [2, 5, 39103] ⟨391031, 7, [(2, 1), (5, 1), (39103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_39103
  · decide +kernel

theorem prime_397013 : Nat.Prime 397013 := by
  apply nodeValid_prime [2, 7, 11, 1289] ⟨397013, 2, [(2, 2), (7, 1), (11, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1289
  · decide +kernel

theorem prime_455969 : Nat.Prime 455969 := by
  apply nodeValid_prime [2, 14249] ⟨455969, 3, [(2, 5), (14249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14249
  · decide +kernel

theorem prime_525457 : Nat.Prime 525457 := by
  apply nodeValid_prime [2, 3, 41, 89] ⟨525457, 5, [(2, 4), (3, 2), (41, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_89
  · decide +kernel

theorem prime_574439 : Nat.Prime 574439 := by
  apply nodeValid_prime [2, 287219] ⟨574439, 13, [(2, 1), (287219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_287219
  · decide +kernel

theorem prime_724903 : Nat.Prime 724903 := by
  apply nodeValid_prime [2, 3, 120817] ⟨724903, 3, [(2, 1), (3, 1), (120817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_120817
  · decide +kernel

theorem prime_771503 : Nat.Prime 771503 := by
  apply nodeValid_prime [2, 109, 3539] ⟨771503, 5, [(2, 1), (109, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_3539
  · decide +kernel

theorem prime_772921 : Nat.Prime 772921 := by
  apply nodeValid_prime [2, 3, 5, 19, 113] ⟨772921, 13, [(2, 3), (3, 2), (5, 1), (19, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_113
  · decide +kernel

theorem prime_779731 : Nat.Prime 779731 := by
  apply nodeValid_prime [2, 3, 5, 7, 47, 79] ⟨779731, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (47, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_79
  · decide +kernel

theorem prime_976351 : Nat.Prime 976351 := by
  apply nodeValid_prime [2, 3, 5, 23, 283] ⟨976351, 15, [(2, 1), (3, 1), (5, 2), (23, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_283
  · decide +kernel

theorem prime_1191691 : Nat.Prime 1191691 := by
  apply nodeValid_prime [2, 3, 5, 13241] ⟨1191691, 15, [(2, 1), (3, 2), (5, 1), (13241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13241
  · decide +kernel

theorem prime_1255391 : Nat.Prime 1255391 := by
  apply nodeValid_prime [2, 5, 125539] ⟨1255391, 7, [(2, 1), (5, 1), (125539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_125539
  · decide +kernel

theorem prime_1295737 : Nat.Prime 1295737 := by
  apply nodeValid_prime [2, 3, 13, 4153] ⟨1295737, 5, [(2, 3), (3, 1), (13, 1), (4153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4153
  · decide +kernel

theorem prime_1334651 : Nat.Prime 1334651 := by
  apply nodeValid_prime [2, 5, 26693] ⟨1334651, 2, [(2, 1), (5, 2), (26693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_26693
  · decide +kernel

theorem prime_1428593 : Nat.Prime 1428593 := by
  apply nodeValid_prime [2, 11, 8117] ⟨1428593, 3, [(2, 4), (11, 1), (8117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8117
  · decide +kernel

theorem prime_1543007 : Nat.Prime 1543007 := by
  apply nodeValid_prime [2, 771503] ⟨1543007, 5, [(2, 1), (771503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_771503
  · decide +kernel

theorem prime_1798637 : Nat.Prime 1798637 := by
  apply nodeValid_prime [2, 7, 64237] ⟨1798637, 2, [(2, 2), (7, 1), (64237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_64237
  · decide +kernel

theorem prime_2025553 : Nat.Prime 2025553 := by
  apply nodeValid_prime [2, 3, 19, 2221] ⟨2025553, 11, [(2, 4), (3, 1), (19, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2221
  · decide +kernel

theorem prime_2336101 : Nat.Prime 2336101 := by
  apply nodeValid_prime [2, 3, 5, 13, 599] ⟨2336101, 6, [(2, 2), (3, 1), (5, 2), (13, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_599
  · decide +kernel

theorem prime_2899613 : Nat.Prime 2899613 := by
  apply nodeValid_prime [2, 724903] ⟨2899613, 2, [(2, 2), (724903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_724903
  · decide +kernel

theorem prime_3122719 : Nat.Prime 3122719 := by
  apply nodeValid_prime [2, 3, 101, 5153] ⟨3122719, 3, [(2, 1), (3, 1), (101, 1), (5153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_5153
  · decide +kernel

theorem prime_3332579 : Nat.Prime 3332579 := by
  apply nodeValid_prime [2, 17, 98017] ⟨3332579, 2, [(2, 1), (17, 1), (98017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_98017
  · decide +kernel

theorem prime_3902779 : Nat.Prime 3902779 := by
  apply nodeValid_prime [2, 3, 11, 23, 857] ⟨3902779, 2, [(2, 1), (3, 2), (11, 1), (23, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_857
  · decide +kernel

theorem prime_4675343 : Nat.Prime 4675343 := by
  apply nodeValid_prime [2, 7, 53, 6301] ⟨4675343, 7, [(2, 1), (7, 1), (53, 1), (6301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_6301
  · decide +kernel

theorem prime_4747291 : Nat.Prime 4747291 := by
  apply nodeValid_prime [2, 3, 5, 158243] ⟨4747291, 10, [(2, 1), (3, 1), (5, 1), (158243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_158243
  · decide +kernel

theorem prime_5182949 : Nat.Prime 5182949 := by
  apply nodeValid_prime [2, 1295737] ⟨5182949, 2, [(2, 2), (1295737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1295737
  · decide +kernel

theorem prime_5908849 : Nat.Prime 5908849 := by
  apply nodeValid_prime [2, 3, 11, 19, 31] ⟨5908849, 13, [(2, 4), (3, 1), (11, 1), (19, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_10095619 : Nat.Prime 10095619 := by
  apply nodeValid_prime [2, 3, 13, 347, 373] ⟨10095619, 2, [(2, 1), (3, 1), (13, 1), (347, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_347
    · exact prime_373
  · decide +kernel

theorem prime_10789717 : Nat.Prime 10789717 := by
  apply nodeValid_prime [2, 3, 7, 128449] ⟨10789717, 2, [(2, 2), (3, 1), (7, 1), (128449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_128449
  · decide +kernel

theorem prime_11848069 : Nat.Prime 11848069 := by
  apply nodeValid_prime [2, 3, 397, 829] ⟨11848069, 6, [(2, 2), (3, 2), (397, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_829
  · decide +kernel

theorem prime_14377073 : Nat.Prime 14377073 := by
  apply nodeValid_prime [2, 19, 47293] ⟨14377073, 3, [(2, 4), (19, 1), (47293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47293
  · decide +kernel

theorem prime_16903891 : Nat.Prime 16903891 := by
  apply nodeValid_prime [2, 3, 5, 41, 509] ⟨16903891, 3, [(2, 1), (3, 4), (5, 1), (41, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_509
  · decide +kernel

theorem prime_17631841 : Nat.Prime 17631841 := by
  apply nodeValid_prime [2, 3, 5, 109, 337] ⟨17631841, 7, [(2, 5), (3, 1), (5, 1), (109, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_337
  · decide +kernel

theorem prime_23941013 : Nat.Prime 23941013 := by
  apply nodeValid_prime [2, 563, 10631] ⟨23941013, 2, [(2, 2), (563, 1), (10631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_10631
  · decide +kernel

theorem prime_54276367 : Nat.Prime 54276367 := by
  apply nodeValid_prime [2, 3, 23, 541, 727] ⟨54276367, 3, [(2, 1), (3, 1), (23, 1), (541, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_541
    · exact prime_727
  · decide +kernel

theorem prime_61470763 : Nat.Prime 61470763 := by
  apply nodeValid_prime [2, 3, 2659, 3853] ⟨61470763, 2, [(2, 1), (3, 1), (2659, 1), (3853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2659
    · exact prime_3853
  · decide +kernel

theorem prime_74312429 : Nat.Prime 74312429 := by
  apply nodeValid_prime [2, 37, 43, 11677] ⟨74312429, 2, [(2, 2), (37, 1), (43, 1), (11677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
    · exact prime_11677
  · decide +kernel

theorem prime_77015849 : Nat.Prime 77015849 := by
  apply nodeValid_prime [2, 7, 13, 17, 127] ⟨77015849, 3, [(2, 3), (7, 3), (13, 1), (17, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_127
  · decide +kernel

theorem prime_91223399 : Nat.Prime 91223399 := by
  apply nodeValid_prime [2, 7, 89, 10459] ⟨91223399, 7, [(2, 1), (7, 2), (89, 1), (10459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_10459
  · decide +kernel

theorem prime_118376449 : Nat.Prime 118376449 := by
  apply nodeValid_prime [2, 3, 19267] ⟨118376449, 19, [(2, 11), (3, 1), (19267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19267
  · decide +kernel

theorem prime_133160893 : Nat.Prime 133160893 := by
  apply nodeValid_prime [2, 3, 19, 23, 67, 379] ⟨133160893, 2, [(2, 2), (3, 1), (19, 1), (23, 1), (67, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_67
    · exact prime_379
  · decide +kernel

theorem prime_147915809 : Nat.Prime 147915809 := by
  apply nodeValid_prime [2, 79, 58511] ⟨147915809, 3, [(2, 5), (79, 1), (58511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_58511
  · decide +kernel

theorem prime_154819517 : Nat.Prime 154819517 := by
  apply nodeValid_prime [2, 29, 1334651] ⟨154819517, 2, [(2, 2), (29, 1), (1334651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1334651
  · decide +kernel

theorem prime_158126729 : Nat.Prime 158126729 := by
  apply nodeValid_prime [2, 2833, 6977] ⟨158126729, 3, [(2, 3), (2833, 1), (6977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2833
    · exact prime_6977
  · decide +kernel

theorem prime_292520089 : Nat.Prime 292520089 := by
  apply nodeValid_prime [2, 3, 7, 17, 34141] ⟨292520089, 19, [(2, 3), (3, 2), (7, 1), (17, 1), (34141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_34141
  · decide +kernel

theorem prime_368824579 : Nat.Prime 368824579 := by
  apply nodeValid_prime [2, 3, 61470763] ⟨368824579, 2, [(2, 1), (3, 1), (61470763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61470763
  · decide +kernel

theorem prime_746344657 : Nat.Prime 746344657 := by
  apply nodeValid_prime [2, 3, 5182949] ⟨746344657, 5, [(2, 4), (3, 2), (5182949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5182949
  · decide +kernel

theorem prime_986858941 : Nat.Prime 986858941 := by
  apply nodeValid_prime [2, 3, 5, 53, 310333] ⟨986858941, 2, [(2, 2), (3, 1), (5, 1), (53, 1), (310333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_310333
  · decide +kernel

theorem prime_1094680789 : Nat.Prime 1094680789 := by
  apply nodeValid_prime [2, 3, 91223399] ⟨1094680789, 2, [(2, 2), (3, 1), (91223399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_91223399
  · decide +kernel

theorem prime_1694584603 : Nat.Prime 1694584603 := by
  apply nodeValid_prime [2, 3, 79, 1191691] ⟨1694584603, 2, [(2, 1), (3, 2), (79, 1), (1191691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_1191691
  · decide +kernel

theorem prime_1858291943 : Nat.Prime 1858291943 := by
  apply nodeValid_prime [2, 13, 73, 149, 6571] ⟨1858291943, 5, [(2, 1), (13, 1), (73, 1), (149, 1), (6571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_149
    · exact prime_6571
  · decide +kernel

theorem prime_2177649401 : Nat.Prime 2177649401 := by
  apply nodeValid_prime [2, 5, 41, 265567] ⟨2177649401, 3, [(2, 3), (5, 2), (41, 1), (265567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_265567
  · decide +kernel

theorem prime_3469802951 : Nat.Prime 3469802951 := by
  apply nodeValid_prime [2, 5, 89, 779731] ⟨3469802951, 29, [(2, 1), (5, 2), (89, 1), (779731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_779731
  · decide +kernel

theorem prime_3831382439 : Nat.Prime 3831382439 := by
  apply nodeValid_prime [2, 13, 2273, 4987] ⟨3831382439, 11, [(2, 1), (13, 2), (2273, 1), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2273
    · exact prime_4987
  · decide +kernel

theorem prime_4118376737 : Nat.Prime 4118376737 := by
  apply nodeValid_prime [2, 577, 223049] ⟨4118376737, 3, [(2, 5), (577, 1), (223049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_223049
  · decide +kernel

theorem prime_4355298803 : Nat.Prime 4355298803 := by
  apply nodeValid_prime [2, 2177649401] ⟨4355298803, 2, [(2, 1), (2177649401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2177649401
  · decide +kernel

theorem prime_6939605903 : Nat.Prime 6939605903 := by
  apply nodeValid_prime [2, 3469802951] ⟨6939605903, 5, [(2, 1), (3469802951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3469802951
  · decide +kernel

theorem prime_8035333157 : Nat.Prime 8035333157 := by
  apply nodeValid_prime [2, 7331, 274019] ⟨8035333157, 2, [(2, 2), (7331, 1), (274019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7331
    · exact prime_274019
  · decide +kernel

theorem prime_10472523947 : Nat.Prime 10472523947 := by
  apply nodeValid_prime [2, 1103, 4747291] ⟨10472523947, 2, [(2, 1), (1103, 1), (4747291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1103
    · exact prime_4747291
  · decide +kernel

theorem prime_15442773173 : Nat.Prime 15442773173 := by
  apply nodeValid_prime [2, 16339, 236287] ⟨15442773173, 2, [(2, 2), (16339, 1), (236287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16339
    · exact prime_236287
  · decide +kernel

theorem prime_22441122917 : Nat.Prime 22441122917 := by
  apply nodeValid_prime [2, 16481, 340409] ⟨22441122917, 2, [(2, 2), (16481, 1), (340409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16481
    · exact prime_340409
  · decide +kernel

theorem prime_26032954613 : Nat.Prime 26032954613 := by
  apply nodeValid_prime [2, 7, 89, 373, 4001] ⟨26032954613, 2, [(2, 2), (7, 2), (89, 1), (373, 1), (4001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_373
    · exact prime_4001
  · decide +kernel

theorem prime_37732139741 : Nat.Prime 37732139741 := by
  apply nodeValid_prime [2, 5, 107, 17631841] ⟨37732139741, 3, [(2, 2), (5, 1), (107, 1), (17631841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_17631841
  · decide +kernel

theorem prime_51770334233 : Nat.Prime 51770334233 := by
  apply nodeValid_prime [2, 641, 10095619] ⟨51770334233, 3, [(2, 3), (641, 1), (10095619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_10095619
  · decide +kernel

theorem prime_52263585637 : Nat.Prime 52263585637 := by
  apply nodeValid_prime [2, 3, 4355298803] ⟨52263585637, 5, [(2, 2), (3, 1), (4355298803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4355298803
  · decide +kernel

theorem prime_151798250249 : Nat.Prime 151798250249 := by
  apply nodeValid_prime [2, 19, 811, 64811] ⟨151798250249, 3, [(2, 3), (19, 2), (811, 1), (64811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_811
    · exact prime_64811
  · decide +kernel

theorem prime_152088905411 : Nat.Prime 152088905411 := by
  apply nodeValid_prime [2, 5, 13, 4523, 258659] ⟨152088905411, 2, [(2, 1), (5, 1), (13, 1), (4523, 1), (258659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4523
    · exact prime_258659
  · decide +kernel

theorem prime_155016210281 : Nat.Prime 155016210281 := by
  apply nodeValid_prime [2, 5, 47, 487, 169313] ⟨155016210281, 3, [(2, 3), (5, 1), (47, 1), (487, 1), (169313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_487
    · exact prime_169313
  · decide +kernel

theorem prime_300124531643 : Nat.Prime 300124531643 := by
  apply nodeValid_prime [2, 13, 73, 158126729] ⟨300124531643, 2, [(2, 1), (13, 1), (73, 1), (158126729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_158126729
  · decide +kernel

theorem prime_300124531813 : Nat.Prime 300124531813 := by
  apply nodeValid_prime [2, 3, 7, 41, 61, 1428593] ⟨300124531813, 2, [(2, 2), (3, 1), (7, 1), (41, 1), (61, 1), (1428593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_61
    · exact prime_1428593
  · decide +kernel

theorem prime_300124538969 : Nat.Prime 300124538969 := by
  apply nodeValid_prime [2, 1567, 23941013] ⟨300124538969, 3, [(2, 3), (1567, 1), (23941013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1567
    · exact prime_23941013
  · decide +kernel

theorem prime_300701310473 : Nat.Prime 300701310473 := by
  apply nodeValid_prime [2, 113, 173, 307, 6263] ⟨300701310473, 3, [(2, 3), (113, 1), (173, 1), (307, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_173
    · exact prime_307
    · exact prime_6263
  · decide +kernel

theorem prime_300701324503 : Nat.Prime 300701324503 := by
  apply nodeValid_prime [2, 3, 17, 9467, 103801] ⟨300701324503, 3, [(2, 1), (3, 2), (17, 1), (9467, 1), (103801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9467
    · exact prime_103801
  · decide +kernel

theorem prime_300701325611 : Nat.Prime 300701325611 := by
  apply nodeValid_prime [2, 5, 7, 727, 5908849] ⟨300701325611, 6, [(2, 1), (5, 1), (7, 1), (727, 1), (5908849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_727
    · exact prime_5908849
  · decide +kernel

theorem prime_301278780083 : Nat.Prime 301278780083 := by
  apply nodeValid_prime [2, 7, 139, 154819517] ⟨301278780083, 2, [(2, 1), (7, 1), (139, 1), (154819517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_139
    · exact prime_154819517
  · decide +kernel

theorem prime_301278780937 : Nat.Prime 301278780937 := by
  apply nodeValid_prime [2, 3, 7, 19, 23, 455969] ⟨301278780937, 5, [(2, 3), (3, 3), (7, 1), (19, 1), (23, 1), (455969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_455969
  · decide +kernel

theorem prime_301278836569 : Nat.Prime 301278836569 := by
  apply nodeValid_prime [2, 3, 17, 19, 179, 217121] ⟨301278836569, 11, [(2, 3), (3, 1), (17, 1), (19, 1), (179, 1), (217121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_179
    · exact prime_217121
  · decide +kernel

theorem prime_301857086599 : Nat.Prime 301857086599 := by
  apply nodeValid_prime [2, 3, 677, 74312429] ⟨301857086599, 3, [(2, 1), (3, 1), (677, 1), (74312429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
    · exact prime_74312429
  · decide +kernel

theorem prime_301857086863 : Nat.Prime 301857086863 := by
  apply nodeValid_prime [2, 3, 19, 3079, 3539] ⟨301857086863, 3, [(2, 1), (3, 6), (19, 1), (3079, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3079
    · exact prime_3539
  · decide +kernel

theorem prime_301857117929 : Nat.Prime 301857117929 := by
  apply nodeValid_prime [2, 37732139741] ⟨301857117929, 3, [(2, 3), (37732139741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37732139741
  · decide +kernel

theorem prime_302436107101 : Nat.Prime 302436107101 := by
  apply nodeValid_prime [2, 3, 5, 4099, 9109] ⟨302436107101, 2, [(2, 2), (3, 4), (5, 2), (4099, 1), (9109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4099
    · exact prime_9109
  · decide +kernel

theorem prime_302436107629 : Nat.Prime 302436107629 := by
  apply nodeValid_prime [2, 3, 1753, 14377073] ⟨302436107629, 6, [(2, 2), (3, 1), (1753, 1), (14377073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1753
    · exact prime_14377073
  · decide +kernel

theorem prime_302436154781 : Nat.Prime 302436154781 := by
  apply nodeValid_prime [2, 5, 41, 368824579] ⟨302436154781, 2, [(2, 2), (5, 1), (41, 1), (368824579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_368824579
  · decide +kernel

theorem prime_303015929863 : Nat.Prime 303015929863 := by
  apply nodeValid_prime [2, 3, 37, 59, 797, 29027] ⟨303015929863, 3, [(2, 1), (3, 1), (37, 1), (59, 1), (797, 1), (29027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_59
    · exact prime_797
    · exact prime_29027
  · decide +kernel

theorem prime_303015930743 : Nat.Prime 303015930743 := by
  apply nodeValid_prime [2, 7, 29, 746344657] ⟨303015930743, 5, [(2, 1), (7, 1), (29, 1), (746344657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_746344657
  · decide +kernel

theorem prime_303015947513 : Nat.Prime 303015947513 := by
  apply nodeValid_prime [2, 1033, 2789, 13147] ⟨303015947513, 3, [(2, 3), (1033, 1), (2789, 1), (13147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1033
    · exact prime_2789
    · exact prime_13147
  · decide +kernel

theorem prime_303596476759 : Nat.Prime 303596476759 := by
  apply nodeValid_prime [2, 3, 73, 77015849] ⟨303596476759, 3, [(2, 1), (3, 3), (73, 1), (77015849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_77015849
  · decide +kernel

theorem prime_303596477077 : Nat.Prime 303596477077 := by
  apply nodeValid_prime [2, 3, 233, 2531, 42901] ⟨303596477077, 5, [(2, 2), (3, 1), (233, 1), (2531, 1), (42901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_2531
    · exact prime_42901
  · decide +kernel

theorem prime_303596500499 : Nat.Prime 303596500499 := by
  apply nodeValid_prime [2, 151798250249] ⟨303596500499, 2, [(2, 1), (151798250249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_151798250249
  · decide +kernel

theorem prime_304177810823 : Nat.Prime 304177810823 := by
  apply nodeValid_prime [2, 152088905411] ⟨304177810823, 5, [(2, 1), (152088905411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_152088905411
  · decide +kernel

theorem prime_304177815581 : Nat.Prime 304177815581 := by
  apply nodeValid_prime [2, 5, 3253, 4675343] ⟨304177815581, 2, [(2, 2), (5, 1), (3253, 1), (4675343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3253
    · exact prime_4675343
  · decide +kernel

theorem prime_304177815647 : Nat.Prime 304177815647 := by
  apply nodeValid_prime [2, 47, 971, 3332579] ⟨304177815647, 5, [(2, 1), (47, 1), (971, 1), (3332579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_971
    · exact prime_3332579
  · decide +kernel

theorem prime_304759878539 : Nat.Prime 304759878539 := by
  apply nodeValid_prime [2, 37, 4118376737] ⟨304759878539, 2, [(2, 1), (37, 1), (4118376737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_4118376737
  · decide +kernel

theorem prime_304759878653 : Nat.Prime 304759878653 := by
  apply nodeValid_prime [2, 41, 1858291943] ⟨304759878653, 2, [(2, 2), (41, 1), (1858291943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1858291943
  · decide +kernel

theorem prime_304759878923 : Nat.Prime 304759878923 := by
  apply nodeValid_prime [2, 127, 199, 311, 19387] ⟨304759878923, 2, [(2, 1), (127, 1), (199, 1), (311, 1), (19387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_199
    · exact prime_311
    · exact prime_19387
  · decide +kernel

theorem prime_305342659733 : Nat.Prime 305342659733 := by
  apply nodeValid_prime [2, 11, 6939605903] ⟨305342659733, 2, [(2, 2), (11, 1), (6939605903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6939605903
  · decide +kernel

theorem prime_305342659967 : Nat.Prime 305342659967 := by
  apply nodeValid_prime [2, 19, 8035333157] ⟨305342659967, 5, [(2, 1), (19, 1), (8035333157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_8035333157
  · decide +kernel

theorem prime_305342698301 : Nat.Prime 305342698301 := by
  apply nodeValid_prime [2, 5, 7691, 397013] ⟨305342698301, 2, [(2, 2), (5, 2), (7691, 1), (397013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7691
    · exact prime_397013
  · decide +kernel

theorem prime_305926231099 : Nat.Prime 305926231099 := by
  apply nodeValid_prime [2, 3, 83, 1571, 391031] ⟨305926231099, 2, [(2, 1), (3, 1), (83, 1), (1571, 1), (391031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_1571
    · exact prime_391031
  · decide +kernel

theorem prime_305926232791 : Nat.Prime 305926232791 := by
  apply nodeValid_prime [2, 3, 5, 8123, 1255391] ⟨305926232791, 6, [(2, 1), (3, 1), (5, 1), (8123, 1), (1255391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8123
    · exact prime_1255391
  · decide +kernel

theorem prime_305926271711 : Nat.Prime 305926271711 := by
  apply nodeValid_prime [2, 5, 31, 986858941] ⟨305926271711, 7, [(2, 1), (5, 1), (31, 1), (986858941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_986858941
  · decide +kernel

theorem prime_306510595121 : Nat.Prime 306510595121 := by
  apply nodeValid_prime [2, 5, 3831382439] ⟨306510595121, 3, [(2, 4), (5, 1), (3831382439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3831382439
  · decide +kernel

theorem prime_306510620719 : Nat.Prime 306510620719 := by
  apply nodeValid_prime [2, 3, 31, 41, 1901, 21143] ⟨306510620719, 6, [(2, 1), (3, 1), (31, 1), (41, 1), (1901, 1), (21143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_41
    · exact prime_1901
    · exact prime_21143
  · decide +kernel

theorem prime_306510620921 : Nat.Prime 306510620921 := by
  apply nodeValid_prime [2, 5, 7, 1094680789] ⟨306510620921, 3, [(2, 3), (5, 1), (7, 1), (1094680789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1094680789
  · decide +kernel

theorem prime_307095675553 : Nat.Prime 307095675553 := by
  apply nodeValid_prime [2, 3, 523, 1409, 1447] ⟨307095675553, 5, [(2, 5), (3, 2), (523, 1), (1409, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_1409
    · exact prime_1447
  · decide +kernel

theorem prime_307095684107 : Nat.Prime 307095684107 := by
  apply nodeValid_prime [2, 85369, 1798637] ⟨307095684107, 2, [(2, 1), (85369, 1), (1798637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_85369
    · exact prime_1798637
  · decide +kernel

theorem prime_307095684487 : Nat.Prime 307095684487 := by
  apply nodeValid_prime [2, 3, 23, 41, 54276367] ⟨307095684487, 3, [(2, 1), (3, 1), (23, 1), (41, 1), (54276367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_54276367
  · decide +kernel

theorem prime_307681500701 : Nat.Prime 307681500701 := by
  apply nodeValid_prime [2, 5, 7, 31, 2025553] ⟨307681500701, 3, [(2, 2), (5, 2), (7, 2), (31, 1), (2025553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_2025553
  · decide +kernel

theorem prime_307681503071 : Nat.Prime 307681503071 := by
  apply nodeValid_prime [2, 5, 59, 167, 3122719] ⟨307681503071, 13, [(2, 1), (5, 1), (59, 1), (167, 1), (3122719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_167
    · exact prime_3122719
  · decide +kernel

theorem prime_307681517441 : Nat.Prime 307681517441 := by
  apply nodeValid_prime [2, 5, 11, 23, 31, 61297] ⟨307681517441, 21, [(2, 7), (5, 1), (11, 1), (23, 1), (31, 1), (61297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_31
    · exact prime_61297
  · decide +kernel

theorem prime_308268093839 : Nat.Prime 308268093839 := by
  apply nodeValid_prime [2, 179, 1499, 574439] ⟨308268093839, 17, [(2, 1), (179, 1), (1499, 1), (574439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_1499
    · exact prime_574439
  · decide +kernel

theorem prime_308268093919 : Nat.Prime 308268093919 := by
  apply nodeValid_prime [2, 3, 19, 41, 149, 23297] ⟨308268093919, 3, [(2, 1), (3, 1), (19, 2), (41, 1), (149, 1), (23297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_149
    · exact prime_23297
  · decide +kernel

theorem prime_308268110489 : Nat.Prime 308268110489 := by
  apply nodeValid_prime [2, 13, 17, 113, 1543007] ⟨308268110489, 6, [(2, 3), (13, 1), (17, 1), (113, 1), (1543007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_113
    · exact prime_1543007
  · decide +kernel

theorem prime_308855456863 : Nat.Prime 308855456863 := by
  apply nodeValid_prime [2, 3, 135719, 379283] ⟨308855456863, 3, [(2, 1), (3, 1), (135719, 1), (379283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_135719
    · exact prime_379283
  · decide +kernel

theorem prime_308855462693 : Nat.Prime 308855462693 := by
  apply nodeValid_prime [2, 7, 19, 11848069] ⟨308855462693, 2, [(2, 2), (7, 3), (19, 1), (11848069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_11848069
  · decide +kernel

theorem prime_308855463461 : Nat.Prime 308855463461 := by
  apply nodeValid_prime [2, 5, 15442773173] ⟨308855463461, 3, [(2, 2), (5, 1), (15442773173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15442773173
  · decide +kernel

theorem prime_309443541353 : Nat.Prime 309443541353 := by
  apply nodeValid_prime [2, 11, 17, 53, 3902779] ⟨309443541353, 5, [(2, 3), (11, 1), (17, 1), (53, 1), (3902779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_53
    · exact prime_3902779
  · decide +kernel

theorem prime_309443542523 : Nat.Prime 309443542523 := by
  apply nodeValid_prime [2, 19, 43, 757, 250169] ⟨309443542523, 2, [(2, 1), (19, 1), (43, 1), (757, 1), (250169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_757
    · exact prime_250169
  · decide +kernel

theorem prime_309443559877 : Nat.Prime 309443559877 := by
  apply nodeValid_prime [2, 3, 11, 337, 772921] ⟨309443559877, 2, [(2, 2), (3, 3), (11, 1), (337, 1), (772921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_337
    · exact prime_772921
  · decide +kernel

theorem prime_310032420041 : Nat.Prime 310032420041 := by
  apply nodeValid_prime [2, 5, 7, 43, 1117, 23053] ⟨310032420041, 3, [(2, 3), (5, 1), (7, 1), (43, 1), (1117, 1), (23053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_1117
    · exact prime_23053
  · decide +kernel

theorem prime_310032420563 : Nat.Prime 310032420563 := by
  apply nodeValid_prime [2, 155016210281] ⟨310032420563, 2, [(2, 1), (155016210281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_155016210281
  · decide +kernel

theorem prime_310032421187 : Nat.Prime 310032421187 := by
  apply nodeValid_prime [2, 193, 277, 2899613] ⟨310032421187, 2, [(2, 1), (193, 1), (277, 1), (2899613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_277
    · exact prime_2899613
  · decide +kernel

theorem prime_310622005399 : Nat.Prime 310622005399 := by
  apply nodeValid_prime [2, 3, 51770334233] ⟨310622005399, 6, [(2, 1), (3, 1), (51770334233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51770334233
  · decide +kernel

theorem prime_310622005567 : Nat.Prime 310622005567 := by
  apply nodeValid_prime [2, 3, 83, 89, 2336101] ⟨310622005567, 3, [(2, 1), (3, 2), (83, 1), (89, 1), (2336101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_89
    · exact prime_2336101
  · decide +kernel

theorem prime_310622041091 : Nat.Prime 310622041091 := by
  apply nodeValid_prime [2, 5, 17, 83, 2053, 10723] ⟨310622041091, 2, [(2, 1), (5, 1), (17, 1), (83, 1), (2053, 1), (10723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_83
    · exact prime_2053
    · exact prime_10723
  · decide +kernel

theorem prime_311212417319 : Nat.Prime 311212417319 := by
  apply nodeValid_prime [2, 11, 23, 37, 47, 353677] ⟨311212417319, 11, [(2, 1), (11, 1), (23, 1), (37, 1), (47, 1), (353677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_37
    · exact prime_47
    · exact prime_353677
  · decide +kernel

theorem prime_311212417391 : Nat.Prime 311212417391 := by
  apply nodeValid_prime [2, 5, 7, 8461, 525457] ⟨311212417391, 14, [(2, 1), (5, 1), (7, 1), (8461, 1), (525457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_8461
    · exact prime_525457
  · decide +kernel

theorem prime_311212418149 : Nat.Prime 311212418149 := by
  apply nodeValid_prime [2, 3, 113, 317, 241333] ⟨311212418149, 6, [(2, 2), (3, 2), (113, 1), (317, 1), (241333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_317
    · exact prime_241333
  · decide +kernel

theorem prime_311803549957 : Nat.Prime 311803549957 := by
  apply nodeValid_prime [2, 3, 2957, 976351] ⟨311803549957, 2, [(2, 2), (3, 3), (2957, 1), (976351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2957
    · exact prime_976351
  · decide +kernel

theorem prime_311803566667 : Nat.Prime 311803566667 := by
  apply nodeValid_prime [2, 3, 439, 118376449] ⟨311803566667, 3, [(2, 1), (3, 1), (439, 1), (118376449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_439
    · exact prime_118376449
  · decide +kernel

theorem prime_311803566953 : Nat.Prime 311803566953 := by
  apply nodeValid_prime [2, 23, 1694584603] ⟨311803566953, 3, [(2, 3), (23, 1), (1694584603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1694584603
  · decide +kernel

theorem prime_312395449867 : Nat.Prime 312395449867 := by
  apply nodeValid_prime [2, 3, 43, 577, 797, 2633] ⟨312395449867, 2, [(2, 1), (3, 1), (43, 1), (577, 1), (797, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_577
    · exact prime_797
    · exact prime_2633
  · decide +kernel

theorem prime_312395454979 : Nat.Prime 312395454979 := by
  apply nodeValid_prime [2, 3, 17, 23, 133160893] ⟨312395454979, 3, [(2, 1), (3, 1), (17, 1), (23, 1), (133160893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_133160893
  · decide +kernel

theorem prime_312395455357 : Nat.Prime 312395455357 := by
  apply nodeValid_prime [2, 3, 26032954613] ⟨312395455357, 5, [(2, 2), (3, 1), (26032954613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26032954613
  · decide +kernel

theorem prime_312988076383 : Nat.Prime 312988076383 := by
  apply nodeValid_prime [2, 3, 23, 43, 367, 143719] ⟨312988076383, 3, [(2, 1), (3, 1), (23, 1), (43, 1), (367, 1), (143719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_43
    · exact prime_367
    · exact prime_143719
  · decide +kernel

theorem prime_312988078609 : Nat.Prime 312988078609 := by
  apply nodeValid_prime [2, 3, 179, 5743, 6343] ⟨312988078609, 7, [(2, 4), (3, 1), (179, 1), (5743, 1), (6343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_5743
    · exact prime_6343
  · decide +kernel

theorem prime_312988110737 : Nat.Prime 312988110737 := by
  apply nodeValid_prime [2, 7, 37, 10789717] ⟨312988110737, 3, [(2, 4), (7, 2), (37, 1), (10789717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_10789717
  · decide +kernel

theorem prime_313581513823 : Nat.Prime 313581513823 := by
  apply nodeValid_prime [2, 3, 52263585637] ⟨313581513823, 5, [(2, 1), (3, 1), (52263585637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52263585637
  · decide +kernel

theorem prime_313581515081 : Nat.Prime 313581515081 := by
  apply nodeValid_prime [2, 5, 53, 147915809] ⟨313581515081, 3, [(2, 3), (5, 1), (53, 1), (147915809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_147915809
  · decide +kernel

theorem prime_313581535409 : Nat.Prime 313581535409 := by
  apply nodeValid_prime [2, 67, 292520089] ⟨313581535409, 3, [(2, 4), (67, 1), (292520089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_292520089
  · decide +kernel

theorem prime_314175718127 : Nat.Prime 314175718127 := by
  apply nodeValid_prime [2, 9293, 16903891] ⟨314175718127, 5, [(2, 1), (9293, 1), (16903891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9293
    · exact prime_16903891
  · decide +kernel

theorem prime_314175718411 : Nat.Prime 314175718411 := by
  apply nodeValid_prime [2, 3, 5, 10472523947] ⟨314175718411, 2, [(2, 1), (3, 1), (5, 1), (10472523947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10472523947
  · decide +kernel

theorem prime_314175720839 : Nat.Prime 314175720839 := by
  apply nodeValid_prime [2, 7, 22441122917] ⟨314175720839, 13, [(2, 1), (7, 1), (22441122917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_22441122917
  · decide +kernel

end Sude.Lucas.Generated
