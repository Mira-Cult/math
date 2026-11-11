import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3877 : Nat.Prime 3877 := by
  apply nodeValid_prime [2, 3, 17, 19] ⟨3877, 2, [(2, 2), (3, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_5227 : Nat.Prime 5227 := by
  apply nodeValid_prime [2, 3, 13, 67] ⟨5227, 2, [(2, 1), (3, 1), (13, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_6619 : Nat.Prime 6619 := by
  apply nodeValid_prime [2, 3, 1103] ⟨6619, 2, [(2, 1), (3, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1103
  · decide +kernel

theorem prime_7727 : Nat.Prime 7727 := by
  apply nodeValid_prime [2, 3863] ⟨7727, 5, [(2, 1), (3863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3863
  · decide +kernel

theorem prime_8191 : Nat.Prime 8191 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨8191, 17, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_8521 : Nat.Prime 8521 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨8521, 13, [(2, 3), (3, 1), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_9281 : Nat.Prime 9281 := by
  apply nodeValid_prime [2, 5, 29] ⟨9281, 3, [(2, 6), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_9419 : Nat.Prime 9419 := by
  apply nodeValid_prime [2, 17, 277] ⟨9419, 2, [(2, 1), (17, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_277
  · decide +kernel

theorem prime_13537 : Nat.Prime 13537 := by
  apply nodeValid_prime [2, 3, 47] ⟨13537, 7, [(2, 5), (3, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_13721 : Nat.Prime 13721 := by
  apply nodeValid_prime [2, 5, 7] ⟨13721, 3, [(2, 3), (5, 1), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_15289 : Nat.Prime 15289 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨15289, 11, [(2, 3), (3, 1), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_15467 : Nat.Prime 15467 := by
  apply nodeValid_prime [2, 11, 19, 37] ⟨15467, 5, [(2, 1), (11, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_16189 : Nat.Prime 16189 := by
  apply nodeValid_prime [2, 3, 19, 71] ⟨16189, 2, [(2, 2), (3, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_17449 : Nat.Prime 17449 := by
  apply nodeValid_prime [2, 3, 727] ⟨17449, 14, [(2, 3), (3, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_727
  · decide +kernel

theorem prime_20963 : Nat.Prime 20963 := by
  apply nodeValid_prime [2, 47, 223] ⟨20963, 2, [(2, 1), (47, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_223
  · decide +kernel

theorem prime_21379 : Nat.Prime 21379 := by
  apply nodeValid_prime [2, 3, 7, 509] ⟨21379, 2, [(2, 1), (3, 1), (7, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_509
  · decide +kernel

theorem prime_22709 : Nat.Prime 22709 := by
  apply nodeValid_prime [2, 7, 811] ⟨22709, 2, [(2, 2), (7, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_811
  · decide +kernel

theorem prime_26833 : Nat.Prime 26833 := by
  apply nodeValid_prime [2, 3, 13, 43] ⟨26833, 5, [(2, 4), (3, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_28109 : Nat.Prime 28109 := by
  apply nodeValid_prime [2, 7027] ⟨28109, 2, [(2, 2), (7027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7027
  · decide +kernel

theorem prime_28123 : Nat.Prime 28123 := by
  apply nodeValid_prime [2, 3, 43, 109] ⟨28123, 2, [(2, 1), (3, 1), (43, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_109
  · decide +kernel

theorem prime_36011 : Nat.Prime 36011 := by
  apply nodeValid_prime [2, 5, 13, 277] ⟨36011, 2, [(2, 1), (5, 1), (13, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_277
  · decide +kernel

theorem prime_42697 : Nat.Prime 42697 := by
  apply nodeValid_prime [2, 3, 593] ⟨42697, 5, [(2, 3), (3, 2), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_593
  · decide +kernel

theorem prime_43853 : Nat.Prime 43853 := by
  apply nodeValid_prime [2, 19, 577] ⟨43853, 2, [(2, 2), (19, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_577
  · decide +kernel

theorem prime_43951 : Nat.Prime 43951 := by
  apply nodeValid_prime [2, 3, 5, 293] ⟨43951, 6, [(2, 1), (3, 1), (5, 2), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
  · decide +kernel

theorem prime_47527 : Nat.Prime 47527 := by
  apply nodeValid_prime [2, 3, 89] ⟨47527, 3, [(2, 1), (3, 1), (89, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_49757 : Nat.Prime 49757 := by
  apply nodeValid_prime [2, 7, 1777] ⟨49757, 2, [(2, 2), (7, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1777
  · decide +kernel

theorem prime_51869 : Nat.Prime 51869 := by
  apply nodeValid_prime [2, 12967] ⟨51869, 2, [(2, 2), (12967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12967
  · decide +kernel

theorem prime_59119 : Nat.Prime 59119 := by
  apply nodeValid_prime [2, 3, 59, 167] ⟨59119, 3, [(2, 1), (3, 1), (59, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_167
  · decide +kernel

theorem prime_63601 : Nat.Prime 63601 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨63601, 7, [(2, 4), (3, 1), (5, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_66721 : Nat.Prime 66721 := by
  apply nodeValid_prime [2, 3, 5, 139] ⟨66721, 13, [(2, 5), (3, 1), (5, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
  · decide +kernel

theorem prime_66947 : Nat.Prime 66947 := by
  apply nodeValid_prime [2, 11, 17, 179] ⟨66947, 2, [(2, 1), (11, 1), (17, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_179
  · decide +kernel

theorem prime_68489 : Nat.Prime 68489 := by
  apply nodeValid_prime [2, 7, 1223] ⟨68489, 3, [(2, 3), (7, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1223
  · decide +kernel

theorem prime_75167 : Nat.Prime 75167 := by
  apply nodeValid_prime [2, 7, 13, 59] ⟨75167, 5, [(2, 1), (7, 2), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_75353 : Nat.Prime 75353 := by
  apply nodeValid_prime [2, 9419] ⟨75353, 3, [(2, 3), (9419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9419
  · decide +kernel

theorem prime_77977 : Nat.Prime 77977 := by
  apply nodeValid_prime [2, 3, 19] ⟨77977, 5, [(2, 3), (3, 3), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_79843 : Nat.Prime 79843 := by
  apply nodeValid_prime [2, 3, 7, 1901] ⟨79843, 2, [(2, 1), (3, 1), (7, 1), (1901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1901
  · decide +kernel

theorem prime_83203 : Nat.Prime 83203 := by
  apply nodeValid_prime [2, 3, 7, 283] ⟨83203, 2, [(2, 1), (3, 1), (7, 2), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
  · decide +kernel

theorem prime_97117 : Nat.Prime 97117 := by
  apply nodeValid_prime [2, 3, 8093] ⟨97117, 2, [(2, 2), (3, 1), (8093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8093
  · decide +kernel

theorem prime_104113 : Nat.Prime 104113 := by
  apply nodeValid_prime [2, 3, 241] ⟨104113, 5, [(2, 4), (3, 3), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel

theorem prime_106219 : Nat.Prime 106219 := by
  apply nodeValid_prime [2, 3, 7, 281] ⟨106219, 7, [(2, 1), (3, 3), (7, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_281
  · decide +kernel

theorem prime_128351 : Nat.Prime 128351 := by
  apply nodeValid_prime [2, 5, 17, 151] ⟨128351, 11, [(2, 1), (5, 2), (17, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_151
  · decide +kernel

theorem prime_136979 : Nat.Prime 136979 := by
  apply nodeValid_prime [2, 68489] ⟨136979, 2, [(2, 1), (68489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68489
  · decide +kernel

theorem prime_149533 : Nat.Prime 149533 := by
  apply nodeValid_prime [2, 3, 17, 733] ⟨149533, 5, [(2, 2), (3, 1), (17, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_733
  · decide +kernel

theorem prime_215939 : Nat.Prime 215939 := by
  apply nodeValid_prime [2, 101, 1069] ⟨215939, 2, [(2, 1), (101, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_1069
  · decide +kernel

theorem prime_238321 : Nat.Prime 238321 := by
  apply nodeValid_prime [2, 3, 5, 331] ⟨238321, 13, [(2, 4), (3, 2), (5, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_331
  · decide +kernel

theorem prime_239803 : Nat.Prime 239803 := by
  apply nodeValid_prime [2, 3, 17, 2351] ⟨239803, 2, [(2, 1), (3, 1), (17, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2351
  · decide +kernel

theorem prime_255457 : Nat.Prime 255457 := by
  apply nodeValid_prime [2, 3, 887] ⟨255457, 7, [(2, 5), (3, 2), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_887
  · decide +kernel

theorem prime_281747 : Nat.Prime 281747 := by
  apply nodeValid_prime [2, 179, 787] ⟨281747, 2, [(2, 1), (179, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_787
  · decide +kernel

theorem prime_292759 : Nat.Prime 292759 := by
  apply nodeValid_prime [2, 3, 59, 827] ⟨292759, 6, [(2, 1), (3, 1), (59, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_827
  · decide +kernel

theorem prime_305497 : Nat.Prime 305497 := by
  apply nodeValid_prime [2, 3, 4243] ⟨305497, 5, [(2, 3), (3, 2), (4243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4243
  · decide +kernel

theorem prime_313219 : Nat.Prime 313219 := by
  apply nodeValid_prime [2, 3, 17401] ⟨313219, 3, [(2, 1), (3, 2), (17401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17401
  · decide +kernel

theorem prime_343037 : Nat.Prime 343037 := by
  apply nodeValid_prime [2, 191, 449] ⟨343037, 2, [(2, 2), (191, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_449
  · decide +kernel

theorem prime_349397 : Nat.Prime 349397 := by
  apply nodeValid_prime [2, 113, 773] ⟨349397, 2, [(2, 2), (113, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_773
  · decide +kernel

theorem prime_363043 : Nat.Prime 363043 := by
  apply nodeValid_prime [2, 3, 83] ⟨363043, 3, [(2, 1), (3, 7), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_667211 : Nat.Prime 667211 := by
  apply nodeValid_prime [2, 5, 66721] ⟨667211, 2, [(2, 1), (5, 1), (66721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_66721
  · decide +kernel

theorem prime_1135451 : Nat.Prime 1135451 := by
  apply nodeValid_prime [2, 5, 22709] ⟨1135451, 2, [(2, 1), (5, 2), (22709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22709
  · decide +kernel

theorem prime_1252877 : Nat.Prime 1252877 := by
  apply nodeValid_prime [2, 313219] ⟨1252877, 2, [(2, 2), (313219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_313219
  · decide +kernel

theorem prime_1334423 : Nat.Prime 1334423 := by
  apply nodeValid_prime [2, 667211] ⟨1334423, 5, [(2, 1), (667211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_667211
  · decide +kernel

theorem prime_1457999 : Nat.Prime 1457999 := by
  apply nodeValid_prime [2, 89, 8191] ⟨1457999, 7, [(2, 1), (89, 1), (8191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_8191
  · decide +kernel

theorem prime_1616429 : Nat.Prime 1616429 := by
  apply nodeValid_prime [2, 11, 17, 2161] ⟨1616429, 3, [(2, 2), (11, 1), (17, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_2161
  · decide +kernel

theorem prime_1620371 : Nat.Prime 1620371 := by
  apply nodeValid_prime [2, 5, 31, 5227] ⟨1620371, 2, [(2, 1), (5, 1), (31, 1), (5227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_5227
  · decide +kernel

theorem prime_1908239 : Nat.Prime 1908239 := by
  apply nodeValid_prime [2, 37, 107, 241] ⟨1908239, 7, [(2, 1), (37, 1), (107, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_107
    · exact prime_241
  · decide +kernel

theorem prime_1953799 : Nat.Prime 1953799 := by
  apply nodeValid_prime [2, 3, 7, 11, 4229] ⟨1953799, 6, [(2, 1), (3, 1), (7, 1), (11, 1), (4229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_4229
  · decide +kernel

theorem prime_2268403 : Nat.Prime 2268403 := by
  apply nodeValid_prime [2, 3, 73, 5179] ⟨2268403, 2, [(2, 1), (3, 1), (73, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_5179
  · decide +kernel

theorem prime_2437207 : Nat.Prime 2437207 := by
  apply nodeValid_prime [2, 3, 19, 21379] ⟨2437207, 3, [(2, 1), (3, 1), (19, 1), (21379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_21379
  · decide +kernel

theorem prime_2642257 : Nat.Prime 2642257 := by
  apply nodeValid_prime [2, 3, 59, 311] ⟨2642257, 5, [(2, 4), (3, 2), (59, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_311
  · decide +kernel

theorem prime_2995309 : Nat.Prime 2995309 := by
  apply nodeValid_prime [2, 3, 83203] ⟨2995309, 2, [(2, 2), (3, 2), (83203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83203
  · decide +kernel

theorem prime_3676643 : Nat.Prime 3676643 := by
  apply nodeValid_prime [2, 23, 257, 311] ⟨3676643, 2, [(2, 1), (23, 1), (257, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_257
    · exact prime_311
  · decide +kernel

theorem prime_3765521 : Nat.Prime 3765521 := by
  apply nodeValid_prime [2, 5, 11, 389] ⟨3765521, 6, [(2, 4), (5, 1), (11, 2), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_389
  · decide +kernel

theorem prime_4230883 : Nat.Prime 4230883 := by
  apply nodeValid_prime [2, 3, 19, 89, 139] ⟨4230883, 2, [(2, 1), (3, 2), (19, 1), (89, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_89
    · exact prime_139
  · decide +kernel

theorem prime_5037863 : Nat.Prime 5037863 := by
  apply nodeValid_prime [2, 53, 47527] ⟨5037863, 5, [(2, 1), (53, 1), (47527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_47527
  · decide +kernel

theorem prime_5341153 : Nat.Prime 5341153 := by
  apply nodeValid_prime [2, 3, 23, 41, 59] ⟨5341153, 5, [(2, 5), (3, 1), (23, 1), (41, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_59
  · decide +kernel

theorem prime_6478489 : Nat.Prime 6478489 := by
  apply nodeValid_prime [2, 3, 89, 337] ⟨6478489, 14, [(2, 3), (3, 3), (89, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_337
  · decide +kernel

theorem prime_7353287 : Nat.Prime 7353287 := by
  apply nodeValid_prime [2, 3676643] ⟨7353287, 5, [(2, 1), (3676643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3676643
  · decide +kernel

theorem prime_8239447 : Nat.Prime 8239447 := by
  apply nodeValid_prime [2, 3, 167, 2741] ⟨8239447, 3, [(2, 1), (3, 2), (167, 1), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_2741
  · decide +kernel

theorem prime_8570647 : Nat.Prime 8570647 := by
  apply nodeValid_prime [2, 3, 7, 251, 271] ⟨8570647, 5, [(2, 1), (3, 2), (7, 1), (251, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_251
    · exact prime_271
  · decide +kernel

theorem prime_10318193 : Nat.Prime 10318193 := by
  apply nodeValid_prime [2, 47, 13721] ⟨10318193, 3, [(2, 4), (47, 1), (13721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_13721
  · decide +kernel

theorem prime_11632637 : Nat.Prime 11632637 := by
  apply nodeValid_prime [2, 19, 269, 569] ⟨11632637, 2, [(2, 2), (19, 1), (269, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_269
    · exact prime_569
  · decide +kernel

theorem prime_11981237 : Nat.Prime 11981237 := by
  apply nodeValid_prime [2, 2995309] ⟨11981237, 2, [(2, 2), (2995309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2995309
  · decide +kernel

theorem prime_12240223 : Nat.Prime 12240223 := by
  apply nodeValid_prime [2, 3, 41, 49757] ⟨12240223, 6, [(2, 1), (3, 1), (41, 1), (49757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_49757
  · decide +kernel

theorem prime_14501029 : Nat.Prime 14501029 := by
  apply nodeValid_prime [2, 3, 19, 63601] ⟨14501029, 2, [(2, 2), (3, 1), (19, 1), (63601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_63601
  · decide +kernel

theorem prime_20107429 : Nat.Prime 20107429 := by
  apply nodeValid_prime [2, 3, 11, 23, 37, 179] ⟨20107429, 2, [(2, 2), (3, 1), (11, 1), (23, 1), (37, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_37
    · exact prime_179
  · decide +kernel

theorem prime_20216191 : Nat.Prime 20216191 := by
  apply nodeValid_prime [2, 3, 5, 19, 29, 1223] ⟨20216191, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (29, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_1223
  · decide +kernel

theorem prime_22684031 : Nat.Prime 22684031 := by
  apply nodeValid_prime [2, 5, 2268403] ⟨22684031, 13, [(2, 1), (5, 1), (2268403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2268403
  · decide +kernel

theorem prime_25913957 : Nat.Prime 25913957 := by
  apply nodeValid_prime [2, 6478489] ⟨25913957, 2, [(2, 2), (6478489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6478489
  · decide +kernel

theorem prime_45797737 : Nat.Prime 45797737 := by
  apply nodeValid_prime [2, 3, 1908239] ⟨45797737, 5, [(2, 3), (3, 1), (1908239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1908239
  · decide +kernel

theorem prime_63834593 : Nat.Prime 63834593 := by
  apply nodeValid_prime [2, 17, 271, 433] ⟨63834593, 3, [(2, 5), (17, 1), (271, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_271
    · exact prime_433
  · decide +kernel

theorem prime_71887423 : Nat.Prime 71887423 := by
  apply nodeValid_prime [2, 3, 11981237] ⟨71887423, 3, [(2, 1), (3, 1), (11981237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11981237
  · decide +kernel

theorem prime_71945477 : Nat.Prime 71945477 := by
  apply nodeValid_prime [2, 19, 929, 1019] ⟨71945477, 2, [(2, 2), (19, 1), (929, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_929
    · exact prime_1019
  · decide +kernel

theorem prime_72240799 : Nat.Prime 72240799 := by
  apply nodeValid_prime [2, 3, 7, 29, 37, 229] ⟨72240799, 3, [(2, 1), (3, 1), (7, 2), (29, 1), (37, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_37
    · exact prime_229
  · decide +kernel

theorem prime_87729443 : Nat.Prime 87729443 := by
  apply nodeValid_prime [2, 31, 37, 167, 229] ⟨87729443, 2, [(2, 1), (31, 1), (37, 1), (167, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37
    · exact prime_167
    · exact prime_229
  · decide +kernel

theorem prime_87739453 : Nat.Prime 87739453 := by
  apply nodeValid_prime [2, 3, 2437207] ⟨87739453, 2, [(2, 2), (3, 2), (2437207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2437207
  · decide +kernel

theorem prime_88373683 : Nat.Prime 88373683 := by
  apply nodeValid_prime [2, 3, 23, 9281] ⟨88373683, 2, [(2, 1), (3, 2), (23, 2), (9281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_9281
  · decide +kernel

theorem prime_91430719 : Nat.Prime 91430719 := by
  apply nodeValid_prime [2, 3, 31, 379, 1297] ⟨91430719, 3, [(2, 1), (3, 1), (31, 1), (379, 1), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_379
    · exact prime_1297
  · decide +kernel

theorem prime_107763379 : Nat.Prime 107763379 := by
  apply nodeValid_prime [2, 3, 31, 137, 4229] ⟨107763379, 2, [(2, 1), (3, 1), (31, 1), (137, 1), (4229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_137
    · exact prime_4229
  · decide +kernel

theorem prime_113320343 : Nat.Prime 113320343 := by
  apply nodeValid_prime [2, 29, 1953799] ⟨113320343, 5, [(2, 1), (29, 1), (1953799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1953799
  · decide +kernel

theorem prime_127669187 : Nat.Prime 127669187 := by
  apply nodeValid_prime [2, 63834593] ⟨127669187, 2, [(2, 1), (63834593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63834593
  · decide +kernel

theorem prime_194620619 : Nat.Prime 194620619 := by
  apply nodeValid_prime [2, 23, 4230883] ⟨194620619, 2, [(2, 1), (23, 1), (4230883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4230883
  · decide +kernel

theorem prime_198662137 : Nat.Prime 198662137 := by
  apply nodeValid_prime [2, 3, 17, 31, 113, 139] ⟨198662137, 10, [(2, 3), (3, 1), (17, 1), (31, 1), (113, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_113
    · exact prime_139
  · decide +kernel

theorem prime_211606333 : Nat.Prime 211606333 := by
  apply nodeValid_prime [2, 3, 7, 59, 42697] ⟨211606333, 2, [(2, 2), (3, 1), (7, 1), (59, 1), (42697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_42697
  · decide +kernel

theorem prime_220363057 : Nat.Prime 220363057 := by
  apply nodeValid_prime [2, 3, 73, 20963] ⟨220363057, 5, [(2, 4), (3, 2), (73, 1), (20963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_20963
  · decide +kernel

theorem prime_300739819 : Nat.Prime 300739819 := by
  apply nodeValid_prime [2, 3, 67, 457, 1637] ⟨300739819, 2, [(2, 1), (3, 1), (67, 1), (457, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_457
    · exact prime_1637
  · decide +kernel

theorem prime_431324539 : Nat.Prime 431324539 := by
  apply nodeValid_prime [2, 3, 71887423] ⟨431324539, 3, [(2, 1), (3, 1), (71887423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71887423
  · decide +kernel

theorem prime_641519561 : Nat.Prime 641519561 := by
  apply nodeValid_prime [2, 5, 11, 1457999] ⟨641519561, 3, [(2, 3), (5, 1), (11, 1), (1457999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1457999
  · decide +kernel

theorem prime_664997917 : Nat.Prime 664997917 := by
  apply nodeValid_prime [2, 3, 11, 5037863] ⟨664997917, 2, [(2, 2), (3, 1), (11, 1), (5037863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5037863
  · decide +kernel

theorem prime_750824551 : Nat.Prime 750824551 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 2003] ⟨750824551, 3, [(2, 1), (3, 2), (5, 2), (7, 2), (17, 1), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_2003
  · decide +kernel

theorem prime_763887269 : Nat.Prime 763887269 := by
  apply nodeValid_prime [2, 157, 257, 4733] ⟨763887269, 2, [(2, 2), (157, 1), (257, 1), (4733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_257
    · exact prime_4733
  · decide +kernel

theorem prime_1096768853 : Nat.Prime 1096768853 := by
  apply nodeValid_prime [2, 281, 757, 1289] ⟨1096768853, 2, [(2, 2), (281, 1), (757, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_757
    · exact prime_1289
  · decide +kernel

theorem prime_1447734889 : Nat.Prime 1447734889 := by
  apply nodeValid_prime [2, 3, 20107429] ⟨1447734889, 7, [(2, 3), (3, 2), (20107429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20107429
  · decide +kernel

theorem prime_2145033083 : Nat.Prime 2145033083 := by
  apply nodeValid_prime [2, 19, 29, 397, 4903] ⟨2145033083, 2, [(2, 1), (19, 1), (29, 1), (397, 1), (4903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_397
    · exact prime_4903
  · decide +kernel

theorem prime_3165600989 : Nat.Prime 3165600989 := by
  apply nodeValid_prime [2, 11, 71945477] ⟨3165600989, 2, [(2, 2), (11, 1), (71945477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71945477
  · decide +kernel

theorem prime_3383325551 : Nat.Prime 3383325551 := by
  apply nodeValid_prime [2, 5, 11, 17, 47, 7699] ⟨3383325551, 7, [(2, 1), (5, 2), (11, 1), (17, 1), (47, 1), (7699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_47
    · exact prime_7699
  · decide +kernel

theorem prime_4046731463 : Nat.Prime 4046731463 := by
  apply nodeValid_prime [2, 43, 443, 106219] ⟨4046731463, 5, [(2, 1), (43, 1), (443, 1), (106219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_443
    · exact prime_106219
  · decide +kernel

theorem prime_4143623431 : Nat.Prime 4143623431 := by
  apply nodeValid_prime [2, 3, 5, 353, 373, 1049] ⟨4143623431, 3, [(2, 1), (3, 1), (5, 1), (353, 1), (373, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
    · exact prime_373
    · exact prime_1049
  · decide +kernel

theorem prime_5536060021 : Nat.Prime 5536060021 := by
  apply nodeValid_prime [2, 3, 5, 19, 167, 359] ⟨5536060021, 6, [(2, 2), (3, 5), (5, 1), (19, 1), (167, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_167
    · exact prime_359
  · decide +kernel

theorem prime_12789907579 : Nat.Prime 12789907579 := by
  apply nodeValid_prime [2, 3, 7, 14501029] ⟨12789907579, 3, [(2, 1), (3, 2), (7, 2), (14501029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14501029
  · decide +kernel

theorem prime_14224766029 : Nat.Prime 14224766029 := by
  apply nodeValid_prime [2, 3, 11, 107763379] ⟨14224766029, 2, [(2, 2), (3, 1), (11, 1), (107763379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_107763379
  · decide +kernel

theorem prime_14477348891 : Nat.Prime 14477348891 := by
  apply nodeValid_prime [2, 5, 1447734889] ⟨14477348891, 2, [(2, 1), (5, 1), (1447734889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1447734889
  · decide +kernel

theorem prime_24762653567 : Nat.Prime 24762653567 := by
  apply nodeValid_prime [2, 7, 23473, 75353] ⟨24762653567, 5, [(2, 1), (7, 1), (23473, 1), (75353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23473
    · exact prime_75353
  · decide +kernel

theorem prime_61023006641 : Nat.Prime 61023006641 := by
  apply nodeValid_prime [2, 5, 89, 8570647] ⟨61023006641, 6, [(2, 4), (5, 1), (89, 1), (8570647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_8570647
  · decide +kernel

theorem prime_72177555721 : Nat.Prime 72177555721 := by
  apply nodeValid_prime [2, 3, 5, 73, 8239447] ⟨72177555721, 14, [(2, 3), (3, 1), (5, 1), (73, 1), (8239447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_8239447
  · decide +kernel

theorem prime_73122136051 : Nat.Prime 73122136051 := by
  apply nodeValid_prime [2, 3, 5, 13537, 36011] ⟨73122136051, 2, [(2, 1), (3, 1), (5, 2), (13537, 1), (36011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13537
    · exact prime_36011
  · decide +kernel

theorem prime_91139387267 : Nat.Prime 91139387267 := by
  apply nodeValid_prime [2, 28123, 1620371] ⟨91139387267, 2, [(2, 1), (28123, 1), (1620371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_28123
    · exact prime_1620371
  · decide +kernel

theorem prime_180182778973 : Nat.Prime 180182778973 := by
  apply nodeValid_prime [2, 3, 7, 2145033083] ⟨180182778973, 2, [(2, 2), (3, 1), (7, 1), (2145033083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2145033083
  · decide +kernel

theorem prime_184921958503 : Nat.Prime 184921958503 := by
  apply nodeValid_prime [2, 3, 19, 593, 11257] ⟨184921958503, 3, [(2, 1), (3, 6), (19, 1), (593, 1), (11257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_593
    · exact prime_11257
  · decide +kernel

theorem prime_367723175951 : Nat.Prime 367723175951 := by
  apply nodeValid_prime [2, 5, 13, 41, 3559, 3877] ⟨367723175951, 38, [(2, 1), (5, 2), (13, 1), (41, 1), (3559, 1), (3877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_3559
    · exact prime_3877
  · decide +kernel

theorem prime_718645451341 : Nat.Prime 718645451341 := by
  apply nodeValid_prime [2, 3, 5, 131, 91430719] ⟨718645451341, 7, [(2, 2), (3, 1), (5, 1), (131, 1), (91430719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_91430719
  · decide +kernel

theorem prime_718645500113 : Nat.Prime 718645500113 := by
  apply nodeValid_prime [2, 97, 347, 1334423] ⟨718645500113, 3, [(2, 4), (97, 1), (347, 1), (1334423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_347
    · exact prime_1334423
  · decide +kernel

theorem prime_718645501433 : Nat.Prime 718645501433 := by
  apply nodeValid_prime [2, 23, 15289, 255457] ⟨718645501433, 3, [(2, 3), (23, 1), (15289, 1), (255457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_15289
    · exact prime_255457
  · decide +kernel

theorem prime_719687774873 : Nat.Prime 719687774873 := by
  apply nodeValid_prime [2, 11, 29027, 281747] ⟨719687774873, 3, [(2, 3), (11, 1), (29027, 1), (281747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29027
    · exact prime_281747
  · decide +kernel

theorem prime_719687775733 : Nat.Prime 719687775733 := by
  apply nodeValid_prime [2, 3, 397, 1451, 104113] ⟨719687775733, 2, [(2, 2), (3, 1), (397, 1), (1451, 1), (104113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_1451
    · exact prime_104113
  · decide +kernel

theorem prime_719687802731 : Nat.Prime 719687802731 := by
  apply nodeValid_prime [2, 5, 13, 5536060021] ⟨719687802731, 2, [(2, 1), (5, 1), (13, 1), (5536060021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_5536060021
  · decide +kernel

theorem prime_720731115751 : Nat.Prime 720731115751 := by
  apply nodeValid_prime [2, 3, 5, 2647, 363043] ⟨720731115751, 3, [(2, 1), (3, 1), (5, 3), (2647, 1), (363043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2647
    · exact prime_363043
  · decide +kernel

theorem prime_720731115893 : Nat.Prime 720731115893 := by
  apply nodeValid_prime [2, 180182778973] ⟨720731115893, 2, [(2, 2), (180182778973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_180182778973
  · decide +kernel

theorem prime_720731170199 : Nat.Prime 720731170199 := by
  apply nodeValid_prime [2, 13, 131, 211606333] ⟨720731170199, 17, [(2, 1), (13, 1), (131, 1), (211606333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_131
    · exact prime_211606333
  · decide +kernel

theorem prime_721775557207 : Nat.Prime 721775557207 := by
  apply nodeValid_prime [2, 3, 11, 17, 3203, 66947] ⟨721775557207, 3, [(2, 1), (3, 2), (11, 1), (17, 1), (3203, 1), (66947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_3203
    · exact prime_66947
  · decide +kernel

theorem prime_721775557211 : Nat.Prime 721775557211 := by
  apply nodeValid_prime [2, 5, 72177555721] ⟨721775557211, 2, [(2, 1), (5, 1), (72177555721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_72177555721
  · decide +kernel

theorem prime_721775565601 : Nat.Prime 721775565601 := by
  apply nodeValid_prime [2, 3, 5, 300739819] ⟨721775565601, 7, [(2, 5), (3, 1), (5, 2), (300739819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_300739819
  · decide +kernel

theorem prime_722820978197 : Nat.Prime 722820978197 := by
  apply nodeValid_prime [2, 23, 41, 1493, 128351] ⟨722820978197, 2, [(2, 2), (23, 1), (41, 1), (1493, 1), (128351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_41
    · exact prime_1493
    · exact prime_128351
  · decide +kernel

theorem prime_722820978967 : Nat.Prime 722820978967 := by
  apply nodeValid_prime [2, 3, 619, 194620619] ⟨722820978967, 5, [(2, 1), (3, 1), (619, 1), (194620619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
    · exact prime_194620619
  · decide +kernel

theorem prime_722820989249 : Nat.Prime 722820989249 := by
  apply nodeValid_prime [2, 47, 1607, 149533] ⟨722820989249, 3, [(2, 6), (47, 1), (1607, 1), (149533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1607
    · exact prime_149533
  · decide +kernel

theorem prime_723867442981 : Nat.Prime 723867442981 := by
  apply nodeValid_prime [2, 3, 5, 11, 1096768853] ⟨723867442981, 10, [(2, 2), (3, 1), (5, 1), (11, 1), (1096768853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1096768853
  · decide +kernel

theorem prime_723867443207 : Nat.Prime 723867443207 := by
  apply nodeValid_prime [2, 136979, 2642257] ⟨723867443207, 5, [(2, 1), (136979, 1), (2642257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_136979
    · exact prime_2642257
  · decide +kernel

theorem prime_723867444551 : Nat.Prime 723867444551 := by
  apply nodeValid_prime [2, 5, 14477348891] ⟨723867444551, 11, [(2, 1), (5, 2), (14477348891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14477348891
  · decide +kernel

theorem prime_724914919721 : Nat.Prime 724914919721 := by
  apply nodeValid_prime [2, 5, 51869, 349397] ⟨724914919721, 3, [(2, 3), (5, 1), (51869, 1), (349397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_51869
    · exact prime_349397
  · decide +kernel

theorem prime_724914966953 : Nat.Prime 724914966953 := by
  apply nodeValid_prime [2, 11, 673, 12240223] ⟨724914966953, 6, [(2, 3), (11, 1), (673, 1), (12240223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_673
    · exact prime_12240223
  · decide +kernel

theorem prime_724914967409 : Nat.Prime 724914967409 := by
  apply nodeValid_prime [2, 4391, 10318193] ⟨724914967409, 3, [(2, 4), (4391, 1), (10318193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4391
    · exact prime_10318193
  · decide +kernel

theorem prime_725963418781 : Nat.Prime 725963418781 := by
  apply nodeValid_prime [2, 3, 5, 37, 167, 863, 2269] ⟨725963418781, 6, [(2, 2), (3, 1), (5, 1), (37, 1), (167, 1), (863, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_167
    · exact prime_863
    · exact prime_2269
  · decide +kernel

theorem prime_725963418811 : Nat.Prime 725963418811 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 20216191] ⟨725963418811, 10, [(2, 1), (3, 3), (5, 1), (7, 1), (19, 1), (20216191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_20216191
  · decide +kernel

theorem prime_725963419387 : Nat.Prime 725963419387 := by
  apply nodeValid_prime [2, 3, 149, 211, 241, 5323] ⟨725963419387, 13, [(2, 1), (3, 2), (149, 1), (211, 1), (241, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_211
    · exact prime_241
    · exact prime_5323
  · decide +kernel

theorem prime_727012915099 : Nat.Prime 727012915099 := by
  apply nodeValid_prime [2, 3, 17, 269, 1481, 17891] ⟨727012915099, 2, [(2, 1), (3, 1), (17, 1), (269, 1), (1481, 1), (17891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_269
    · exact prime_1481
    · exact prime_17891
  · decide +kernel

theorem prime_727012917343 : Nat.Prime 727012917343 := by
  apply nodeValid_prime [2, 3, 17, 37, 487, 43951] ⟨727012917343, 3, [(2, 1), (3, 3), (17, 1), (37, 1), (487, 1), (43951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_487
    · exact prime_43951
  · decide +kernel

theorem prime_727012946551 : Nat.Prime 727012946551 := by
  apply nodeValid_prime [2, 3, 5, 11, 29, 257, 59119] ⟨727012946551, 21, [(2, 1), (3, 1), (5, 2), (11, 1), (29, 1), (257, 1), (59119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_257
    · exact prime_59119
  · decide +kernel

theorem prime_728063484557 : Nat.Prime 728063484557 := by
  apply nodeValid_prime [2, 15647, 11632637] ⟨728063484557, 2, [(2, 2), (15647, 1), (11632637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15647
    · exact prime_11632637
  · decide +kernel

theorem prime_728063485351 : Nat.Prime 728063485351 := by
  apply nodeValid_prime [2, 3, 5, 1289, 3765521] ⟨728063485351, 3, [(2, 1), (3, 1), (5, 2), (1289, 1), (3765521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1289
    · exact prime_3765521
  · decide +kernel

theorem prime_728063505371 : Nat.Prime 728063505371 := by
  apply nodeValid_prime [2, 5, 238321, 305497] ⟨728063505371, 6, [(2, 1), (5, 1), (238321, 1), (305497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_238321
    · exact prime_305497
  · decide +kernel

theorem prime_729115094153 : Nat.Prime 729115094153 := by
  apply nodeValid_prime [2, 3517, 25913957] ⟨729115094153, 3, [(2, 3), (3517, 1), (25913957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3517
    · exact prime_25913957
  · decide +kernel

theorem prime_729115097981 : Nat.Prime 729115097981 := by
  apply nodeValid_prime [2, 5, 563, 811, 79843] ⟨729115097981, 2, [(2, 2), (5, 1), (563, 1), (811, 1), (79843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_563
    · exact prime_811
    · exact prime_79843
  · decide +kernel

theorem prime_729115098137 : Nat.Prime 729115098137 := by
  apply nodeValid_prime [2, 91139387267] ⟨729115098137, 3, [(2, 3), (91139387267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_91139387267
  · decide +kernel

theorem prime_730167712867 : Nat.Prime 730167712867 := by
  apply nodeValid_prime [2, 3, 61, 664997917] ⟨730167712867, 2, [(2, 1), (3, 2), (61, 1), (664997917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_664997917
  · decide +kernel

theorem prime_730167727867 : Nat.Prime 730167727867 := by
  apply nodeValid_prime [2, 3, 19, 73, 87739453] ⟨730167727867, 2, [(2, 1), (3, 1), (19, 1), (73, 1), (87739453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_73
    · exact prime_87739453
  · decide +kernel

theorem prime_730167727981 : Nat.Prime 730167727981 := by
  apply nodeValid_prime [2, 3, 5, 19, 8521, 75167] ⟨730167727981, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (8521, 1), (75167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_8521
    · exact prime_75167
  · decide +kernel

theorem prime_731221360393 : Nat.Prime 731221360393 := by
  apply nodeValid_prime [2, 3, 26833, 1135451] ⟨731221360393, 5, [(2, 3), (3, 1), (26833, 1), (1135451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26833
    · exact prime_1135451
  · decide +kernel

theorem prime_731221360511 : Nat.Prime 731221360511 := by
  apply nodeValid_prime [2, 5, 73122136051] ⟨731221360511, 11, [(2, 1), (5, 1), (73122136051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73122136051
  · decide +kernel

theorem prime_731221367479 : Nat.Prime 731221367479 := by
  apply nodeValid_prime [2, 3, 7, 241, 72240799] ⟨731221367479, 6, [(2, 1), (3, 1), (7, 1), (241, 1), (72240799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_241
    · exact prime_72240799
  · decide +kernel

theorem prime_732276056467 : Nat.Prime 732276056467 := by
  apply nodeValid_prime [2, 3, 359, 113320343] ⟨732276056467, 2, [(2, 1), (3, 2), (359, 1), (113320343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_113320343
  · decide +kernel

theorem prime_732276079693 : Nat.Prime 732276079693 := by
  apply nodeValid_prime [2, 3, 61023006641] ⟨732276079693, 2, [(2, 2), (3, 1), (61023006641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61023006641
  · decide +kernel

theorem prime_732276080749 : Nat.Prime 732276080749 := by
  apply nodeValid_prime [2, 3, 89, 977, 77977] ⟨732276080749, 2, [(2, 2), (3, 3), (89, 1), (977, 1), (77977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_977
    · exact prime_77977
  · decide +kernel

theorem prime_733331778241 : Nat.Prime 733331778241 := by
  apply nodeValid_prime [2, 3, 5, 763887269] ⟨733331778241, 7, [(2, 6), (3, 1), (5, 1), (763887269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_763887269
  · decide +kernel

theorem prime_733331810129 : Nat.Prime 733331810129 := by
  apply nodeValid_prime [2, 359, 127669187] ⟨733331810129, 3, [(2, 4), (359, 1), (127669187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_127669187
  · decide +kernel

theorem prime_733331810147 : Nat.Prime 733331810147 := by
  apply nodeValid_prime [2, 13, 17449, 1616429] ⟨733331810147, 2, [(2, 1), (13, 1), (17449, 1), (1616429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17449
    · exact prime_1616429
  · decide +kernel

theorem prime_734388459323 : Nat.Prime 734388459323 := by
  apply nodeValid_prime [2, 7, 23, 41, 2153, 3691] ⟨734388459323, 5, [(2, 1), (7, 2), (23, 1), (41, 1), (2153, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_41
    · exact prime_2153
    · exact prime_3691
  · decide +kernel

theorem prime_734388459599 : Nat.Prime 734388459599 := by
  apply nodeValid_prime [2, 23, 43, 3823, 97117] ⟨734388459599, 7, [(2, 1), (23, 1), (43, 1), (3823, 1), (97117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
    · exact prime_3823
    · exact prime_97117
  · decide +kernel

theorem prime_734388534199 : Nat.Prime 734388534199 := by
  apply nodeValid_prime [2, 3, 11, 15467, 239803] ⟨734388534199, 6, [(2, 1), (3, 2), (11, 1), (15467, 1), (239803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_15467
    · exact prime_239803
  · decide +kernel

theorem prime_735446316263 : Nat.Prime 735446316263 := by
  apply nodeValid_prime [2, 7, 23, 1823, 1252877] ⟨735446316263, 7, [(2, 1), (7, 1), (23, 1), (1823, 1), (1252877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_1823
    · exact prime_1252877
  · decide +kernel

theorem prime_735446351903 : Nat.Prime 735446351903 := by
  apply nodeValid_prime [2, 367723175951] ⟨735446351903, 5, [(2, 1), (367723175951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_367723175951
  · decide +kernel

theorem prime_735446352593 : Nat.Prime 735446352593 := by
  apply nodeValid_prime [2, 7, 19, 47, 7353287] ⟨735446352593, 3, [(2, 4), (7, 1), (19, 1), (47, 1), (7353287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_47
    · exact prime_7353287
  · decide +kernel

theorem prime_736505118131 : Nat.Prime 736505118131 := by
  apply nodeValid_prime [2, 5, 19, 149, 1607, 16189] ⟨736505118131, 2, [(2, 1), (5, 1), (19, 1), (149, 1), (1607, 1), (16189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_149
    · exact prime_1607
    · exact prime_16189
  · decide +kernel

theorem prime_736505118509 : Nat.Prime 736505118509 := by
  apply nodeValid_prime [2, 8117, 22684031] ⟨736505118509, 2, [(2, 2), (8117, 1), (22684031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8117
    · exact prime_22684031
  · decide +kernel

theorem prime_736505126267 : Nat.Prime 736505126267 := by
  apply nodeValid_prime [2, 7, 13, 4046731463] ⟨736505126267, 2, [(2, 1), (7, 1), (13, 1), (4046731463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_4046731463
  · decide +kernel

theorem prime_737564961691 : Nat.Prime 737564961691 := by
  apply nodeValid_prime [2, 3, 5, 19, 431324539] ⟨737564961691, 2, [(2, 1), (3, 2), (5, 1), (19, 1), (431324539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_431324539
  · decide +kernel

theorem prime_737564970119 : Nat.Prime 737564970119 := by
  apply nodeValid_prime [2, 109, 3383325551] ⟨737564970119, 23, [(2, 1), (109, 1), (3383325551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_3383325551
  · decide +kernel

theorem prime_737564970719 : Nat.Prime 737564970719 := by
  apply nodeValid_prime [2, 89, 4143623431] ⟨737564970719, 11, [(2, 1), (89, 1), (4143623431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_4143623431
  · decide +kernel

theorem prime_738625825367 : Nat.Prime 738625825367 := by
  apply nodeValid_prime [2, 11, 13, 198662137] ⟨738625825367, 5, [(2, 1), (11, 1), (13, 2), (198662137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_198662137
  · decide +kernel

theorem prime_738625902073 : Nat.Prime 738625902073 := by
  apply nodeValid_prime [2, 3, 547, 1283, 43853] ⟨738625902073, 5, [(2, 3), (3, 1), (547, 1), (1283, 1), (43853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_547
    · exact prime_1283
    · exact prime_43853
  · decide +kernel

theorem prime_738625902337 : Nat.Prime 738625902337 := by
  apply nodeValid_prime [2, 3, 7, 45797737] ⟨738625902337, 5, [(2, 8), (3, 2), (7, 1), (45797737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_45797737
  · decide +kernel

theorem prime_739687726711 : Nat.Prime 739687726711 := by
  apply nodeValid_prime [2, 3, 5, 31, 88373683] ⟨739687726711, 12, [(2, 1), (3, 3), (5, 1), (31, 1), (88373683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_88373683
  · decide +kernel

theorem prime_739687833509 : Nat.Prime 739687833509 := by
  apply nodeValid_prime [2, 13, 14224766029] ⟨739687833509, 2, [(2, 2), (13, 1), (14224766029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_14224766029
  · decide +kernel

theorem prime_739687834013 : Nat.Prime 739687834013 := by
  apply nodeValid_prime [2, 184921958503] ⟨739687834013, 2, [(2, 2), (184921958503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_184921958503
  · decide +kernel

theorem prime_740750630329 : Nat.Prime 740750630329 := by
  apply nodeValid_prime [2, 3, 571, 641, 28109] ⟨740750630329, 7, [(2, 3), (3, 2), (571, 1), (641, 1), (28109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
    · exact prime_641
    · exact prime_28109
  · decide +kernel

theorem prime_740750631427 : Nat.Prime 740750631427 := by
  apply nodeValid_prime [2, 3, 13, 3165600989] ⟨740750631427, 2, [(2, 1), (3, 2), (13, 1), (3165600989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3165600989
  · decide +kernel

theorem prime_740750667431 : Nat.Prime 740750667431 := by
  apply nodeValid_prime [2, 5, 215939, 343037] ⟨740750667431, 11, [(2, 1), (5, 1), (215939, 1), (343037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_215939
    · exact prime_343037
  · decide +kernel

theorem prime_741814639583 : Nat.Prime 741814639583 := by
  apply nodeValid_prime [2, 29, 12789907579] ⟨741814639583, 5, [(2, 1), (29, 1), (12789907579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_12789907579
  · decide +kernel

theorem prime_741814655357 : Nat.Prime 741814655357 := by
  apply nodeValid_prime [2, 3691, 6619, 7591] ⟨741814655357, 2, [(2, 2), (3691, 1), (6619, 1), (7591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3691
    · exact prime_6619
    · exact prime_7591
  · decide +kernel

theorem prime_741814656389 : Nat.Prime 741814656389 := by
  apply nodeValid_prime [2, 13, 19, 750824551] ⟨741814656389, 2, [(2, 2), (13, 1), (19, 1), (750824551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_750824551
  · decide +kernel

theorem prime_742879606159 : Nat.Prime 742879606159 := by
  apply nodeValid_prime [2, 3, 7727, 5341153] ⟨742879606159, 11, [(2, 1), (3, 2), (7727, 1), (5341153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7727
    · exact prime_5341153
  · decide +kernel

theorem prime_742879607011 : Nat.Prime 742879607011 := by
  apply nodeValid_prime [2, 3, 5, 24762653567] ⟨742879607011, 11, [(2, 1), (3, 1), (5, 1), (24762653567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_24762653567
  · decide +kernel

theorem prime_742879651639 : Nat.Prime 742879651639 := by
  apply nodeValid_prime [2, 3, 193, 641519561] ⟨742879651639, 6, [(2, 1), (3, 1), (193, 1), (641519561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_641519561
  · decide +kernel

theorem prime_743945676641 : Nat.Prime 743945676641 := by
  apply nodeValid_prime [2, 5, 53, 87729443] ⟨743945676641, 3, [(2, 5), (5, 1), (53, 1), (87729443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_87729443
  · decide +kernel

theorem prime_743945680433 : Nat.Prime 743945680433 := by
  apply nodeValid_prime [2, 211, 220363057] ⟨743945680433, 3, [(2, 4), (211, 1), (220363057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_220363057
  · decide +kernel

theorem prime_743945703887 : Nat.Prime 743945703887 := by
  apply nodeValid_prime [2, 7, 11, 29, 569, 292759] ⟨743945703887, 5, [(2, 1), (7, 1), (11, 1), (29, 1), (569, 1), (292759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_569
    · exact prime_292759
  · decide +kernel

end Sude.Lucas.Generated
