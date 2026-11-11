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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4217 : Nat.Prime 4217 := by
  apply nodeValid_prime [2, 17, 31] ⟨4217, 3, [(2, 3), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_4373 : Nat.Prime 4373 := by
  apply nodeValid_prime [2, 1093] ⟨4373, 2, [(2, 2), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1093
  · decide +kernel

theorem prime_4451 : Nat.Prime 4451 := by
  apply nodeValid_prime [2, 5, 89] ⟨4451, 2, [(2, 1), (5, 2), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_4639 : Nat.Prime 4639 := by
  apply nodeValid_prime [2, 3, 773] ⟨4639, 3, [(2, 1), (3, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_773
  · decide +kernel

theorem prime_4751 : Nat.Prime 4751 := by
  apply nodeValid_prime [2, 5, 19] ⟨4751, 19, [(2, 1), (5, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_6337 : Nat.Prime 6337 := by
  apply nodeValid_prime [2, 3, 11] ⟨6337, 10, [(2, 6), (3, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_6823 : Nat.Prime 6823 := by
  apply nodeValid_prime [2, 3, 379] ⟨6823, 3, [(2, 1), (3, 2), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
  · decide +kernel

theorem prime_8219 : Nat.Prime 8219 := by
  apply nodeValid_prime [2, 7, 587] ⟨8219, 2, [(2, 1), (7, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_587
  · decide +kernel

theorem prime_8369 : Nat.Prime 8369 := by
  apply nodeValid_prime [2, 523] ⟨8369, 3, [(2, 4), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_523
  · decide +kernel

theorem prime_8623 : Nat.Prime 8623 := by
  apply nodeValid_prime [2, 3, 479] ⟨8623, 3, [(2, 1), (3, 2), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
  · decide +kernel

theorem prime_8747 : Nat.Prime 8747 := by
  apply nodeValid_prime [2, 4373] ⟨8747, 2, [(2, 1), (4373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4373
  · decide +kernel

theorem prime_8941 : Nat.Prime 8941 := by
  apply nodeValid_prime [2, 3, 5, 149] ⟨8941, 6, [(2, 2), (3, 1), (5, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
  · decide +kernel

theorem prime_8969 : Nat.Prime 8969 := by
  apply nodeValid_prime [2, 19, 59] ⟨8969, 3, [(2, 3), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_9829 : Nat.Prime 9829 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨9829, 10, [(2, 2), (3, 3), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_10513 : Nat.Prime 10513 := by
  apply nodeValid_prime [2, 3, 73] ⟨10513, 7, [(2, 4), (3, 2), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_13627 : Nat.Prime 13627 := by
  apply nodeValid_prime [2, 3, 757] ⟨13627, 2, [(2, 1), (3, 2), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_757
  · decide +kernel

theorem prime_23473 : Nat.Prime 23473 := by
  apply nodeValid_prime [2, 3, 163] ⟨23473, 5, [(2, 4), (3, 2), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
  · decide +kernel

theorem prime_24169 : Nat.Prime 24169 := by
  apply nodeValid_prime [2, 3, 19, 53] ⟨24169, 11, [(2, 3), (3, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_25349 : Nat.Prime 25349 := by
  apply nodeValid_prime [2, 6337] ⟨25349, 2, [(2, 2), (6337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6337
  · decide +kernel

theorem prime_26293 : Nat.Prime 26293 := by
  apply nodeValid_prime [2, 3, 7, 313] ⟨26293, 6, [(2, 2), (3, 1), (7, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_313
  · decide +kernel

theorem prime_26431 : Nat.Prime 26431 := by
  apply nodeValid_prime [2, 3, 5, 881] ⟨26431, 3, [(2, 1), (3, 1), (5, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_881
  · decide +kernel

theorem prime_26437 : Nat.Prime 26437 := by
  apply nodeValid_prime [2, 3, 2203] ⟨26437, 5, [(2, 2), (3, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2203
  · decide +kernel

theorem prime_28793 : Nat.Prime 28793 := by
  apply nodeValid_prime [2, 59, 61] ⟨28793, 3, [(2, 3), (59, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_61
  · decide +kernel

theorem prime_30211 : Nat.Prime 30211 := by
  apply nodeValid_prime [2, 3, 5, 19, 53] ⟨30211, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_38447 : Nat.Prime 38447 := by
  apply nodeValid_prime [2, 47, 409] ⟨38447, 5, [(2, 1), (47, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_409
  · decide +kernel

theorem prime_41647 : Nat.Prime 41647 := by
  apply nodeValid_prime [2, 3, 11, 631] ⟨41647, 3, [(2, 1), (3, 1), (11, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_631
  · decide +kernel

theorem prime_43991 : Nat.Prime 43991 := by
  apply nodeValid_prime [2, 5, 53, 83] ⟨43991, 17, [(2, 1), (5, 1), (53, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_83
  · decide +kernel

theorem prime_46301 : Nat.Prime 46301 := by
  apply nodeValid_prime [2, 5, 463] ⟨46301, 2, [(2, 2), (5, 2), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_463
  · decide +kernel

theorem prime_47147 : Nat.Prime 47147 := by
  apply nodeValid_prime [2, 11, 2143] ⟨47147, 2, [(2, 1), (11, 1), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2143
  · decide +kernel

theorem prime_47269 : Nat.Prime 47269 := by
  apply nodeValid_prime [2, 3, 13, 101] ⟨47269, 6, [(2, 2), (3, 2), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_51329 : Nat.Prime 51329 := by
  apply nodeValid_prime [2, 401] ⟨51329, 3, [(2, 7), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_401
  · decide +kernel

theorem prime_51913 : Nat.Prime 51913 := by
  apply nodeValid_prime [2, 3, 7, 103] ⟨51913, 10, [(2, 3), (3, 2), (7, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_52391 : Nat.Prime 52391 := by
  apply nodeValid_prime [2, 5, 13, 31] ⟨52391, 11, [(2, 1), (5, 1), (13, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_53101 : Nat.Prime 53101 := by
  apply nodeValid_prime [2, 3, 5, 59] ⟨53101, 2, [(2, 2), (3, 2), (5, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_55541 : Nat.Prime 55541 := by
  apply nodeValid_prime [2, 5, 2777] ⟨55541, 2, [(2, 2), (5, 1), (2777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2777
  · decide +kernel

theorem prime_55697 : Nat.Prime 55697 := by
  apply nodeValid_prime [2, 59] ⟨55697, 3, [(2, 4), (59, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59
  · decide +kernel

theorem prime_57587 : Nat.Prime 57587 := by
  apply nodeValid_prime [2, 28793] ⟨57587, 2, [(2, 1), (28793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28793
  · decide +kernel

theorem prime_59797 : Nat.Prime 59797 := by
  apply nodeValid_prime [2, 3, 11, 151] ⟨59797, 2, [(2, 2), (3, 2), (11, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_151
  · decide +kernel

theorem prime_67033 : Nat.Prime 67033 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨67033, 5, [(2, 3), (3, 2), (7, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_77267 : Nat.Prime 77267 := by
  apply nodeValid_prime [2, 7, 5519] ⟨77267, 2, [(2, 1), (7, 1), (5519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5519
  · decide +kernel

theorem prime_78193 : Nat.Prime 78193 := by
  apply nodeValid_prime [2, 3, 181] ⟨78193, 5, [(2, 4), (3, 3), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel

theorem prime_78779 : Nat.Prime 78779 := by
  apply nodeValid_prime [2, 7, 17, 331] ⟨78779, 2, [(2, 1), (7, 1), (17, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_331
  · decide +kernel

theorem prime_80491 : Nat.Prime 80491 := by
  apply nodeValid_prime [2, 3, 5, 2683] ⟨80491, 2, [(2, 1), (3, 1), (5, 1), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2683
  · decide +kernel

theorem prime_94057 : Nat.Prime 94057 := by
  apply nodeValid_prime [2, 3, 3919] ⟨94057, 7, [(2, 3), (3, 1), (3919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3919
  · decide +kernel

theorem prime_98479 : Nat.Prime 98479 := by
  apply nodeValid_prime [2, 3, 5471] ⟨98479, 3, [(2, 1), (3, 2), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5471
  · decide +kernel

theorem prime_98887 : Nat.Prime 98887 := by
  apply nodeValid_prime [2, 3, 16481] ⟨98887, 3, [(2, 1), (3, 1), (16481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16481
  · decide +kernel

theorem prime_101921 : Nat.Prime 101921 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨101921, 11, [(2, 5), (5, 1), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_105601 : Nat.Prime 105601 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨105601, 17, [(2, 7), (3, 1), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_116177 : Nat.Prime 116177 := by
  apply nodeValid_prime [2, 53, 137] ⟨116177, 3, [(2, 4), (53, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_137
  · decide +kernel

theorem prime_130987 : Nat.Prime 130987 := by
  apply nodeValid_prime [2, 3, 19, 383] ⟨130987, 5, [(2, 1), (3, 2), (19, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_383
  · decide +kernel

theorem prime_131771 : Nat.Prime 131771 := by
  apply nodeValid_prime [2, 5, 13177] ⟨131771, 2, [(2, 1), (5, 1), (13177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13177
  · decide +kernel

theorem prime_157559 : Nat.Prime 157559 := by
  apply nodeValid_prime [2, 78779] ⟨157559, 17, [(2, 1), (78779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_78779
  · decide +kernel

theorem prime_174257 : Nat.Prime 174257 := by
  apply nodeValid_prime [2, 10891] ⟨174257, 3, [(2, 4), (10891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10891
  · decide +kernel

theorem prime_176021 : Nat.Prime 176021 := by
  apply nodeValid_prime [2, 5, 13, 677] ⟨176021, 2, [(2, 2), (5, 1), (13, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_677
  · decide +kernel

theorem prime_179381 : Nat.Prime 179381 := by
  apply nodeValid_prime [2, 5, 8969] ⟨179381, 2, [(2, 2), (5, 1), (8969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8969
  · decide +kernel

theorem prime_203843 : Nat.Prime 203843 := by
  apply nodeValid_prime [2, 101921] ⟨203843, 2, [(2, 1), (101921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_101921
  · decide +kernel

theorem prime_207653 : Nat.Prime 207653 := by
  apply nodeValid_prime [2, 51913] ⟨207653, 2, [(2, 2), (51913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_51913
  · decide +kernel

theorem prime_220327 : Nat.Prime 220327 := by
  apply nodeValid_prime [2, 3, 36721] ⟨220327, 3, [(2, 1), (3, 1), (36721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36721
  · decide +kernel

theorem prime_250501 : Nat.Prime 250501 := by
  apply nodeValid_prime [2, 3, 5, 167] ⟨250501, 2, [(2, 2), (3, 1), (5, 3), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
  · decide +kernel

theorem prime_253901 : Nat.Prime 253901 := by
  apply nodeValid_prime [2, 5, 2539] ⟨253901, 2, [(2, 2), (5, 2), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2539
  · decide +kernel

theorem prime_266369 : Nat.Prime 266369 := by
  apply nodeValid_prime [2, 2081] ⟨266369, 3, [(2, 7), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2081
  · decide +kernel

theorem prime_351929 : Nat.Prime 351929 := by
  apply nodeValid_prime [2, 43991] ⟨351929, 3, [(2, 3), (43991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43991
  · decide +kernel

theorem prime_375569 : Nat.Prime 375569 := by
  apply nodeValid_prime [2, 23473] ⟨375569, 3, [(2, 4), (23473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23473
  · decide +kernel

theorem prime_438017 : Nat.Prime 438017 := by
  apply nodeValid_prime [2, 29, 59] ⟨438017, 3, [(2, 8), (29, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_59
  · decide +kernel

theorem prime_635147 : Nat.Prime 635147 := by
  apply nodeValid_prime [2, 227, 1399] ⟨635147, 2, [(2, 1), (227, 1), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_1399
  · decide +kernel

theorem prime_636539 : Nat.Prime 636539 := by
  apply nodeValid_prime [2, 7, 19, 2393] ⟨636539, 6, [(2, 1), (7, 1), (19, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_2393
  · decide +kernel

theorem prime_665789 : Nat.Prime 665789 := by
  apply nodeValid_prime [2, 17, 9791] ⟨665789, 2, [(2, 2), (17, 1), (9791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9791
  · decide +kernel

theorem prime_697601 : Nat.Prime 697601 := by
  apply nodeValid_prime [2, 5, 109] ⟨697601, 3, [(2, 8), (5, 2), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_749429 : Nat.Prime 749429 := by
  apply nodeValid_prime [2, 17, 103, 107] ⟨749429, 2, [(2, 2), (17, 1), (103, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
    · exact prime_107
  · decide +kernel

theorem prime_785923 : Nat.Prime 785923 := by
  apply nodeValid_prime [2, 3, 130987] ⟨785923, 2, [(2, 1), (3, 1), (130987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130987
  · decide +kernel

theorem prime_794039 : Nat.Prime 794039 := by
  apply nodeValid_prime [2, 7, 43, 1319] ⟨794039, 11, [(2, 1), (7, 1), (43, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_1319
  · decide +kernel

theorem prime_805463 : Nat.Prime 805463 := by
  apply nodeValid_prime [2, 7, 8219] ⟨805463, 5, [(2, 1), (7, 2), (8219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8219
  · decide +kernel

theorem prime_965893 : Nat.Prime 965893 := by
  apply nodeValid_prime [2, 3, 80491] ⟨965893, 2, [(2, 2), (3, 1), (80491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80491
  · decide +kernel

theorem prime_1185787 : Nat.Prime 1185787 := by
  apply nodeValid_prime [2, 3, 7, 3137] ⟨1185787, 3, [(2, 1), (3, 3), (7, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3137
  · decide +kernel

theorem prime_1265281 : Nat.Prime 1265281 := by
  apply nodeValid_prime [2, 3, 5, 659] ⟨1265281, 14, [(2, 7), (3, 1), (5, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_659
  · decide +kernel

theorem prime_1828423 : Nat.Prime 1828423 := by
  apply nodeValid_prime [2, 3, 157, 647] ⟨1828423, 3, [(2, 1), (3, 2), (157, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_647
  · decide +kernel

theorem prime_2574653 : Nat.Prime 2574653 := by
  apply nodeValid_prime [2, 19, 1783] ⟨2574653, 2, [(2, 2), (19, 2), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1783
  · decide +kernel

theorem prime_2632099 : Nat.Prime 2632099 := by
  apply nodeValid_prime [2, 3, 7, 29, 2161] ⟨2632099, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_2161
  · decide +kernel

theorem prime_2933897 : Nat.Prime 2933897 := by
  apply nodeValid_prime [2, 7, 52391] ⟨2933897, 5, [(2, 3), (7, 1), (52391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_52391
  · decide +kernel

theorem prime_3568141 : Nat.Prime 3568141 := by
  apply nodeValid_prime [2, 3, 5, 43, 461] ⟨3568141, 6, [(2, 2), (3, 2), (5, 1), (43, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_461
  · decide +kernel

theorem prime_5374307 : Nat.Prime 5374307 := by
  apply nodeValid_prime [2, 7, 53, 7243] ⟨5374307, 2, [(2, 1), (7, 1), (53, 1), (7243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_7243
  · decide +kernel

theorem prime_6076337 : Nat.Prime 6076337 := by
  apply nodeValid_prime [2, 7, 227, 239] ⟨6076337, 3, [(2, 4), (7, 1), (227, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
    · exact prime_239
  · decide +kernel

theorem prime_7898669 : Nat.Prime 7898669 := by
  apply nodeValid_prime [2, 229, 8623] ⟨7898669, 2, [(2, 2), (229, 1), (8623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_8623
  · decide +kernel

theorem prime_8306509 : Nat.Prime 8306509 := by
  apply nodeValid_prime [2, 3, 7, 98887] ⟨8306509, 2, [(2, 2), (3, 1), (7, 1), (98887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_98887
  · decide +kernel

theorem prime_9567521 : Nat.Prime 9567521 := by
  apply nodeValid_prime [2, 5, 59797] ⟨9567521, 3, [(2, 5), (5, 1), (59797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59797
  · decide +kernel

theorem prime_10821389 : Nat.Prime 10821389 := by
  apply nodeValid_prime [2, 1583, 1709] ⟨10821389, 2, [(2, 2), (1583, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1583
    · exact prime_1709
  · decide +kernel

theorem prime_10970539 : Nat.Prime 10970539 := by
  apply nodeValid_prime [2, 3, 1828423] ⟨10970539, 2, [(2, 1), (3, 1), (1828423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1828423
  · decide +kernel

theorem prime_11267071 : Nat.Prime 11267071 := by
  apply nodeValid_prime [2, 3, 5, 375569] ⟨11267071, 3, [(2, 1), (3, 1), (5, 1), (375569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_375569
  · decide +kernel

theorem prime_13117781 : Nat.Prime 13117781 := by
  apply nodeValid_prime [2, 5, 13, 3881] ⟨13117781, 2, [(2, 2), (5, 1), (13, 2), (3881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_3881
  · decide +kernel

theorem prime_15258739 : Nat.Prime 15258739 := by
  apply nodeValid_prime [2, 3, 11, 47, 4919] ⟨15258739, 2, [(2, 1), (3, 1), (11, 1), (47, 1), (4919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_4919
  · decide +kernel

theorem prime_15484877 : Nat.Prime 15484877 := by
  apply nodeValid_prime [2, 11, 351929] ⟨15484877, 2, [(2, 2), (11, 1), (351929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_351929
  · decide +kernel

theorem prime_15567719 : Nat.Prime 15567719 := by
  apply nodeValid_prime [2, 67, 116177] ⟨15567719, 13, [(2, 1), (67, 1), (116177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_116177
  · decide +kernel

theorem prime_17607943 : Nat.Prime 17607943 := by
  apply nodeValid_prime [2, 3, 11, 41, 241] ⟨17607943, 3, [(2, 1), (3, 4), (11, 1), (41, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_241
  · decide +kernel

theorem prime_19352083 : Nat.Prime 19352083 := by
  apply nodeValid_prime [2, 3, 41, 97, 811] ⟨19352083, 2, [(2, 1), (3, 1), (41, 1), (97, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_97
    · exact prime_811
  · decide +kernel

theorem prime_28931411 : Nat.Prime 28931411 := by
  apply nodeValid_prime [2, 5, 37, 78193] ⟨28931411, 2, [(2, 1), (5, 1), (37, 1), (78193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_78193
  · decide +kernel

theorem prime_39955351 : Nat.Prime 39955351 := by
  apply nodeValid_prime [2, 3, 5, 266369] ⟨39955351, 3, [(2, 1), (3, 1), (5, 2), (266369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_266369
  · decide +kernel

theorem prime_47000879 : Nat.Prime 47000879 := by
  apply nodeValid_prime [2, 37, 635147] ⟨47000879, 7, [(2, 1), (37, 1), (635147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_635147
  · decide +kernel

theorem prime_49158409 : Nat.Prime 49158409 := by
  apply nodeValid_prime [2, 3, 13, 157559] ⟨49158409, 7, [(2, 3), (3, 1), (13, 1), (157559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_157559
  · decide +kernel

theorem prime_57862823 : Nat.Prime 57862823 := by
  apply nodeValid_prime [2, 28931411] ⟨57862823, 5, [(2, 1), (28931411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28931411
  · decide +kernel

theorem prime_77564351 : Nat.Prime 77564351 := by
  apply nodeValid_prime [2, 5, 59, 26293] ⟨77564351, 7, [(2, 1), (5, 2), (59, 1), (26293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_26293
  · decide +kernel

theorem prime_98842829 : Nat.Prime 98842829 := by
  apply nodeValid_prime [2, 7, 17, 207653] ⟨98842829, 2, [(2, 2), (7, 1), (17, 1), (207653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_207653
  · decide +kernel

theorem prime_148116497 : Nat.Prime 148116497 := by
  apply nodeValid_prime [2, 11, 199, 4229] ⟨148116497, 3, [(2, 4), (11, 1), (199, 1), (4229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_199
    · exact prime_4229
  · decide +kernel

theorem prime_155128703 : Nat.Prime 155128703 := by
  apply nodeValid_prime [2, 77564351] ⟨155128703, 5, [(2, 1), (77564351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_77564351
  · decide +kernel

theorem prime_209593597 : Nat.Prime 209593597 := by
  apply nodeValid_prime [2, 3, 1777, 9829] ⟨209593597, 6, [(2, 2), (3, 1), (1777, 1), (9829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1777
    · exact prime_9829
  · decide +kernel

theorem prime_235067827 : Nat.Prime 235067827 := by
  apply nodeValid_prime [2, 3, 7, 53, 105601] ⟨235067827, 3, [(2, 1), (3, 1), (7, 1), (53, 1), (105601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_105601
  · decide +kernel

theorem prime_253285973 : Nat.Prime 253285973 := by
  apply nodeValid_prime [2, 353, 179381] ⟨253285973, 2, [(2, 2), (353, 1), (179381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_179381
  · decide +kernel

theorem prime_291012349 : Nat.Prime 291012349 := by
  apply nodeValid_prime [2, 3, 11, 193, 11423] ⟨291012349, 2, [(2, 2), (3, 1), (11, 1), (193, 1), (11423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193
    · exact prime_11423
  · decide +kernel

theorem prime_552705941 : Nat.Prime 552705941 := by
  apply nodeValid_prime [2, 5, 157, 176021] ⟨552705941, 3, [(2, 2), (5, 1), (157, 1), (176021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_176021
  · decide +kernel

theorem prime_626795849 : Nat.Prime 626795849 := by
  apply nodeValid_prime [2, 7, 17, 94057] ⟨626795849, 3, [(2, 3), (7, 2), (17, 1), (94057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_94057
  · decide +kernel

theorem prime_715516531 : Nat.Prime 715516531 := by
  apply nodeValid_prime [2, 3, 5, 181, 131771] ⟨715516531, 2, [(2, 1), (3, 1), (5, 1), (181, 1), (131771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
    · exact prime_131771
  · decide +kernel

theorem prime_829115909 : Nat.Prime 829115909 := by
  apply nodeValid_prime [2, 17, 47, 59, 4397] ⟨829115909, 2, [(2, 2), (17, 1), (47, 1), (59, 1), (4397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_59
    · exact prime_4397
  · decide +kernel

theorem prime_838374389 : Nat.Prime 838374389 := by
  apply nodeValid_prime [2, 209593597] ⟨838374389, 2, [(2, 2), (209593597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_209593597
  · decide +kernel

theorem prime_853148209 : Nat.Prime 853148209 := by
  apply nodeValid_prime [2, 3, 11, 43, 53, 709] ⟨853148209, 31, [(2, 4), (3, 1), (11, 1), (43, 1), (53, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_53
    · exact prime_709
  · decide +kernel

theorem prime_943350799 : Nat.Prime 943350799 := by
  apply nodeValid_prime [2, 3, 13, 19, 636539] ⟨943350799, 6, [(2, 1), (3, 1), (13, 1), (19, 1), (636539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_636539
  · decide +kernel

theorem prime_984262691 : Nat.Prime 984262691 := by
  apply nodeValid_prime [2, 5, 23, 43, 4327] ⟨984262691, 10, [(2, 1), (5, 1), (23, 2), (43, 1), (4327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_43
    · exact prime_4327
  · decide +kernel

theorem prime_1276030771 : Nat.Prime 1276030771 := by
  apply nodeValid_prime [2, 3, 5, 7, 6076337] ⟨1276030771, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (6076337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_6076337
  · decide +kernel

theorem prime_1519715839 : Nat.Prime 1519715839 := by
  apply nodeValid_prime [2, 3, 253285973] ⟨1519715839, 3, [(2, 1), (3, 1), (253285973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_253285973
  · decide +kernel

theorem prime_2650366687 : Nat.Prime 2650366687 := by
  apply nodeValid_prime [2, 3, 11, 197, 203843] ⟨2650366687, 3, [(2, 1), (3, 1), (11, 1), (197, 1), (203843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_197
    · exact prime_203843
  · decide +kernel

theorem prime_3761085233 : Nat.Prime 3761085233 := by
  apply nodeValid_prime [2, 235067827] ⟨3761085233, 3, [(2, 4), (235067827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_235067827
  · decide +kernel

theorem prime_6780680107 : Nat.Prime 6780680107 := by
  apply nodeValid_prime [2, 3, 4451, 253901] ⟨6780680107, 3, [(2, 1), (3, 1), (4451, 1), (253901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4451
    · exact prime_253901
  · decide +kernel

theorem prime_7698340721 : Nat.Prime 7698340721 := by
  apply nodeValid_prime [2, 5, 7, 3331, 4127] ⟨7698340721, 3, [(2, 4), (5, 1), (7, 1), (3331, 1), (4127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3331
    · exact prime_4127
  · decide +kernel

theorem prime_9213664619 : Nat.Prime 9213664619 := by
  apply nodeValid_prime [2, 26437, 174257] ⟨9213664619, 2, [(2, 1), (26437, 1), (174257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_26437
    · exact prime_174257
  · decide +kernel

theorem prime_11737241447 : Nat.Prime 11737241447 := by
  apply nodeValid_prime [2, 7, 838374389] ⟨11737241447, 5, [(2, 1), (7, 1), (838374389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_838374389
  · decide +kernel

theorem prime_14842053557 : Nat.Prime 14842053557 := by
  apply nodeValid_prime [2, 11, 983, 343153] ⟨14842053557, 2, [(2, 2), (11, 1), (983, 1), (343153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_983
    · exact prime_343153
  · decide +kernel

theorem prime_18024267769 : Nat.Prime 18024267769 := by
  apply nodeValid_prime [2, 3, 13, 19, 23, 10169] ⟨18024267769, 11, [(2, 3), (3, 1), (13, 2), (19, 1), (23, 1), (10169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_23
    · exact prime_10169
  · decide +kernel

theorem prime_54165182219 : Nat.Prime 54165182219 := by
  apply nodeValid_prime [2, 7, 552705941] ⟨54165182219, 2, [(2, 1), (7, 2), (552705941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_552705941
  · decide +kernel

theorem prime_431107058659 : Nat.Prime 431107058659 := by
  apply nodeValid_prime [2, 3, 73, 984262691] ⟨431107058659, 2, [(2, 1), (3, 1), (73, 1), (984262691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_984262691
  · decide +kernel

theorem prime_431107058729 : Nat.Prime 431107058729 := by
  apply nodeValid_prime [2, 68567, 785923] ⟨431107058729, 3, [(2, 3), (68567, 1), (785923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_68567
    · exact prime_785923
  · decide +kernel

theorem prime_431107080377 : Nat.Prime 431107080377 := by
  apply nodeValid_prime [2, 7, 7698340721] ⟨431107080377, 3, [(2, 3), (7, 1), (7698340721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7698340721
  · decide +kernel

theorem prime_431844297197 : Nat.Prime 431844297197 := by
  apply nodeValid_prime [2, 13, 757, 10970539] ⟨431844297197, 2, [(2, 2), (13, 1), (757, 1), (10970539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_757
    · exact prime_10970539
  · decide +kernel

theorem prime_431844297289 : Nat.Prime 431844297289 := by
  apply nodeValid_prime [2, 3, 1597, 11267071] ⟨431844297289, 7, [(2, 3), (3, 1), (1597, 1), (11267071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1597
    · exact prime_11267071
  · decide +kernel

theorem prime_431844343921 : Nat.Prime 431844343921 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 23, 199] ⟨431844343921, 37, [(2, 4), (3, 3), (5, 1), (11, 2), (19, 2), (23, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_23
    · exact prime_199
  · decide +kernel

theorem prime_432582426457 : Nat.Prime 432582426457 := by
  apply nodeValid_prime [2, 3, 18024267769] ⟨432582426457, 5, [(2, 3), (3, 1), (18024267769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18024267769
  · decide +kernel

theorem prime_432582426967 : Nat.Prime 432582426967 := by
  apply nodeValid_prime [2, 3, 227, 10513, 30211] ⟨432582426967, 6, [(2, 1), (3, 1), (227, 1), (10513, 1), (30211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_10513
    · exact prime_30211
  · decide +kernel

theorem prime_432582464749 : Nat.Prime 432582464749 := by
  apply nodeValid_prime [2, 3, 7, 89, 57862823] ⟨432582464749, 6, [(2, 2), (3, 1), (7, 1), (89, 1), (57862823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_57862823
  · decide +kernel

theorem prime_433321442881 : Nat.Prime 433321442881 := by
  apply nodeValid_prime [2, 3, 5, 17, 29, 41, 137, 163] ⟨433321442881, 21, [(2, 6), (3, 1), (5, 1), (17, 1), (29, 1), (41, 1), (137, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_29
    · exact prime_41
    · exact prime_137
    · exact prime_163
  · decide +kernel

theorem prime_433321457753 : Nat.Prime 433321457753 := by
  apply nodeValid_prime [2, 54165182219] ⟨433321457753, 3, [(2, 3), (54165182219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54165182219
  · decide +kernel

theorem prime_433321457761 : Nat.Prime 433321457761 := by
  apply nodeValid_prime [2, 3, 5, 229, 438017] ⟨433321457761, 7, [(2, 5), (3, 3), (5, 1), (229, 1), (438017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
    · exact prime_438017
  · decide +kernel

theorem prime_434061279163 : Nat.Prime 434061279163 := by
  apply nodeValid_prime [2, 3, 7, 641, 5374307] ⟨434061279163, 3, [(2, 1), (3, 2), (7, 1), (641, 1), (5374307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_641
    · exact prime_5374307
  · decide +kernel

theorem prime_434061294221 : Nat.Prime 434061294221 := by
  apply nodeValid_prime [2, 5, 53, 587, 697601] ⟨434061294221, 2, [(2, 2), (5, 1), (53, 1), (587, 1), (697601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_587
    · exact prime_697601
  · decide +kernel

theorem prime_434061294319 : Nat.Prime 434061294319 := by
  apply nodeValid_prime [2, 3, 401, 1471, 13627] ⟨434061294319, 3, [(2, 1), (3, 3), (401, 1), (1471, 1), (13627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_1471
    · exact prime_13627
  · decide +kernel

theorem prime_434801969027 : Nat.Prime 434801969027 := by
  apply nodeValid_prime [2, 16573, 13117781] ⟨434801969027, 2, [(2, 1), (16573, 1), (13117781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16573
    · exact prime_13117781
  · decide +kernel

theorem prime_434802004837 : Nat.Prime 434802004837 := by
  apply nodeValid_prime [2, 3, 19, 53, 701, 51329] ⟨434802004837, 2, [(2, 2), (3, 1), (19, 1), (53, 1), (701, 1), (51329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
    · exact prime_701
    · exact prime_51329
  · decide +kernel

theorem prime_434802005587 : Nat.Prime 434802005587 := by
  apply nodeValid_prime [2, 3, 13, 1567, 1185787] ⟨434802005587, 5, [(2, 1), (3, 2), (13, 1), (1567, 1), (1185787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1567
    · exact prime_1185787
  · decide +kernel

theorem prime_435543492907 : Nat.Prime 435543492907 := by
  apply nodeValid_prime [2, 3, 971, 8306509] ⟨435543492907, 2, [(2, 1), (3, 3), (971, 1), (8306509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_971
    · exact prime_8306509
  · decide +kernel

theorem prime_435543493061 : Nat.Prime 435543493061 := by
  apply nodeValid_prime [2, 5, 13, 19, 29, 73, 41647] ⟨435543493061, 2, [(2, 2), (5, 1), (13, 1), (19, 1), (29, 1), (73, 1), (41647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_29
    · exact prime_73
    · exact prime_41647
  · decide +kernel

theorem prime_435543503741 : Nat.Prime 435543503741 := by
  apply nodeValid_prime [2, 5, 443, 49158409] ⟨435543503741, 3, [(2, 2), (5, 1), (443, 1), (49158409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_443
    · exact prime_49158409
  · decide +kernel

theorem prime_436285796899 : Nat.Prime 436285796899 := by
  apply nodeValid_prime [2, 3, 7, 47147, 220327] ⟨436285796899, 2, [(2, 1), (3, 1), (7, 1), (47147, 1), (220327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47147
    · exact prime_220327
  · decide +kernel

theorem prime_436285887029 : Nat.Prime 436285887029 := by
  apply nodeValid_prime [2, 29, 3761085233] ⟨436285887029, 2, [(2, 2), (29, 1), (3761085233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3761085233
  · decide +kernel

theorem prime_437029125139 : Nat.Prime 437029125139 := by
  apply nodeValid_prime [2, 3, 19, 1231, 38447] ⟨437029125139, 3, [(2, 1), (3, 5), (19, 1), (1231, 1), (38447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1231
    · exact prime_38447
  · decide +kernel

theorem prime_437029145261 : Nat.Prime 437029145261 := by
  apply nodeValid_prime [2, 5, 17, 73, 17607943] ⟨437029145261, 2, [(2, 2), (5, 1), (17, 1), (73, 1), (17607943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_73
    · exact prime_17607943
  · decide +kernel

theorem prime_437029145909 : Nat.Prime 437029145909 := by
  apply nodeValid_prime [2, 61, 181, 719, 13763] ⟨437029145909, 2, [(2, 2), (61, 1), (181, 1), (719, 1), (13763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_181
    · exact prime_719
    · exact prime_13763
  · decide +kernel

theorem prime_437773199867 : Nat.Prime 437773199867 := by
  apply nodeValid_prime [2, 17, 83, 155128703] ⟨437773199867, 2, [(2, 1), (17, 1), (83, 1), (155128703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_83
    · exact prime_155128703
  · decide +kernel

theorem prime_437773199953 : Nat.Prime 437773199953 := by
  apply nodeValid_prime [2, 3, 11, 829115909] ⟨437773199953, 5, [(2, 4), (3, 1), (11, 1), (829115909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_829115909
  · decide +kernel

theorem prime_437773221911 : Nat.Prime 437773221911 := by
  apply nodeValid_prime [2, 5, 19, 151, 15258739] ⟨437773221911, 7, [(2, 1), (5, 1), (19, 1), (151, 1), (15258739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_151
    · exact prime_15258739
  · decide +kernel

theorem prime_438518179427 : Nat.Prime 438518179427 := by
  apply nodeValid_prime [2, 257, 853148209] ⟨438518179427, 2, [(2, 1), (257, 1), (853148209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_853148209
  · decide +kernel

theorem prime_438518200781 : Nat.Prime 438518200781 := by
  apply nodeValid_prime [2, 5, 11, 103, 19352083] ⟨438518200781, 7, [(2, 2), (5, 1), (11, 1), (103, 1), (19352083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_103
    · exact prime_19352083
  · decide +kernel

theorem prime_438518201071 : Nat.Prime 438518201071 := by
  apply nodeValid_prime [2, 3, 5, 311, 47000879] ⟨438518201071, 3, [(2, 1), (3, 1), (5, 1), (311, 1), (47000879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_311
    · exact prime_47000879
  · decide +kernel

theorem prime_439264003837 : Nat.Prime 439264003837 := by
  apply nodeValid_prime [2, 3, 7, 53101, 98479] ⟨439264003837, 2, [(2, 2), (3, 1), (7, 1), (53101, 1), (98479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53101
    · exact prime_98479
  · decide +kernel

theorem prime_439264024153 : Nat.Prime 439264024153 := by
  apply nodeValid_prime [2, 3, 1913, 9567521] ⟨439264024153, 10, [(2, 3), (3, 1), (1913, 1), (9567521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1913
    · exact prime_9567521
  · decide +kernel

theorem prime_439264024543 : Nat.Prime 439264024543 := by
  apply nodeValid_prime [2, 3, 7, 4639, 250501] ⟨439264024543, 3, [(2, 1), (3, 3), (7, 1), (4639, 1), (250501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4639
    · exact prime_250501
  · decide +kernel

theorem prime_440010671389 : Nat.Prime 440010671389 := by
  apply nodeValid_prime [2, 3, 23, 29, 1163, 47269] ⟨440010671389, 2, [(2, 2), (3, 1), (23, 1), (29, 1), (1163, 1), (47269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_29
    · exact prime_1163
    · exact prime_47269
  · decide +kernel

theorem prime_440010671689 : Nat.Prime 440010671689 := by
  apply nodeValid_prime [2, 3, 7, 291012349] ⟨440010671689, 33, [(2, 3), (3, 3), (7, 1), (291012349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_291012349
  · decide +kernel

theorem prime_440010685999 : Nat.Prime 440010685999 := by
  apply nodeValid_prime [2, 3, 13, 626795849] ⟨440010685999, 6, [(2, 1), (3, 3), (13, 1), (626795849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_626795849
  · decide +kernel

theorem prime_440758183097 : Nat.Prime 440758183097 := by
  apply nodeValid_prime [2, 7, 11, 715516531] ⟨440758183097, 3, [(2, 3), (7, 1), (11, 1), (715516531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_715516531
  · decide +kernel

theorem prime_440758185167 : Nat.Prime 440758185167 := by
  apply nodeValid_prime [2, 13, 4751, 3568141] ⟨440758185167, 5, [(2, 1), (13, 1), (4751, 1), (3568141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4751
    · exact prime_3568141
  · decide +kernel

theorem prime_440758225547 : Nat.Prime 440758225547 := by
  apply nodeValid_prime [2, 151, 1511, 965893] ⟨440758225547, 2, [(2, 1), (151, 1), (1511, 1), (965893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_1511
    · exact prime_965893
  · decide +kernel

theorem prime_441506628551 : Nat.Prime 441506628551 := by
  apply nodeValid_prime [2, 5, 13, 17, 39955351] ⟨441506628551, 7, [(2, 1), (5, 2), (13, 1), (17, 1), (39955351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_39955351
  · decide +kernel

theorem prime_441506645747 : Nat.Prime 441506645747 := by
  apply nodeValid_prime [2, 179, 479, 2574653] ⟨441506645747, 2, [(2, 1), (179, 1), (479, 1), (2574653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_479
    · exact prime_2574653
  · decide +kernel

theorem prime_441506646767 : Nat.Prime 441506646767 := by
  apply nodeValid_prime [2, 173, 1276030771] ⟨441506646767, 5, [(2, 1), (173, 1), (1276030771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_1276030771
  · decide +kernel

theorem prime_442255894903 : Nat.Prime 442255894903 := by
  apply nodeValid_prime [2, 3, 317, 8747, 8861] ⟨442255894903, 3, [(2, 1), (3, 2), (317, 1), (8747, 1), (8861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
    · exact prime_8747
    · exact prime_8861
  · decide +kernel

theorem prime_442255901713 : Nat.Prime 442255901713 := by
  apply nodeValid_prime [2, 3, 9213664619] ⟨442255901713, 5, [(2, 4), (3, 1), (9213664619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9213664619
  · decide +kernel

theorem prime_442255901831 : Nat.Prime 442255901831 := by
  apply nodeValid_prime [2, 5, 55697, 794039] ⟨442255901831, 7, [(2, 1), (5, 1), (55697, 1), (794039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_55697
    · exact prime_794039
  · decide +kernel

theorem prime_443006017549 : Nat.Prime 443006017549 := by
  apply nodeValid_prime [2, 3, 167, 2861, 77267] ⟨443006017549, 6, [(2, 2), (3, 1), (167, 1), (2861, 1), (77267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_2861
    · exact prime_77267
  · decide +kernel

theorem prime_443006018929 : Nat.Prime 443006018929 := by
  apply nodeValid_prime [2, 3, 11, 17, 59, 25349] ⟨443006018929, 13, [(2, 4), (3, 2), (11, 2), (17, 1), (59, 1), (25349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_59
    · exact prime_25349
  · decide +kernel

theorem prime_443006022883 : Nat.Prime 443006022883 := by
  apply nodeValid_prime [2, 3, 6823, 10821389] ⟨443006022883, 3, [(2, 1), (3, 1), (6823, 1), (10821389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6823
    · exact prime_10821389
  · decide +kernel

theorem prime_443757014299 : Nat.Prime 443757014299 := by
  apply nodeValid_prime [2, 3, 13, 3659, 57587] ⟨443757014299, 7, [(2, 1), (3, 4), (13, 1), (3659, 1), (57587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3659
    · exact prime_57587
  · decide +kernel

theorem prime_443757024989 : Nat.Prime 443757024989 := by
  apply nodeValid_prime [2, 73, 1519715839] ⟨443757024989, 2, [(2, 2), (73, 1), (1519715839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1519715839
  · decide +kernel

theorem prime_443757025013 : Nat.Prime 443757025013 := by
  apply nodeValid_prime [2, 7, 107, 148116497] ⟨443757025013, 2, [(2, 2), (7, 1), (107, 1), (148116497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
    · exact prime_148116497
  · decide +kernel

theorem prime_444508866677 : Nat.Prime 444508866677 := by
  apply nodeValid_prime [2, 7, 773, 2933897] ⟨444508866677, 2, [(2, 2), (7, 2), (773, 1), (2933897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_773
    · exact prime_2933897
  · decide +kernel

theorem prime_444508879121 : Nat.Prime 444508879121 := by
  apply nodeValid_prime [2, 5, 2111, 2632099] ⟨444508879121, 3, [(2, 4), (5, 1), (2111, 1), (2632099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2111
    · exact prime_2632099
  · decide +kernel

theorem prime_444508879163 : Nat.Prime 444508879163 := by
  apply nodeValid_prime [2, 31, 463, 15484877] ⟨444508879163, 2, [(2, 1), (31, 1), (463, 1), (15484877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_463
    · exact prime_15484877
  · decide +kernel

theorem prime_445261577129 : Nat.Prime 445261577129 := by
  apply nodeValid_prime [2, 59, 943350799] ⟨445261577129, 3, [(2, 3), (59, 1), (943350799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_943350799
  · decide +kernel

theorem prime_445261603417 : Nat.Prime 445261603417 := by
  apply nodeValid_prime [2, 3, 7, 2650366687] ⟨445261603417, 20, [(2, 3), (3, 1), (7, 1), (2650366687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2650366687
  · decide +kernel

theorem prime_445261606711 : Nat.Prime 445261606711 := by
  apply nodeValid_prime [2, 3, 5, 14842053557] ⟨445261606711, 12, [(2, 1), (3, 1), (5, 1), (14842053557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14842053557
  · decide +kernel

theorem prime_446015149351 : Nat.Prime 446015149351 := by
  apply nodeValid_prime [2, 3, 5, 191, 15567719] ⟨446015149351, 3, [(2, 1), (3, 1), (5, 2), (191, 1), (15567719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
    · exact prime_15567719
  · decide +kernel

theorem prime_446015174987 : Nat.Prime 446015174987 := by
  apply nodeValid_prime [2, 19, 11737241447] ⟨446015174987, 2, [(2, 1), (19, 1), (11737241447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_11737241447
  · decide +kernel

theorem prime_446015175061 : Nat.Prime 446015175061 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 109, 749429] ⟨446015175061, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (109, 1), (749429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_109
    · exact prime_749429
  · decide +kernel

theorem prime_446769582361 : Nat.Prime 446769582361 := by
  apply nodeValid_prime [2, 3, 5, 55541, 67033] ⟨446769582361, 23, [(2, 3), (3, 1), (5, 1), (55541, 1), (67033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_55541
    · exact prime_67033
  · decide +kernel

theorem prime_446769587081 : Nat.Prime 446769587081 := by
  apply nodeValid_prime [2, 5, 113, 98842829] ⟨446769587081, 3, [(2, 3), (5, 1), (113, 1), (98842829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
    · exact prime_98842829
  · decide +kernel

theorem prime_447524887063 : Nat.Prime 447524887063 := by
  apply nodeValid_prime [2, 3, 11, 6780680107] ⟨447524887063, 3, [(2, 1), (3, 1), (11, 1), (6780680107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6780680107
  · decide +kernel

theorem prime_447524908001 : Nat.Prime 447524908001 := by
  apply nodeValid_prime [2, 5, 43, 617, 4217] ⟨447524908001, 3, [(2, 5), (5, 3), (43, 1), (617, 1), (4217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_617
    · exact prime_4217
  · decide +kernel

theorem prime_447524908357 : Nat.Prime 447524908357 := by
  apply nodeValid_prime [2, 3, 46301, 805463] ⟨447524908357, 5, [(2, 2), (3, 1), (46301, 1), (805463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_46301
    · exact prime_805463
  · decide +kernel

theorem prime_448281053131 : Nat.Prime 448281053131 := by
  apply nodeValid_prime [2, 3, 5, 163, 3793, 24169] ⟨448281053131, 13, [(2, 1), (3, 1), (5, 1), (163, 1), (3793, 1), (24169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_163
    · exact prime_3793
    · exact prime_24169
  · decide +kernel

theorem prime_448281060013 : Nat.Prime 448281060013 := by
  apply nodeValid_prime [2, 3, 59, 317, 665789] ⟨448281060013, 2, [(2, 2), (3, 2), (59, 1), (317, 1), (665789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_317
    · exact prime_665789
  · decide +kernel

theorem prime_448281060427 : Nat.Prime 448281060427 := by
  apply nodeValid_prime [2, 3, 1051, 7898669] ⟨448281060427, 2, [(2, 1), (3, 3), (1051, 1), (7898669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1051
    · exact prime_7898669
  · decide +kernel

theorem prime_449038084997 : Nat.Prime 449038084997 := by
  apply nodeValid_prime [2, 31, 593, 683, 8941] ⟨449038084997, 2, [(2, 2), (31, 1), (593, 1), (683, 1), (8941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_593
    · exact prime_683
    · exact prime_8941
  · decide +kernel

theorem prime_449038104653 : Nat.Prime 449038104653 := by
  apply nodeValid_prime [2, 17, 307, 1265281] ⟨449038104653, 2, [(2, 2), (17, 2), (307, 1), (1265281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_307
    · exact prime_1265281
  · decide +kernel

theorem prime_449038109171 : Nat.Prime 449038109171 := by
  apply nodeValid_prime [2, 5, 7, 29, 8369, 26431] ⟨449038109171, 2, [(2, 1), (5, 1), (7, 1), (29, 1), (8369, 1), (26431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_8369
    · exact prime_26431
  · decide +kernel

end Sude.Lucas.Generated
