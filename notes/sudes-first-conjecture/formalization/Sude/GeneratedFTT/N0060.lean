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
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0057

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6079 : Nat.Prime 6079 := by
  apply nodeValid_prime [2, 3, 1013] ⟨6079, 17, [(2, 1), (3, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1013
  · decide +kernel

theorem prime_7499 : Nat.Prime 7499 := by
  apply nodeValid_prime [2, 23, 163] ⟨7499, 2, [(2, 1), (23, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_163
  · decide +kernel

theorem prime_10271 : Nat.Prime 10271 := by
  apply nodeValid_prime [2, 5, 13, 79] ⟨10271, 7, [(2, 1), (5, 1), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_10733 : Nat.Prime 10733 := by
  apply nodeValid_prime [2, 2683] ⟨10733, 2, [(2, 2), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2683
  · decide +kernel

theorem prime_12781 : Nat.Prime 12781 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨12781, 2, [(2, 2), (3, 2), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_14731 : Nat.Prime 14731 := by
  apply nodeValid_prime [2, 3, 5, 491] ⟨14731, 10, [(2, 1), (3, 1), (5, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_491
  · decide +kernel

theorem prime_15643 : Nat.Prime 15643 := by
  apply nodeValid_prime [2, 3, 11, 79] ⟨15643, 5, [(2, 1), (3, 2), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_15881 : Nat.Prime 15881 := by
  apply nodeValid_prime [2, 5, 397] ⟨15881, 3, [(2, 3), (5, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_397
  · decide +kernel

theorem prime_16921 : Nat.Prime 16921 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨16921, 17, [(2, 3), (3, 2), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_17011 : Nat.Prime 17011 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨17011, 2, [(2, 1), (3, 5), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_17231 : Nat.Prime 17231 := by
  apply nodeValid_prime [2, 5, 1723] ⟨17231, 13, [(2, 1), (5, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1723
  · decide +kernel

theorem prime_18367 : Nat.Prime 18367 := by
  apply nodeValid_prime [2, 3, 3061] ⟨18367, 3, [(2, 1), (3, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3061
  · decide +kernel

theorem prime_20593 : Nat.Prime 20593 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨20593, 5, [(2, 4), (3, 2), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_22531 : Nat.Prime 22531 := by
  apply nodeValid_prime [2, 3, 5, 751] ⟨22531, 2, [(2, 1), (3, 1), (5, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_751
  · decide +kernel

theorem prime_24317 : Nat.Prime 24317 := by
  apply nodeValid_prime [2, 6079] ⟨24317, 2, [(2, 2), (6079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6079
  · decide +kernel

theorem prime_24359 : Nat.Prime 24359 := by
  apply nodeValid_prime [2, 19, 641] ⟨24359, 11, [(2, 1), (19, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_641
  · decide +kernel

theorem prime_28069 : Nat.Prime 28069 := by
  apply nodeValid_prime [2, 3, 2339] ⟨28069, 7, [(2, 2), (3, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2339
  · decide +kernel

theorem prime_32327 : Nat.Prime 32327 := by
  apply nodeValid_prime [2, 7, 2309] ⟨32327, 5, [(2, 1), (7, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2309
  · decide +kernel

theorem prime_32441 : Nat.Prime 32441 := by
  apply nodeValid_prime [2, 5, 811] ⟨32441, 3, [(2, 3), (5, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_811
  · decide +kernel

theorem prime_37363 : Nat.Prime 37363 := by
  apply nodeValid_prime [2, 3, 13, 479] ⟨37363, 3, [(2, 1), (3, 1), (13, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_479
  · decide +kernel

theorem prime_46091 : Nat.Prime 46091 := by
  apply nodeValid_prime [2, 5, 11, 419] ⟨46091, 2, [(2, 1), (5, 1), (11, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_419
  · decide +kernel

theorem prime_47237 : Nat.Prime 47237 := by
  apply nodeValid_prime [2, 7, 241] ⟨47237, 2, [(2, 2), (7, 2), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_241
  · decide +kernel

theorem prime_55813 : Nat.Prime 55813 := by
  apply nodeValid_prime [2, 3, 4651] ⟨55813, 2, [(2, 2), (3, 1), (4651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4651
  · decide +kernel

theorem prime_65101 : Nat.Prime 65101 := by
  apply nodeValid_prime [2, 3, 5, 7, 31] ⟨65101, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_67741 : Nat.Prime 67741 := by
  apply nodeValid_prime [2, 3, 5, 1129] ⟨67741, 6, [(2, 2), (3, 1), (5, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1129
  · decide +kernel

theorem prime_84059 : Nat.Prime 84059 := by
  apply nodeValid_prime [2, 13, 53, 61] ⟨84059, 2, [(2, 1), (13, 1), (53, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_61
  · decide +kernel

theorem prime_89083 : Nat.Prime 89083 := by
  apply nodeValid_prime [2, 3, 7, 101] ⟨89083, 2, [(2, 1), (3, 2), (7, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
  · decide +kernel

theorem prime_89989 : Nat.Prime 89989 := by
  apply nodeValid_prime [2, 3, 7499] ⟨89989, 2, [(2, 2), (3, 1), (7499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7499
  · decide +kernel

theorem prime_90397 : Nat.Prime 90397 := by
  apply nodeValid_prime [2, 3, 31] ⟨90397, 2, [(2, 2), (3, 6), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_101527 : Nat.Prime 101527 := by
  apply nodeValid_prime [2, 3, 16921] ⟨101527, 5, [(2, 1), (3, 1), (16921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16921
  · decide +kernel

theorem prime_103177 : Nat.Prime 103177 := by
  apply nodeValid_prime [2, 3, 1433] ⟨103177, 10, [(2, 3), (3, 2), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1433
  · decide +kernel

theorem prime_108923 : Nat.Prime 108923 := by
  apply nodeValid_prime [2, 11, 4951] ⟨108923, 2, [(2, 1), (11, 1), (4951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4951
  · decide +kernel

theorem prime_122957 : Nat.Prime 122957 := by
  apply nodeValid_prime [2, 59, 521] ⟨122957, 2, [(2, 2), (59, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_521
  · decide +kernel

theorem prime_135119 : Nat.Prime 135119 := by
  apply nodeValid_prime [2, 67559] ⟨135119, 17, [(2, 1), (67559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67559
  · decide +kernel

theorem prime_137353 : Nat.Prime 137353 := by
  apply nodeValid_prime [2, 3, 59, 97] ⟨137353, 5, [(2, 3), (3, 1), (59, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_97
  · decide +kernel

theorem prime_141697 : Nat.Prime 141697 := by
  apply nodeValid_prime [2, 3, 41] ⟨141697, 10, [(2, 7), (3, 3), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_193433 : Nat.Prime 193433 := by
  apply nodeValid_prime [2, 24179] ⟨193433, 3, [(2, 3), (24179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24179
  · decide +kernel

theorem prime_238919 : Nat.Prime 238919 := by
  apply nodeValid_prime [2, 17, 7027] ⟨238919, 7, [(2, 1), (17, 1), (7027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_7027
  · decide +kernel

theorem prime_257297 : Nat.Prime 257297 := by
  apply nodeValid_prime [2, 13, 1237] ⟨257297, 3, [(2, 4), (13, 1), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1237
  · decide +kernel

theorem prime_314779 : Nat.Prime 314779 := by
  apply nodeValid_prime [2, 3, 23, 2281] ⟨314779, 3, [(2, 1), (3, 1), (23, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2281
  · decide +kernel

theorem prime_317621 : Nat.Prime 317621 := by
  apply nodeValid_prime [2, 5, 15881] ⟨317621, 3, [(2, 2), (5, 1), (15881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15881
  · decide +kernel

theorem prime_368729 : Nat.Prime 368729 := by
  apply nodeValid_prime [2, 46091] ⟨368729, 3, [(2, 3), (46091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46091
  · decide +kernel

theorem prime_437473 : Nat.Prime 437473 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨437473, 10, [(2, 5), (3, 2), (7, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_459397 : Nat.Prime 459397 := by
  apply nodeValid_prime [2, 3, 7, 1823] ⟨459397, 6, [(2, 2), (3, 2), (7, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1823
  · decide +kernel

theorem prime_477839 : Nat.Prime 477839 := by
  apply nodeValid_prime [2, 238919] ⟨477839, 13, [(2, 1), (238919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_238919
  · decide +kernel

theorem prime_536651 : Nat.Prime 536651 := by
  apply nodeValid_prime [2, 5, 10733] ⟨536651, 6, [(2, 1), (5, 2), (10733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10733
  · decide +kernel

theorem prime_587417 : Nat.Prime 587417 := by
  apply nodeValid_prime [2, 101, 727] ⟨587417, 3, [(2, 3), (101, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_727
  · decide +kernel

theorem prime_609163 : Nat.Prime 609163 := by
  apply nodeValid_prime [2, 3, 101527] ⟨609163, 3, [(2, 1), (3, 1), (101527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101527
  · decide +kernel

theorem prime_690419 : Nat.Prime 690419 := by
  apply nodeValid_prime [2, 59, 5851] ⟨690419, 2, [(2, 1), (59, 1), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_5851
  · decide +kernel

theorem prime_720991 : Nat.Prime 720991 := by
  apply nodeValid_prime [2, 3, 5, 8011] ⟨720991, 3, [(2, 1), (3, 2), (5, 1), (8011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8011
  · decide +kernel

theorem prime_819037 : Nat.Prime 819037 := by
  apply nodeValid_prime [2, 3, 22751] ⟨819037, 2, [(2, 2), (3, 2), (22751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22751
  · decide +kernel

theorem prime_842071 : Nat.Prime 842071 := by
  apply nodeValid_prime [2, 3, 5, 28069] ⟨842071, 3, [(2, 1), (3, 1), (5, 1), (28069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28069
  · decide +kernel

theorem prime_882587 : Nat.Prime 882587 := by
  apply nodeValid_prime [2, 29, 15217] ⟨882587, 2, [(2, 1), (29, 1), (15217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_15217
  · decide +kernel

theorem prime_971713 : Nat.Prime 971713 := by
  apply nodeValid_prime [2, 3, 7, 241] ⟨971713, 10, [(2, 6), (3, 2), (7, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_241
  · decide +kernel

theorem prime_1095541 : Nat.Prime 1095541 := by
  apply nodeValid_prime [2, 3, 5, 19, 31] ⟨1095541, 10, [(2, 2), (3, 1), (5, 1), (19, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_1171811 : Nat.Prime 1171811 := by
  apply nodeValid_prime [2, 5, 17, 61, 113] ⟨1171811, 2, [(2, 1), (5, 1), (17, 1), (61, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_61
    · exact prime_113
  · decide +kernel

theorem prime_1296007 : Nat.Prime 1296007 := by
  apply nodeValid_prime [2, 3, 61, 3541] ⟨1296007, 3, [(2, 1), (3, 1), (61, 1), (3541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_3541
  · decide +kernel

theorem prime_1382501 : Nat.Prime 1382501 := by
  apply nodeValid_prime [2, 5, 7, 79] ⟨1382501, 2, [(2, 2), (5, 4), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_1585279 : Nat.Prime 1585279 := by
  apply nodeValid_prime [2, 3, 31, 947] ⟨1585279, 3, [(2, 1), (3, 3), (31, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_947
  · decide +kernel

theorem prime_1676947 : Nat.Prime 1676947 := by
  apply nodeValid_prime [2, 3, 269, 1039] ⟨1676947, 2, [(2, 1), (3, 1), (269, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_1039
  · decide +kernel

theorem prime_1720321 : Nat.Prime 1720321 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨1720321, 17, [(2, 14), (3, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_1990151 : Nat.Prime 1990151 := by
  apply nodeValid_prime [2, 5, 53, 751] ⟨1990151, 7, [(2, 1), (5, 2), (53, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_751
  · decide +kernel

theorem prime_2413511 : Nat.Prime 2413511 := by
  apply nodeValid_prime [2, 5, 11, 37, 593] ⟨2413511, 7, [(2, 1), (5, 1), (11, 1), (37, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_593
  · decide +kernel

theorem prime_2531117 : Nat.Prime 2531117 := by
  apply nodeValid_prime [2, 7, 90397] ⟨2531117, 3, [(2, 2), (7, 1), (90397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_90397
  · decide +kernel

theorem prime_2647031 : Nat.Prime 2647031 := by
  apply nodeValid_prime [2, 5, 151, 1753] ⟨2647031, 7, [(2, 1), (5, 1), (151, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_1753
  · decide +kernel

theorem prime_2654467 : Nat.Prime 2654467 := by
  apply nodeValid_prime [2, 3, 47, 9413] ⟨2654467, 22, [(2, 1), (3, 1), (47, 1), (9413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_9413
  · decide +kernel

theorem prime_2812717 : Nat.Prime 2812717 := by
  apply nodeValid_prime [2, 3, 23, 43, 79] ⟨2812717, 5, [(2, 2), (3, 2), (23, 1), (43, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_43
    · exact prime_79
  · decide +kernel

theorem prime_3980303 : Nat.Prime 3980303 := by
  apply nodeValid_prime [2, 1990151] ⟨3980303, 5, [(2, 1), (1990151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1990151
  · decide +kernel

theorem prime_4577569 : Nat.Prime 4577569 := by
  apply nodeValid_prime [2, 3, 41, 1163] ⟨4577569, 7, [(2, 5), (3, 1), (41, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1163
  · decide +kernel

theorem prime_6689723 : Nat.Prime 6689723 := by
  apply nodeValid_prime [2, 13, 257297] ⟨6689723, 2, [(2, 1), (13, 1), (257297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_257297
  · decide +kernel

theorem prime_7209383 : Nat.Prime 7209383 := by
  apply nodeValid_prime [2, 79, 103, 443] ⟨7209383, 5, [(2, 1), (79, 1), (103, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_103
    · exact prime_443
  · decide +kernel

theorem prime_8761439 : Nat.Prime 8761439 := by
  apply nodeValid_prime [2, 7, 607, 1031] ⟨8761439, 7, [(2, 1), (7, 1), (607, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_607
    · exact prime_1031
  · decide +kernel

theorem prime_9352003 : Nat.Prime 9352003 := by
  apply nodeValid_prime [2, 3, 11, 141697] ⟨9352003, 3, [(2, 1), (3, 1), (11, 1), (141697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_141697
  · decide +kernel

theorem prime_9758821 : Nat.Prime 9758821 := by
  apply nodeValid_prime [2, 3, 5, 41, 3967] ⟨9758821, 2, [(2, 2), (3, 1), (5, 1), (41, 1), (3967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_3967
  · decide +kernel

theorem prime_10617869 : Nat.Prime 10617869 := by
  apply nodeValid_prime [2, 2654467] ⟨10617869, 2, [(2, 2), (2654467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2654467
  · decide +kernel

theorem prime_12208303 : Nat.Prime 12208303 := by
  apply nodeValid_prime [2, 3, 43, 15773] ⟨12208303, 3, [(2, 1), (3, 2), (43, 1), (15773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_15773
  · decide +kernel

theorem prime_15547409 : Nat.Prime 15547409 := by
  apply nodeValid_prime [2, 971713] ⟨15547409, 3, [(2, 4), (971713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_971713
  · decide +kernel

theorem prime_15861803 : Nat.Prime 15861803 := by
  apply nodeValid_prime [2, 11, 720991] ⟨15861803, 2, [(2, 1), (11, 1), (720991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_720991
  · decide +kernel

theorem prime_15886567 : Nat.Prime 15886567 := by
  apply nodeValid_prime [2, 3, 882587] ⟨15886567, 3, [(2, 1), (3, 2), (882587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_882587
  · decide +kernel

theorem prime_17892209 : Nat.Prime 17892209 := by
  apply nodeValid_prime [2, 31, 36073] ⟨17892209, 3, [(2, 4), (31, 1), (36073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_36073
  · decide +kernel

theorem prime_22215409 : Nat.Prime 22215409 := by
  apply nodeValid_prime [2, 3, 19, 24359] ⟨22215409, 7, [(2, 4), (3, 1), (19, 1), (24359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_24359
  · decide +kernel

theorem prime_27055961 : Nat.Prime 27055961 := by
  apply nodeValid_prime [2, 5, 233, 2903] ⟨27055961, 3, [(2, 3), (5, 1), (233, 1), (2903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
    · exact prime_2903
  · decide +kernel

theorem prime_32116577 : Nat.Prime 32116577 := by
  apply nodeValid_prime [2, 983, 1021] ⟨32116577, 3, [(2, 5), (983, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_983
    · exact prime_1021
  · decide +kernel

theorem prime_39940841 : Nat.Prime 39940841 := by
  apply nodeValid_prime [2, 5, 373, 2677] ⟨39940841, 3, [(2, 3), (5, 1), (373, 1), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_373
    · exact prime_2677
  · decide +kernel

theorem prime_43256299 : Nat.Prime 43256299 := by
  apply nodeValid_prime [2, 3, 7209383] ⟨43256299, 3, [(2, 1), (3, 1), (7209383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7209383
  · decide +kernel

theorem prime_46330913 : Nat.Prime 46330913 := by
  apply nodeValid_prime [2, 619, 2339] ⟨46330913, 3, [(2, 5), (619, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_2339
  · decide +kernel

theorem prime_49417493 : Nat.Prime 49417493 := by
  apply nodeValid_prime [2, 43, 47, 6113] ⟨49417493, 2, [(2, 2), (43, 1), (47, 1), (6113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_47
    · exact prime_6113
  · decide +kernel

theorem prime_58407061 : Nat.Prime 58407061 := by
  apply nodeValid_prime [2, 3, 5, 53, 18367] ⟨58407061, 2, [(2, 2), (3, 1), (5, 1), (53, 1), (18367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_18367
  · decide +kernel

theorem prime_62959207 : Nat.Prime 62959207 := by
  apply nodeValid_prime [2, 3, 821, 12781] ⟨62959207, 5, [(2, 1), (3, 1), (821, 1), (12781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_821
    · exact prime_12781
  · decide +kernel

theorem prime_79877569 : Nat.Prime 79877569 := by
  apply nodeValid_prime [2, 3, 541, 769] ⟨79877569, 11, [(2, 6), (3, 1), (541, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
    · exact prime_769
  · decide +kernel

theorem prime_98496533 : Nat.Prime 98496533 := by
  apply nodeValid_prime [2, 19, 1296007] ⟨98496533, 2, [(2, 2), (19, 1), (1296007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1296007
  · decide +kernel

theorem prime_103530131 : Nat.Prime 103530131 := by
  apply nodeValid_prime [2, 5, 11, 23, 151, 271] ⟨103530131, 2, [(2, 1), (5, 1), (11, 1), (23, 1), (151, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_151
    · exact prime_271
  · decide +kernel

theorem prime_117105853 : Nat.Prime 117105853 := by
  apply nodeValid_prime [2, 3, 9758821] ⟨117105853, 5, [(2, 2), (3, 1), (9758821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9758821
  · decide +kernel

theorem prime_130477861 : Nat.Prime 130477861 := by
  apply nodeValid_prime [2, 3, 5, 101, 7177] ⟨130477861, 13, [(2, 2), (3, 2), (5, 1), (101, 1), (7177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_7177
  · decide +kernel

theorem prime_171444803 : Nat.Prime 171444803 := by
  apply nodeValid_prime [2, 787, 108923] ⟨171444803, 2, [(2, 1), (787, 1), (108923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_787
    · exact prime_108923
  · decide +kernel

theorem prime_232758077 : Nat.Prime 232758077 := by
  apply nodeValid_prime [2, 859, 67741] ⟨232758077, 2, [(2, 2), (859, 1), (67741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_859
    · exact prime_67741
  · decide +kernel

theorem prime_293609573 : Nat.Prime 293609573 := by
  apply nodeValid_prime [2, 29, 2531117] ⟨293609573, 2, [(2, 2), (29, 1), (2531117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_2531117
  · decide +kernel

theorem prime_393723433 : Nat.Prime 393723433 := by
  apply nodeValid_prime [2, 3, 53, 103177] ⟨393723433, 15, [(2, 3), (3, 2), (53, 1), (103177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_103177
  · decide +kernel

theorem prime_408709069 : Nat.Prime 408709069 := by
  apply nodeValid_prime [2, 3, 277, 122957] ⟨408709069, 2, [(2, 2), (3, 1), (277, 1), (122957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_122957
  · decide +kernel

theorem prime_504118723 : Nat.Prime 504118723 := by
  apply nodeValid_prime [2, 3, 53, 1585279] ⟨504118723, 2, [(2, 1), (3, 1), (53, 1), (1585279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1585279
  · decide +kernel

theorem prime_603988501 : Nat.Prime 603988501 := by
  apply nodeValid_prime [2, 3, 5, 31, 419] ⟨603988501, 11, [(2, 2), (3, 1), (5, 3), (31, 2), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_419
  · decide +kernel

theorem prime_724291313 : Nat.Prime 724291313 := by
  apply nodeValid_prime [2, 43, 293, 3593] ⟨724291313, 3, [(2, 4), (43, 1), (293, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_293
    · exact prime_3593
  · decide +kernel

theorem prime_796458631 : Nat.Prime 796458631 := by
  apply nodeValid_prime [2, 3, 5, 11, 2413511] ⟨796458631, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (2413511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2413511
  · decide +kernel

theorem prime_1098563629 : Nat.Prime 1098563629 := by
  apply nodeValid_prime [2, 3, 23, 3980303] ⟨1098563629, 13, [(2, 2), (3, 1), (23, 1), (3980303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3980303
  · decide +kernel

theorem prime_1700320813 : Nat.Prime 1700320813 := by
  apply nodeValid_prime [2, 3, 173, 819037] ⟨1700320813, 2, [(2, 2), (3, 1), (173, 1), (819037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_819037
  · decide +kernel

theorem prime_1786804373 : Nat.Prime 1786804373 := by
  apply nodeValid_prime [2, 647, 690419] ⟨1786804373, 2, [(2, 2), (647, 1), (690419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_647
    · exact prime_690419
  · decide +kernel

theorem prime_1928031037 : Nat.Prime 1928031037 := by
  apply nodeValid_prime [2, 3, 10271, 15643] ⟨1928031037, 2, [(2, 2), (3, 1), (10271, 1), (15643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10271
    · exact prime_15643
  · decide +kernel

theorem prime_2381723089 : Nat.Prime 2381723089 := by
  apply nodeValid_prime [2, 3, 557, 89083] ⟨2381723089, 13, [(2, 4), (3, 1), (557, 1), (89083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
    · exact prime_89083
  · decide +kernel

theorem prime_2638345043 : Nat.Prime 2638345043 := by
  apply nodeValid_prime [2, 23, 283, 389, 521] ⟨2638345043, 2, [(2, 1), (23, 1), (283, 1), (389, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_283
    · exact prime_389
    · exact prime_521
  · decide +kernel

theorem prime_3220597621 : Nat.Prime 3220597621 := by
  apply nodeValid_prime [2, 3, 5, 17892209] ⟨3220597621, 7, [(2, 2), (3, 2), (5, 1), (17892209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17892209
  · decide +kernel

theorem prime_6493253953 : Nat.Prime 6493253953 := by
  apply nodeValid_prime [2, 3, 19, 79, 22531] ⟨6493253953, 5, [(2, 6), (3, 1), (19, 1), (79, 1), (22531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_79
    · exact prime_22531
  · decide +kernel

theorem prime_7661229677 : Nat.Prime 7661229677 := by
  apply nodeValid_prime [2, 43, 83, 536651] ⟨7661229677, 2, [(2, 2), (43, 1), (83, 1), (536651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_83
    · exact prime_536651
  · decide +kernel

theorem prime_9054540637 : Nat.Prime 9054540637 := by
  apply nodeValid_prime [2, 3, 31, 4729, 5147] ⟨9054540637, 2, [(2, 2), (3, 1), (31, 1), (4729, 1), (5147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_4729
    · exact prime_5147
  · decide +kernel

theorem prime_9557503573 : Nat.Prime 9557503573 := by
  apply nodeValid_prime [2, 3, 796458631] ⟨9557503573, 2, [(2, 2), (3, 1), (796458631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_796458631
  · decide +kernel

theorem prime_18689233427 : Nat.Prime 18689233427 := by
  apply nodeValid_prime [2, 211, 1129, 39227] ⟨18689233427, 2, [(2, 1), (211, 1), (1129, 1), (39227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_1129
    · exact prime_39227
  · decide +kernel

theorem prime_27069508231 : Nat.Prime 27069508231 := by
  apply nodeValid_prime [2, 3, 5, 61, 2801, 5281] ⟨27069508231, 12, [(2, 1), (3, 1), (5, 1), (61, 1), (2801, 1), (5281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_2801
    · exact prime_5281
  · decide +kernel

theorem prime_185954980633 : Nat.Prime 185954980633 := by
  apply nodeValid_prime [2, 3, 97, 79877569] ⟨185954980633, 5, [(2, 3), (3, 1), (97, 1), (79877569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_79877569
  · decide +kernel

theorem prime_185954980831 : Nat.Prime 185954980831 := by
  apply nodeValid_prime [2, 3, 5, 193, 32116577] ⟨185954980831, 7, [(2, 1), (3, 1), (5, 1), (193, 1), (32116577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_193
    · exact prime_32116577
  · decide +kernel

theorem prime_189013085531 : Nat.Prime 189013085531 := by
  apply nodeValid_prime [2, 5, 337, 397, 141277] ⟨189013085531, 2, [(2, 1), (5, 1), (337, 1), (397, 1), (141277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_337
    · exact prime_397
    · exact prime_141277
  · decide +kernel

theorem prime_282456546997 : Nat.Prime 282456546997 := by
  apply nodeValid_prime [2, 3, 13, 31, 58407061] ⟨282456546997, 2, [(2, 2), (3, 1), (13, 1), (31, 1), (58407061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_58407061
  · decide +kernel

theorem prime_284941262587 : Nat.Prime 284941262587 := by
  apply nodeValid_prime [2, 3, 277, 171444803] ⟨284941262587, 3, [(2, 1), (3, 1), (277, 1), (171444803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_171444803
  · decide +kernel

theorem prime_284941264639 : Nat.Prime 284941264639 := by
  apply nodeValid_prime [2, 3, 31, 49417493] ⟨284941264639, 3, [(2, 1), (3, 1), (31, 2), (49417493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_49417493
  · decide +kernel

theorem prime_559269767663 : Nat.Prime 559269767663 := by
  apply nodeValid_prime [2, 37, 73, 103530131] ⟨559269767663, 5, [(2, 1), (37, 1), (73, 1), (103530131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_73
    · exact prime_103530131
  · decide +kernel

theorem prime_567749190941 : Nat.Prime 567749190941 := by
  apply nodeValid_prime [2, 5, 47, 603988501] ⟨567749190941, 2, [(2, 2), (5, 1), (47, 1), (603988501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_603988501
  · decide +kernel

theorem prime_1114326776809 : Nat.Prime 1114326776809 := by
  apply nodeValid_prime [2, 3, 7, 23, 4577569] ⟨1114326776809, 29, [(2, 3), (3, 3), (7, 2), (23, 1), (4577569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_4577569
  · decide +kernel

theorem prime_1114326776867 : Nat.Prime 1114326776867 := by
  apply nodeValid_prime [2, 173, 3220597621] ⟨1114326776867, 2, [(2, 1), (173, 1), (3220597621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_3220597621
  · decide +kernel

theorem prime_1114326809747 : Nat.Prime 1114326809747 := by
  apply nodeValid_prime [2, 20593, 27055961] ⟨1114326809747, 2, [(2, 1), (20593, 1), (27055961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_20593
    · exact prime_27055961
  · decide +kernel

theorem prime_1115729855299 : Nat.Prime 1115729855299 := by
  apply nodeValid_prime [2, 3, 37, 1676947] ⟨1115729855299, 2, [(2, 1), (3, 5), (37, 2), (1676947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1676947
  · decide +kernel

theorem prime_1115729883799 : Nat.Prime 1115729883799 := by
  apply nodeValid_prime [2, 3, 185954980633] ⟨1115729883799, 3, [(2, 1), (3, 1), (185954980633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_185954980633
  · decide +kernel

theorem prime_1115729884987 : Nat.Prime 1115729884987 := by
  apply nodeValid_prime [2, 3, 185954980831] ⟨1115729884987, 2, [(2, 1), (3, 1), (185954980831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_185954980831
  · decide +kernel

theorem prime_1117134095717 : Nat.Prime 1117134095717 := by
  apply nodeValid_prime [2, 877, 9851, 32327] ⟨1117134095717, 2, [(2, 2), (877, 1), (9851, 1), (32327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_877
    · exact prime_9851
    · exact prime_32327
  · decide +kernel

theorem prime_1117134165821 : Nat.Prime 1117134165821 := by
  apply nodeValid_prime [2, 5, 17, 24317, 135119] ⟨1117134165821, 2, [(2, 2), (5, 1), (17, 1), (24317, 1), (135119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_24317
    · exact prime_135119
  · decide +kernel

theorem prime_1117134166363 : Nat.Prime 1117134166363 := by
  apply nodeValid_prime [2, 3, 43, 463, 9352003] ⟨1117134166363, 2, [(2, 1), (3, 1), (43, 1), (463, 1), (9352003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_463
    · exact prime_9352003
  · decide +kernel

theorem prime_1118539532843 : Nat.Prime 1118539532843 := by
  apply nodeValid_prime [2, 73, 7661229677] ⟨1118539532843, 2, [(2, 1), (73, 1), (7661229677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_7661229677
  · decide +kernel

theorem prime_1118539535327 : Nat.Prime 1118539535327 := by
  apply nodeValid_prime [2, 559269767663] ⟨1118539535327, 5, [(2, 1), (559269767663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_559269767663
  · decide +kernel

theorem prime_1118539537499 : Nat.Prime 1118539537499 := by
  apply nodeValid_prime [2, 313, 1786804373] ⟨1118539537499, 2, [(2, 1), (313, 1), (1786804373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_313
    · exact prime_1786804373
  · decide +kernel

theorem prime_1119946169561 : Nat.Prime 1119946169561 := by
  apply nodeValid_prime [2, 5, 19, 23, 613, 5501] ⟨1119946169561, 3, [(2, 3), (5, 1), (19, 2), (23, 1), (613, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_613
    · exact prime_5501
  · decide +kernel

theorem prime_1119946174211 : Nat.Prime 1119946174211 := by
  apply nodeValid_prime [2, 5, 65101, 1720321] ⟨1119946174211, 2, [(2, 1), (5, 1), (65101, 1), (1720321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_65101
    · exact prime_1720321
  · decide +kernel

theorem prime_1119946175501 : Nat.Prime 1119946175501 := by
  apply nodeValid_prime [2, 5, 3677, 609163] ⟨1119946175501, 2, [(2, 2), (5, 3), (3677, 1), (609163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3677
    · exact prime_609163
  · decide +kernel

theorem prime_1121353952003 : Nat.Prime 1121353952003 := by
  apply nodeValid_prime [2, 811, 821, 842071] ⟨1121353952003, 2, [(2, 1), (811, 1), (821, 1), (842071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_811
    · exact prime_821
    · exact prime_842071
  · decide +kernel

theorem prime_1121353952839 : Nat.Prime 1121353952839 := by
  apply nodeValid_prime [2, 3, 7, 84059, 317621] ⟨1121353952839, 3, [(2, 1), (3, 1), (7, 1), (84059, 1), (317621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_84059
    · exact prime_317621
  · decide +kernel

theorem prime_1121354005621 : Nat.Prime 1121354005621 := by
  apply nodeValid_prime [2, 3, 5, 18689233427] ⟨1121354005621, 17, [(2, 2), (3, 1), (5, 1), (18689233427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18689233427
  · decide +kernel

theorem prime_1122763007153 : Nat.Prime 1122763007153 := by
  apply nodeValid_prime [2, 239, 293609573] ⟨1122763007153, 3, [(2, 4), (239, 1), (293609573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_293609573
  · decide +kernel

theorem prime_1122763007453 : Nat.Prime 1122763007453 := by
  apply nodeValid_prime [2, 477839, 587417] ⟨1122763007453, 2, [(2, 2), (477839, 1), (587417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_477839
    · exact prime_587417
  · decide +kernel

theorem prime_1122763038989 : Nat.Prime 1122763038989 := by
  apply nodeValid_prime [2, 31, 9054540637] ⟨1122763038989, 3, [(2, 2), (31, 1), (9054540637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_9054540637
  · decide +kernel

theorem prime_1124173273033 : Nat.Prime 1124173273033 := by
  apply nodeValid_prime [2, 3, 337, 46330913] ⟨1124173273033, 5, [(2, 3), (3, 2), (337, 1), (46330913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
    · exact prime_46330913
  · decide +kernel

theorem prime_1124173298009 : Nat.Prime 1124173298009 := by
  apply nodeValid_prime [2, 59, 2381723089] ⟨1124173298009, 3, [(2, 3), (59, 1), (2381723089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2381723089
  · decide +kernel

theorem prime_1125584702747 : Nat.Prime 1125584702747 := by
  apply nodeValid_prime [2, 7, 1277, 62959207] ⟨1125584702747, 2, [(2, 1), (7, 1), (1277, 1), (62959207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1277
    · exact prime_62959207
  · decide +kernel

theorem prime_1125584776027 : Nat.Prime 1125584776027 := by
  apply nodeValid_prime [2, 3, 17, 408709069] ⟨1125584776027, 3, [(2, 1), (3, 4), (17, 1), (408709069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_408709069
  · decide +kernel

theorem prime_1125584776073 : Nat.Prime 1125584776073 := by
  apply nodeValid_prime [2, 521, 5717, 47237] ⟨1125584776073, 3, [(2, 3), (521, 1), (5717, 1), (47237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_521
    · exact prime_5717
    · exact prime_47237
  · decide +kernel

theorem prime_1126997283029 : Nat.Prime 1126997283029 := by
  apply nodeValid_prime [2, 389, 724291313] ⟨1126997283029, 2, [(2, 2), (389, 1), (724291313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_389
    · exact prime_724291313
  · decide +kernel

theorem prime_1126997283143 : Nat.Prime 1126997283143 := by
  apply nodeValid_prime [2, 101, 457, 12208303] ⟨1126997283143, 5, [(2, 1), (101, 1), (457, 1), (12208303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_457
    · exact prime_12208303
  · decide +kernel

theorem prime_1126997330587 : Nat.Prime 1126997330587 := by
  apply nodeValid_prime [2, 3, 1907, 98496533] ⟨1126997330587, 2, [(2, 1), (3, 1), (1907, 1), (98496533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1907
    · exact prime_98496533
  · decide +kernel

theorem prime_1128411140203 : Nat.Prime 1128411140203 := by
  apply nodeValid_prime [2, 3, 61, 29803, 34483] ⟨1128411140203, 2, [(2, 1), (3, 2), (61, 1), (29803, 1), (34483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_29803
    · exact prime_34483
  · decide +kernel

theorem prime_1128411141211 : Nat.Prime 1128411141211 := by
  apply nodeValid_prime [2, 3, 5, 3023, 1382501] ⟨1128411141211, 2, [(2, 1), (3, 3), (5, 1), (3023, 1), (1382501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3023
    · exact prime_1382501
  · decide +kernel

theorem prime_1128411157297 : Nat.Prime 1128411157297 := by
  apply nodeValid_prime [2, 3, 101, 232758077] ⟨1128411157297, 11, [(2, 4), (3, 1), (101, 1), (232758077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_232758077
  · decide +kernel

theorem prime_1129826187683 : Nat.Prime 1129826187683 := by
  apply nodeValid_prime [2, 293, 1928031037] ⟨1129826187683, 2, [(2, 1), (293, 1), (1928031037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_1928031037
  · decide +kernel

theorem prime_1129826187823 : Nat.Prime 1129826187823 := by
  apply nodeValid_prime [2, 3, 29, 6493253953] ⟨1129826187823, 3, [(2, 1), (3, 1), (29, 1), (6493253953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_6493253953
  · decide +kernel

theorem prime_1129826187989 : Nat.Prime 1129826187989 := by
  apply nodeValid_prime [2, 282456546997] ⟨1129826187989, 2, [(2, 2), (282456546997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_282456546997
  · decide +kernel

theorem prime_1131242414413 : Nat.Prime 1131242414413 := by
  apply nodeValid_prime [2, 3, 11, 17, 504118723] ⟨1131242414413, 2, [(2, 2), (3, 1), (11, 1), (17, 1), (504118723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_504118723
  · decide +kernel

theorem prime_1131242539981 : Nat.Prime 1131242539981 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 117105853] ⟨1131242539981, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (23, 1), (117105853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_117105853
  · decide +kernel

theorem prime_1131242540123 : Nat.Prime 1131242540123 := by
  apply nodeValid_prime [2, 37, 257, 661, 89989] ⟨1131242540123, 2, [(2, 1), (37, 1), (257, 1), (661, 1), (89989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_257
    · exact prime_661
    · exact prime_89989
  · decide +kernel

theorem prime_1132659831503 : Nat.Prime 1132659831503 := by
  apply nodeValid_prime [2, 43, 83, 9209, 17231] ⟨1132659831503, 5, [(2, 1), (43, 1), (83, 1), (9209, 1), (17231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_83
    · exact prime_9209
    · exact prime_17231
  · decide +kernel

theorem prime_1132659832331 : Nat.Prime 1132659832331 := by
  apply nodeValid_prime [2, 5, 13, 89, 311, 314779] ⟨1132659832331, 2, [(2, 1), (5, 1), (13, 1), (89, 1), (311, 1), (314779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_89
    · exact prime_311
    · exact prime_314779
  · decide +kernel

theorem prime_1132659840469 : Nat.Prime 1132659840469 := by
  apply nodeValid_prime [2, 3, 13, 467, 15547409] ⟨1132659840469, 6, [(2, 2), (3, 1), (13, 1), (467, 1), (15547409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_467
    · exact prime_15547409
  · decide +kernel

theorem prime_1134078471863 : Nat.Prime 1134078471863 := by
  apply nodeValid_prime [2, 7, 5099, 15886567] ⟨1134078471863, 5, [(2, 1), (7, 1), (5099, 1), (15886567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5099
    · exact prime_15886567
  · decide +kernel

theorem prime_1134078512659 : Nat.Prime 1134078512659 := by
  apply nodeValid_prime [2, 3, 7, 13, 53, 71, 78853] ⟨1134078512659, 2, [(2, 1), (3, 1), (7, 2), (13, 1), (53, 1), (71, 1), (78853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_53
    · exact prime_71
    · exact prime_78853
  · decide +kernel

theorem prime_1134078513187 : Nat.Prime 1134078513187 := by
  apply nodeValid_prime [2, 3, 189013085531] ⟨1134078513187, 2, [(2, 1), (3, 1), (189013085531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_189013085531
  · decide +kernel

theorem prime_1135498304233 : Nat.Prime 1135498304233 := by
  apply nodeValid_prime [2, 3, 17, 331, 827, 3389] ⟨1135498304233, 5, [(2, 3), (3, 2), (17, 1), (331, 1), (827, 1), (3389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_331
    · exact prime_827
    · exact prime_3389
  · decide +kernel

theorem prime_1135498380773 : Nat.Prime 1135498380773 := by
  apply nodeValid_prime [2, 7, 103, 393723433] ⟨1135498380773, 2, [(2, 2), (7, 1), (103, 1), (393723433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_103
    · exact prime_393723433
  · decide +kernel

theorem prime_1135498381883 : Nat.Prime 1135498381883 := by
  apply nodeValid_prime [2, 567749190941] ⟨1135498381883, 2, [(2, 1), (567749190941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_567749190941
  · decide +kernel

theorem prime_1136919345703 : Nat.Prime 1136919345703 := by
  apply nodeValid_prime [2, 3, 7, 27069508231] ⟨1136919345703, 7, [(2, 1), (3, 1), (7, 1), (27069508231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_27069508231
  · decide +kernel

theorem prime_1136919370397 : Nat.Prime 1136919370397 := by
  apply nodeValid_prime [2, 32441, 8761439] ⟨1136919370397, 2, [(2, 2), (32441, 1), (8761439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32441
    · exact prime_8761439
  · decide +kernel

theorem prime_1136919370777 : Nat.Prime 1136919370777 := by
  apply nodeValid_prime [2, 3, 7, 14731, 459397] ⟨1136919370777, 10, [(2, 3), (3, 1), (7, 1), (14731, 1), (459397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14731
    · exact prime_459397
  · decide +kernel

theorem prime_1138341595789 : Nat.Prime 1138341595789 := by
  apply nodeValid_prime [2, 3, 1069, 1095541] ⟨1138341595789, 2, [(2, 2), (3, 5), (1069, 1), (1095541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
    · exact prime_1095541
  · decide +kernel

theorem prime_1138341734219 : Nat.Prime 1138341734219 := by
  apply nodeValid_prime [2, 13, 37363, 1171811] ⟨1138341734219, 2, [(2, 1), (13, 1), (37363, 1), (1171811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37363
    · exact prime_1171811
  · decide +kernel

theorem prime_1138341735491 : Nat.Prime 1138341735491 := by
  apply nodeValid_prime [2, 5, 71, 151, 10617869] ⟨1138341735491, 2, [(2, 1), (5, 1), (71, 1), (151, 1), (10617869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_151
    · exact prime_10617869
  · decide +kernel

theorem prime_1139765050349 : Nat.Prime 1139765050349 := by
  apply nodeValid_prime [2, 284941262587] ⟨1139765050349, 2, [(2, 2), (284941262587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_284941262587
  · decide +kernel

theorem prime_1139765058557 : Nat.Prime 1139765058557 := by
  apply nodeValid_prime [2, 284941264639] ⟨1139765058557, 2, [(2, 2), (284941264639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_284941264639
  · decide +kernel

theorem prime_1139765058577 : Nat.Prime 1139765058577 := by
  apply nodeValid_prime [2, 3, 2638345043] ⟨1139765058577, 5, [(2, 4), (3, 3), (2638345043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2638345043
  · decide +kernel

theorem prime_1141189706513 : Nat.Prime 1141189706513 := by
  apply nodeValid_prime [2, 193433, 368729] ⟨1141189706513, 3, [(2, 4), (193433, 1), (368729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193433
    · exact prime_368729
  · decide +kernel

theorem prime_1141189708733 : Nat.Prime 1141189708733 := by
  apply nodeValid_prime [2, 17, 61, 2003, 137353] ⟨1141189708733, 2, [(2, 2), (17, 1), (61, 1), (2003, 1), (137353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_2003
    · exact prime_137353
  · decide +kernel

theorem prime_1141189709053 : Nat.Prime 1141189709053 := by
  apply nodeValid_prime [2, 3, 2381, 39940841] ⟨1141189709053, 6, [(2, 2), (3, 1), (2381, 1), (39940841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2381
    · exact prime_39940841
  · decide +kernel

theorem prime_1142615572309 : Nat.Prime 1142615572309 := by
  apply nodeValid_prime [2, 3, 7, 17, 229, 383, 3041] ⟨1142615572309, 2, [(2, 2), (3, 2), (7, 1), (17, 1), (229, 1), (383, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_229
    · exact prime_383
    · exact prime_3041
  · decide +kernel

theorem prime_1142615586337 : Nat.Prime 1142615586337 := by
  apply nodeValid_prime [2, 3, 7, 1700320813] ⟨1142615586337, 15, [(2, 5), (3, 1), (7, 1), (1700320813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1700320813
  · decide +kernel

theorem prime_1144042595141 : Nat.Prime 1144042595141 := by
  apply nodeValid_prime [2, 5, 29, 59, 599, 55813] ⟨1144042595141, 2, [(2, 2), (5, 1), (29, 1), (59, 1), (599, 1), (55813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_59
    · exact prime_599
    · exact prime_55813
  · decide +kernel

theorem prime_1144042595953 : Nat.Prime 1144042595953 := by
  apply nodeValid_prime [2, 3, 19, 29, 43256299] ⟨1144042595953, 5, [(2, 4), (3, 1), (19, 1), (29, 1), (43256299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_43256299
  · decide +kernel

theorem prime_1144042641869 : Nat.Prime 1144042641869 := by
  apply nodeValid_prime [2, 7, 59, 1583, 437473] ⟨1144042641869, 2, [(2, 2), (7, 1), (59, 1), (1583, 1), (437473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_1583
    · exact prime_437473
  · decide +kernel

theorem prime_1145470900537 : Nat.Prime 1145470900537 := by
  apply nodeValid_prime [2, 3, 17, 23, 43, 47, 2237] ⟨1145470900537, 5, [(2, 3), (3, 4), (17, 1), (23, 1), (43, 1), (47, 1), (2237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_43
    · exact prime_47
    · exact prime_2237
  · decide +kernel

theorem prime_1145470900879 : Nat.Prime 1145470900879 := by
  apply nodeValid_prime [2, 3, 29, 829, 2647031] ⟨1145470900879, 3, [(2, 1), (3, 2), (29, 1), (829, 1), (2647031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_829
    · exact prime_2647031
  · decide +kernel

theorem prime_1145470918859 : Nat.Prime 1145470918859 := by
  apply nodeValid_prime [2, 7, 29, 127, 22215409] ⟨1145470918859, 2, [(2, 1), (7, 1), (29, 1), (127, 1), (22215409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_127
    · exact prime_22215409
  · decide +kernel

theorem prime_1146900398191 : Nat.Prime 1146900398191 := by
  apply nodeValid_prime [2, 3, 5, 293, 130477861] ⟨1146900398191, 3, [(2, 1), (3, 1), (5, 1), (293, 1), (130477861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_130477861
  · decide +kernel

theorem prime_1146900428677 : Nat.Prime 1146900428677 := by
  apply nodeValid_prime [2, 3, 29, 1098563629] ⟨1146900428677, 5, [(2, 2), (3, 2), (29, 1), (1098563629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1098563629
  · decide +kernel

theorem prime_1146900428761 : Nat.Prime 1146900428761 := by
  apply nodeValid_prime [2, 3, 5, 9557503573] ⟨1146900428761, 11, [(2, 3), (3, 1), (5, 1), (9557503573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9557503573
  · decide +kernel

theorem prime_1148331089989 : Nat.Prime 1148331089989 := by
  apply nodeValid_prime [2, 3, 2011, 15861803] ⟨1148331089989, 2, [(2, 2), (3, 2), (2011, 1), (15861803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2011
    · exact prime_15861803
  · decide +kernel

theorem prime_1148331091289 : Nat.Prime 1148331091289 := by
  apply nodeValid_prime [2, 43, 499, 6689723] ⟨1148331091289, 3, [(2, 3), (43, 1), (499, 1), (6689723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_499
    · exact prime_6689723
  · decide +kernel

theorem prime_1148331093289 : Nat.Prime 1148331093289 := by
  apply nodeValid_prime [2, 3, 17011, 2812717] ⟨1148331093289, 22, [(2, 3), (3, 1), (17011, 1), (2812717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17011
    · exact prime_2812717
  · decide +kernel

end Sude.Lucas.Generated
