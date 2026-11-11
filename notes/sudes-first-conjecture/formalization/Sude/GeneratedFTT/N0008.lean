import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_823 : Nat.Prime 823 := by
  apply nodeValid_prime [2, 3, 137] ⟨823, 3, [(2, 1), (3, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_863 : Nat.Prime 863 := by
  apply nodeValid_prime [2, 431] ⟨863, 5, [(2, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_431
  · decide +kernel

theorem prime_1181 : Nat.Prime 1181 := by
  apply nodeValid_prime [2, 5, 59] ⟨1181, 7, [(2, 2), (5, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_1451 : Nat.Prime 1451 := by
  apply nodeValid_prime [2, 5, 29] ⟨1451, 2, [(2, 1), (5, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_1483 : Nat.Prime 1483 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨1483, 2, [(2, 1), (3, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_1549 : Nat.Prime 1549 := by
  apply nodeValid_prime [2, 3, 43] ⟨1549, 2, [(2, 2), (3, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_1597 : Nat.Prime 1597 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨1597, 11, [(2, 2), (3, 1), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_1709 : Nat.Prime 1709 := by
  apply nodeValid_prime [2, 7, 61] ⟨1709, 3, [(2, 2), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_1993 : Nat.Prime 1993 := by
  apply nodeValid_prime [2, 3, 83] ⟨1993, 5, [(2, 3), (3, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_1997 : Nat.Prime 1997 := by
  apply nodeValid_prime [2, 499] ⟨1997, 2, [(2, 2), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_499
  · decide +kernel

theorem prime_2137 : Nat.Prime 2137 := by
  apply nodeValid_prime [2, 3, 89] ⟨2137, 10, [(2, 3), (3, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_2341 : Nat.Prime 2341 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨2341, 7, [(2, 2), (3, 2), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_2593 : Nat.Prime 2593 := by
  apply nodeValid_prime [2, 3] ⟨2593, 7, [(2, 5), (3, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_2657 : Nat.Prime 2657 := by
  apply nodeValid_prime [2, 83] ⟨2657, 3, [(2, 5), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_83
  · decide +kernel

theorem prime_2663 : Nat.Prime 2663 := by
  apply nodeValid_prime [2, 11] ⟨2663, 5, [(2, 1), (11, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel

theorem prime_2953 : Nat.Prime 2953 := by
  apply nodeValid_prime [2, 3, 41] ⟨2953, 13, [(2, 3), (3, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_3181 : Nat.Prime 3181 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨3181, 7, [(2, 2), (3, 1), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_3607 : Nat.Prime 3607 := by
  apply nodeValid_prime [2, 3, 601] ⟨3607, 5, [(2, 1), (3, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
  · decide +kernel

theorem prime_3889 : Nat.Prime 3889 := by
  apply nodeValid_prime [2, 3] ⟨3889, 11, [(2, 4), (3, 5)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_4127 : Nat.Prime 4127 := by
  apply nodeValid_prime [2, 2063] ⟨4127, 5, [(2, 1), (2063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2063
  · decide +kernel

theorem prime_4339 : Nat.Prime 4339 := by
  apply nodeValid_prime [2, 3, 241] ⟨4339, 10, [(2, 1), (3, 2), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel

theorem prime_5179 : Nat.Prime 5179 := by
  apply nodeValid_prime [2, 3, 863] ⟨5179, 2, [(2, 1), (3, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863
  · decide +kernel

theorem prime_5651 : Nat.Prime 5651 := by
  apply nodeValid_prime [2, 5, 113] ⟨5651, 2, [(2, 1), (5, 2), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_6053 : Nat.Prime 6053 := by
  apply nodeValid_prime [2, 17, 89] ⟨6053, 2, [(2, 2), (17, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_89
  · decide +kernel

theorem prime_6197 : Nat.Prime 6197 := by
  apply nodeValid_prime [2, 1549] ⟨6197, 2, [(2, 2), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1549
  · decide +kernel

theorem prime_6389 : Nat.Prime 6389 := by
  apply nodeValid_prime [2, 1597] ⟨6389, 2, [(2, 2), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1597
  · decide +kernel

theorem prime_6529 : Nat.Prime 6529 := by
  apply nodeValid_prime [2, 3, 17] ⟨6529, 7, [(2, 7), (3, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_6547 : Nat.Prime 6547 := by
  apply nodeValid_prime [2, 3, 1091] ⟨6547, 2, [(2, 1), (3, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
  · decide +kernel

theorem prime_8243 : Nat.Prime 8243 := by
  apply nodeValid_prime [2, 13, 317] ⟨8243, 2, [(2, 1), (13, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_317
  · decide +kernel

theorem prime_8431 : Nat.Prime 8431 := by
  apply nodeValid_prime [2, 3, 5, 281] ⟨8431, 3, [(2, 1), (3, 1), (5, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_281
  · decide +kernel

theorem prime_9413 : Nat.Prime 9413 := by
  apply nodeValid_prime [2, 13, 181] ⟨9413, 3, [(2, 2), (13, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_181
  · decide +kernel

theorem prime_9689 : Nat.Prime 9689 := by
  apply nodeValid_prime [2, 7, 173] ⟨9689, 3, [(2, 3), (7, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_173
  · decide +kernel

theorem prime_12011 : Nat.Prime 12011 := by
  apply nodeValid_prime [2, 5, 1201] ⟨12011, 2, [(2, 1), (5, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1201
  · decide +kernel

theorem prime_12497 : Nat.Prime 12497 := by
  apply nodeValid_prime [2, 11, 71] ⟨12497, 3, [(2, 4), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_13109 : Nat.Prime 13109 := by
  apply nodeValid_prime [2, 29, 113] ⟨13109, 2, [(2, 2), (29, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_113
  · decide +kernel

theorem prime_14747 : Nat.Prime 14747 := by
  apply nodeValid_prime [2, 73, 101] ⟨14747, 2, [(2, 1), (73, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_101
  · decide +kernel

theorem prime_15269 : Nat.Prime 15269 := by
  apply nodeValid_prime [2, 11, 347] ⟨15269, 2, [(2, 2), (11, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_347
  · decide +kernel

theorem prime_15661 : Nat.Prime 15661 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨15661, 2, [(2, 2), (3, 3), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_15671 : Nat.Prime 15671 := by
  apply nodeValid_prime [2, 5, 1567] ⟨15671, 13, [(2, 1), (5, 1), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1567
  · decide +kernel

theorem prime_16097 : Nat.Prime 16097 := by
  apply nodeValid_prime [2, 503] ⟨16097, 3, [(2, 5), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_503
  · decide +kernel

theorem prime_16903 : Nat.Prime 16903 := by
  apply nodeValid_prime [2, 3, 313] ⟨16903, 3, [(2, 1), (3, 3), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
  · decide +kernel

theorem prime_19603 : Nat.Prime 19603 := by
  apply nodeValid_prime [2, 3, 11] ⟨19603, 2, [(2, 1), (3, 4), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_20353 : Nat.Prime 20353 := by
  apply nodeValid_prime [2, 3, 53] ⟨20353, 5, [(2, 7), (3, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
  · decide +kernel

theorem prime_21341 : Nat.Prime 21341 := by
  apply nodeValid_prime [2, 5, 11, 97] ⟨21341, 2, [(2, 2), (5, 1), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_23917 : Nat.Prime 23917 := by
  apply nodeValid_prime [2, 3, 1993] ⟨23917, 2, [(2, 2), (3, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1993
  · decide +kernel

theorem prime_26119 : Nat.Prime 26119 := by
  apply nodeValid_prime [2, 3, 1451] ⟨26119, 3, [(2, 1), (3, 2), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
  · decide +kernel

theorem prime_26227 : Nat.Prime 26227 := by
  apply nodeValid_prime [2, 3, 31, 47] ⟨26227, 3, [(2, 1), (3, 2), (31, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_47
  · decide +kernel

theorem prime_30539 : Nat.Prime 30539 := by
  apply nodeValid_prime [2, 15269] ⟨30539, 2, [(2, 1), (15269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15269
  · decide +kernel

theorem prime_31259 : Nat.Prime 31259 := by
  apply nodeValid_prime [2, 15629] ⟨31259, 2, [(2, 1), (15629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15629
  · decide +kernel

theorem prime_32369 : Nat.Prime 32369 := by
  apply nodeValid_prime [2, 7, 17] ⟨32369, 6, [(2, 4), (7, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_32783 : Nat.Prime 32783 := by
  apply nodeValid_prime [2, 37, 443] ⟨32783, 7, [(2, 1), (37, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_443
  · decide +kernel

theorem prime_33301 : Nat.Prime 33301 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨33301, 2, [(2, 2), (3, 2), (5, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_35593 : Nat.Prime 35593 := by
  apply nodeValid_prime [2, 3, 1483] ⟨35593, 5, [(2, 3), (3, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1483
  · decide +kernel

theorem prime_37567 : Nat.Prime 37567 := by
  apply nodeValid_prime [2, 3, 2087] ⟨37567, 3, [(2, 1), (3, 2), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2087
  · decide +kernel

theorem prime_38891 : Nat.Prime 38891 := by
  apply nodeValid_prime [2, 5, 3889] ⟨38891, 2, [(2, 1), (5, 1), (3889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3889
  · decide +kernel

theorem prime_40177 : Nat.Prime 40177 := by
  apply nodeValid_prime [2, 3, 31] ⟨40177, 10, [(2, 4), (3, 4), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_41017 : Nat.Prime 41017 := by
  apply nodeValid_prime [2, 3, 1709] ⟨41017, 5, [(2, 3), (3, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1709
  · decide +kernel

theorem prime_42463 : Nat.Prime 42463 := by
  apply nodeValid_prime [2, 3, 7, 337] ⟨42463, 3, [(2, 1), (3, 2), (7, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_337
  · decide +kernel

theorem prime_47807 : Nat.Prime 47807 := by
  apply nodeValid_prime [2, 11, 41, 53] ⟨47807, 5, [(2, 1), (11, 1), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_48781 : Nat.Prime 48781 := by
  apply nodeValid_prime [2, 3, 5, 271] ⟨48781, 6, [(2, 2), (3, 2), (5, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
  · decide +kernel

theorem prime_49603 : Nat.Prime 49603 := by
  apply nodeValid_prime [2, 3, 7, 1181] ⟨49603, 3, [(2, 1), (3, 1), (7, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1181
  · decide +kernel

theorem prime_57413 : Nat.Prime 57413 := by
  apply nodeValid_prime [2, 31, 463] ⟨57413, 2, [(2, 2), (31, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_463
  · decide +kernel

theorem prime_63691 : Nat.Prime 63691 := by
  apply nodeValid_prime [2, 3, 5, 11, 193] ⟨63691, 15, [(2, 1), (3, 1), (5, 1), (11, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_193
  · decide +kernel

theorem prime_72739 : Nat.Prime 72739 := by
  apply nodeValid_prime [2, 3, 449] ⟨72739, 2, [(2, 1), (3, 4), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
  · decide +kernel

theorem prime_78893 : Nat.Prime 78893 := by
  apply nodeValid_prime [2, 11, 163] ⟨78893, 2, [(2, 2), (11, 2), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_163
  · decide +kernel

theorem prime_82727 : Nat.Prime 82727 := by
  apply nodeValid_prime [2, 7, 19, 311] ⟨82727, 5, [(2, 1), (7, 1), (19, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_311
  · decide +kernel

theorem prime_88591 : Nat.Prime 88591 := by
  apply nodeValid_prime [2, 3, 5, 2953] ⟨88591, 15, [(2, 1), (3, 1), (5, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2953
  · decide +kernel

theorem prime_100207 : Nat.Prime 100207 := by
  apply nodeValid_prime [2, 3, 19, 293] ⟨100207, 3, [(2, 1), (3, 2), (19, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_293
  · decide +kernel

theorem prime_100769 : Nat.Prime 100769 := by
  apply nodeValid_prime [2, 47, 67] ⟨100769, 3, [(2, 5), (47, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_67
  · decide +kernel

theorem prime_101383 : Nat.Prime 101383 := by
  apply nodeValid_prime [2, 3, 61, 277] ⟨101383, 3, [(2, 1), (3, 1), (61, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_277
  · decide +kernel

theorem prime_113209 : Nat.Prime 113209 := by
  apply nodeValid_prime [2, 3, 53, 89] ⟨113209, 7, [(2, 3), (3, 1), (53, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_89
  · decide +kernel

theorem prime_114827 : Nat.Prime 114827 := by
  apply nodeValid_prime [2, 57413] ⟨114827, 2, [(2, 1), (57413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57413
  · decide +kernel

theorem prime_135661 : Nat.Prime 135661 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 19] ⟨135661, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_136951 : Nat.Prime 136951 := by
  apply nodeValid_prime [2, 3, 5, 11, 83] ⟨136951, 3, [(2, 1), (3, 1), (5, 2), (11, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_83
  · decide +kernel

theorem prime_151783 : Nat.Prime 151783 := by
  apply nodeValid_prime [2, 3, 41, 617] ⟨151783, 5, [(2, 1), (3, 1), (41, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_617
  · decide +kernel

theorem prime_198413 : Nat.Prime 198413 := by
  apply nodeValid_prime [2, 49603] ⟨198413, 2, [(2, 2), (49603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49603
  · decide +kernel

theorem prime_221987 : Nat.Prime 221987 := by
  apply nodeValid_prime [2, 17, 6529] ⟨221987, 2, [(2, 1), (17, 1), (6529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_6529
  · decide +kernel

theorem prime_224947 : Nat.Prime 224947 := by
  apply nodeValid_prime [2, 3, 12497] ⟨224947, 2, [(2, 1), (3, 2), (12497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12497
  · decide +kernel

theorem prime_233347 : Nat.Prime 233347 := by
  apply nodeValid_prime [2, 3, 38891] ⟨233347, 2, [(2, 1), (3, 1), (38891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_38891
  · decide +kernel

theorem prime_244313 : Nat.Prime 244313 := by
  apply nodeValid_prime [2, 30539] ⟨244313, 3, [(2, 3), (30539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30539
  · decide +kernel

theorem prime_296981 : Nat.Prime 296981 := by
  apply nodeValid_prime [2, 5, 31, 479] ⟨296981, 2, [(2, 2), (5, 1), (31, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_479
  · decide +kernel

theorem prime_329473 : Nat.Prime 329473 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨329473, 5, [(2, 8), (3, 2), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_393271 : Nat.Prime 393271 := by
  apply nodeValid_prime [2, 3, 5, 13109] ⟨393271, 3, [(2, 1), (3, 1), (5, 1), (13109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13109
  · decide +kernel

theorem prime_434479 : Nat.Prime 434479 := by
  apply nodeValid_prime [2, 3, 11, 29, 227] ⟨434479, 3, [(2, 1), (3, 1), (11, 1), (29, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_227
  · decide +kernel

theorem prime_463283 : Nat.Prime 463283 := by
  apply nodeValid_prime [2, 43, 5387] ⟨463283, 2, [(2, 1), (43, 1), (5387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_5387
  · decide +kernel

theorem prime_470473 : Nat.Prime 470473 := by
  apply nodeValid_prime [2, 3, 19603] ⟨470473, 7, [(2, 3), (3, 1), (19603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19603
  · decide +kernel

theorem prime_572969 : Nat.Prime 572969 := by
  apply nodeValid_prime [2, 11, 17, 383] ⟨572969, 3, [(2, 3), (11, 1), (17, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_383
  · decide +kernel

theorem prime_590407 : Nat.Prime 590407 := by
  apply nodeValid_prime [2, 3, 19, 5179] ⟨590407, 3, [(2, 1), (3, 1), (19, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_5179
  · decide +kernel

theorem prime_764293 : Nat.Prime 764293 := by
  apply nodeValid_prime [2, 3, 63691] ⟨764293, 2, [(2, 2), (3, 1), (63691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63691
  · decide +kernel

theorem prime_772991 : Nat.Prime 772991 := by
  apply nodeValid_prime [2, 5, 17, 4547] ⟨772991, 7, [(2, 1), (5, 1), (17, 1), (4547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_4547
  · decide +kernel

theorem prime_806153 : Nat.Prime 806153 := by
  apply nodeValid_prime [2, 100769] ⟨806153, 3, [(2, 3), (100769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_100769
  · decide +kernel

theorem prime_878831 : Nat.Prime 878831 := by
  apply nodeValid_prime [2, 5, 23, 3821] ⟨878831, 13, [(2, 1), (5, 1), (23, 1), (3821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_3821
  · decide +kernel

theorem prime_926567 : Nat.Prime 926567 := by
  apply nodeValid_prime [2, 463283] ⟨926567, 5, [(2, 1), (463283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_463283
  · decide +kernel

theorem prime_995677 : Nat.Prime 995677 := by
  apply nodeValid_prime [2, 3, 11, 19, 397] ⟨995677, 2, [(2, 2), (3, 1), (11, 1), (19, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_397
  · decide +kernel

theorem prime_1127011 : Nat.Prime 1127011 := by
  apply nodeValid_prime [2, 3, 5, 37567] ⟨1127011, 7, [(2, 1), (3, 1), (5, 1), (37567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37567
  · decide +kernel

theorem prime_1132091 : Nat.Prime 1132091 := by
  apply nodeValid_prime [2, 5, 113209] ⟨1132091, 2, [(2, 1), (5, 1), (113209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113209
  · decide +kernel

theorem prime_1356611 : Nat.Prime 1356611 := by
  apply nodeValid_prime [2, 5, 135661] ⟨1356611, 2, [(2, 1), (5, 1), (135661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_135661
  · decide +kernel

theorem prime_1514101 : Nat.Prime 1514101 := by
  apply nodeValid_prime [2, 3, 5, 7, 103] ⟨1514101, 2, [(2, 2), (3, 1), (5, 2), (7, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_1545983 : Nat.Prime 1545983 := by
  apply nodeValid_prime [2, 772991] ⟨1545983, 5, [(2, 1), (772991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_772991
  · decide +kernel

theorem prime_1757663 : Nat.Prime 1757663 := by
  apply nodeValid_prime [2, 878831] ⟨1757663, 5, [(2, 1), (878831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_878831
  · decide +kernel

theorem prime_1909573 : Nat.Prime 1909573 := by
  apply nodeValid_prime [2, 3, 7, 127, 179] ⟨1909573, 2, [(2, 2), (3, 1), (7, 1), (127, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127
    · exact prime_179
  · decide +kernel

theorem prime_2264183 : Nat.Prime 2264183 := by
  apply nodeValid_prime [2, 1132091] ⟨2264183, 5, [(2, 1), (1132091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1132091
  · decide +kernel

theorem prime_2571329 : Nat.Prime 2571329 := by
  apply nodeValid_prime [2, 40177] ⟨2571329, 3, [(2, 6), (40177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40177
  · decide +kernel

theorem prime_3462523 : Nat.Prime 3462523 := by
  apply nodeValid_prime [2, 3, 7, 19, 4339] ⟨3462523, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (4339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_4339
  · decide +kernel

theorem prime_3769081 : Nat.Prime 3769081 := by
  apply nodeValid_prime [2, 3, 5, 7, 641] ⟨3769081, 11, [(2, 3), (3, 1), (5, 1), (7, 2), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_641
  · decide +kernel

theorem prime_4528367 : Nat.Prime 4528367 := by
  apply nodeValid_prime [2, 2264183] ⟨4528367, 5, [(2, 1), (2264183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2264183
  · decide +kernel

theorem prime_4668407 : Nat.Prime 4668407 := by
  apply nodeValid_prime [2, 89, 26227] ⟨4668407, 5, [(2, 1), (89, 1), (26227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_26227
  · decide +kernel

theorem prime_4957817 : Nat.Prime 4957817 := by
  apply nodeValid_prime [2, 239, 2593] ⟨4957817, 3, [(2, 3), (239, 1), (2593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_2593
  · decide +kernel

theorem prime_6510499 : Nat.Prime 6510499 := by
  apply nodeValid_prime [2, 3, 569, 1907] ⟨6510499, 2, [(2, 1), (3, 1), (569, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
    · exact prime_1907
  · decide +kernel

theorem prime_7682201 : Nat.Prime 7682201 := by
  apply nodeValid_prime [2, 5, 71, 541] ⟨7682201, 3, [(2, 3), (5, 2), (71, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_541
  · decide +kernel

theorem prime_8689799 : Nat.Prime 8689799 := by
  apply nodeValid_prime [2, 13, 283, 1181] ⟨8689799, 17, [(2, 1), (13, 1), (283, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_283
    · exact prime_1181
  · decide +kernel

theorem prime_9283271 : Nat.Prime 9283271 := by
  apply nodeValid_prime [2, 5, 43, 21589] ⟨9283271, 7, [(2, 1), (5, 1), (43, 1), (21589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_21589
  · decide +kernel

theorem prime_13377131 : Nat.Prime 13377131 := by
  apply nodeValid_prime [2, 5, 13, 17, 6053] ⟨13377131, 2, [(2, 1), (5, 1), (13, 1), (17, 1), (6053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_6053
  · decide +kernel

theorem prime_14643589 : Nat.Prime 14643589 := by
  apply nodeValid_prime [2, 3, 191, 6389] ⟨14643589, 2, [(2, 2), (3, 1), (191, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_6389
  · decide +kernel

theorem prime_14748301 : Nat.Prime 14748301 := by
  apply nodeValid_prime [2, 3, 5, 7, 2341] ⟨14748301, 6, [(2, 2), (3, 2), (5, 2), (7, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2341
  · decide +kernel

theorem prime_15113491 : Nat.Prime 15113491 := by
  apply nodeValid_prime [2, 3, 5, 7, 79, 911] ⟨15113491, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (79, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_79
    · exact prime_911
  · decide +kernel

theorem prime_20035357 : Nat.Prime 20035357 := by
  apply nodeValid_prime [2, 3, 11, 151783] ⟨20035357, 2, [(2, 2), (3, 1), (11, 1), (151783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_151783
  · decide +kernel

theorem prime_21540229 : Nat.Prime 21540229 := by
  apply nodeValid_prime [2, 3, 1117, 1607] ⟨21540229, 2, [(2, 2), (3, 1), (1117, 1), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1117
    · exact prime_1607
  · decide +kernel

theorem prime_24064699 : Nat.Prime 24064699 := by
  apply nodeValid_prime [2, 3, 7, 572969] ⟨24064699, 10, [(2, 1), (3, 1), (7, 1), (572969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_572969
  · decide +kernel

theorem prime_25907377 : Nat.Prime 25907377 := by
  apply nodeValid_prime [2, 3, 11, 139, 353] ⟨25907377, 5, [(2, 4), (3, 1), (11, 1), (139, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
    · exact prime_353
  · decide +kernel

theorem prime_31556309 : Nat.Prime 31556309 := by
  apply nodeValid_prime [2, 7, 1127011] ⟨31556309, 2, [(2, 2), (7, 1), (1127011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1127011
  · decide +kernel

theorem prime_31944013 : Nat.Prime 31944013 := by
  apply nodeValid_prime [2, 3, 31, 43, 1997] ⟨31944013, 2, [(2, 2), (3, 1), (31, 1), (43, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
    · exact prime_1997
  · decide +kernel

theorem prime_33689947 : Nat.Prime 33689947 := by
  apply nodeValid_prime [2, 3, 41, 136951] ⟨33689947, 2, [(2, 1), (3, 1), (41, 1), (136951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_136951
  · decide +kernel

theorem prime_38558417 : Nat.Prime 38558417 := by
  apply nodeValid_prime [2, 13, 197, 941] ⟨38558417, 3, [(2, 4), (13, 1), (197, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_197
    · exact prime_941
  · decide +kernel

theorem prime_43860409 : Nat.Prime 43860409 := by
  apply nodeValid_prime [2, 3, 17, 193, 557] ⟨43860409, 11, [(2, 3), (3, 1), (17, 1), (193, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_193
    · exact prime_557
  · decide +kernel

theorem prime_58574357 : Nat.Prime 58574357 := by
  apply nodeValid_prime [2, 14643589] ⟨58574357, 2, [(2, 2), (14643589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14643589
  · decide +kernel

theorem prime_62985161 : Nat.Prime 62985161 := by
  apply nodeValid_prime [2, 5, 7, 224947] ⟨62985161, 3, [(2, 3), (5, 1), (7, 1), (224947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_224947
  · decide +kernel

theorem prime_70385599 : Nat.Prime 70385599 := by
  apply nodeValid_prime [2, 3, 434479] ⟨70385599, 3, [(2, 1), (3, 4), (434479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_434479
  · decide +kernel

theorem prime_71981951 : Nat.Prime 71981951 := by
  apply nodeValid_prime [2, 5, 23, 53, 1181] ⟨71981951, 13, [(2, 1), (5, 2), (23, 1), (53, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_53
    · exact prime_1181
  · decide +kernel

theorem prime_118052887 : Nat.Prime 118052887 := by
  apply nodeValid_prime [2, 3, 7, 107, 109, 241] ⟨118052887, 3, [(2, 1), (3, 1), (7, 1), (107, 1), (109, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_109
    · exact prime_241
  · decide +kernel

theorem prime_120212143 : Nat.Prime 120212143 := by
  apply nodeValid_prime [2, 3, 20035357] ⟨120212143, 5, [(2, 1), (3, 1), (20035357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20035357
  · decide +kernel

theorem prime_153644021 : Nat.Prime 153644021 := by
  apply nodeValid_prime [2, 5, 7682201] ⟨153644021, 3, [(2, 2), (5, 1), (7682201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7682201
  · decide +kernel

theorem prime_219767131 : Nat.Prime 219767131 := by
  apply nodeValid_prime [2, 3, 5, 11, 221987] ⟨219767131, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (221987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_221987
  · decide +kernel

theorem prime_225502427 : Nat.Prime 225502427 := by
  apply nodeValid_prime [2, 3607, 31259] ⟨225502427, 2, [(2, 1), (3607, 1), (31259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3607
    · exact prime_31259
  · decide +kernel

theorem prime_278375047 : Nat.Prime 278375047 := by
  apply nodeValid_prime [2, 3, 463, 100207] ⟨278375047, 3, [(2, 1), (3, 1), (463, 1), (100207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
    · exact prime_100207
  · decide +kernel

theorem prime_319440131 : Nat.Prime 319440131 := by
  apply nodeValid_prime [2, 5, 31944013] ⟨319440131, 6, [(2, 1), (5, 1), (31944013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31944013
  · decide +kernel

theorem prime_463291753 : Nat.Prime 463291753 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 14747] ⟨463291753, 5, [(2, 3), (3, 1), (7, 1), (11, 1), (17, 1), (14747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_14747
  · decide +kernel

theorem prime_472211549 : Nat.Prime 472211549 := by
  apply nodeValid_prime [2, 118052887] ⟨472211549, 2, [(2, 2), (118052887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_118052887
  · decide +kernel

theorem prime_707877139 : Nat.Prime 707877139 := by
  apply nodeValid_prime [2, 3, 4517, 26119] ⟨707877139, 3, [(2, 1), (3, 1), (4517, 1), (26119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4517
    · exact prime_26119
  · decide +kernel

theorem prime_820040999 : Nat.Prime 820040999 := by
  apply nodeValid_prime [2, 7, 58574357] ⟨820040999, 7, [(2, 1), (7, 1), (58574357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_58574357
  · decide +kernel

theorem prime_957656369 : Nat.Prime 957656369 := by
  apply nodeValid_prime [2, 3541, 16903] ⟨957656369, 3, [(2, 4), (3541, 1), (16903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3541
    · exact prime_16903
  · decide +kernel

theorem prime_1113500189 : Nat.Prime 1113500189 := by
  apply nodeValid_prime [2, 278375047] ⟨1113500189, 2, [(2, 2), (278375047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_278375047
  · decide +kernel

theorem prime_1132559063 : Nat.Prime 1132559063 := by
  apply nodeValid_prime [2, 61, 9283271] ⟨1132559063, 5, [(2, 1), (61, 1), (9283271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_9283271
  · decide +kernel

theorem prime_1414060343 : Nat.Prime 1414060343 := by
  apply nodeValid_prime [2, 79, 1367, 6547] ⟨1414060343, 5, [(2, 1), (79, 1), (1367, 1), (6547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1367
    · exact prime_6547
  · decide +kernel

theorem prime_2813278417 : Nat.Prime 2813278417 := by
  apply nodeValid_prime [2, 3, 13, 1693, 2663] ⟨2813278417, 10, [(2, 4), (3, 1), (13, 1), (1693, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1693
    · exact prime_2663
  · decide +kernel

theorem prime_2850484997 : Nat.Prime 2850484997 := by
  apply nodeValid_prime [2, 17, 71, 590407] ⟨2850484997, 2, [(2, 2), (17, 1), (71, 1), (590407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_590407
  · decide +kernel

theorem prime_3488890763 : Nat.Prime 3488890763 := by
  apply nodeValid_prime [2, 7, 29, 97, 88591] ⟨3488890763, 2, [(2, 1), (7, 1), (29, 1), (97, 1), (88591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_97
    · exact prime_88591
  · decide +kernel

theorem prime_3692088157 : Nat.Prime 3692088157 := by
  apply nodeValid_prime [2, 3, 23, 13377131] ⟨3692088157, 2, [(2, 2), (3, 1), (23, 1), (13377131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_13377131
  · decide +kernel

theorem prime_3840653959 : Nat.Prime 3840653959 := by
  apply nodeValid_prime [2, 3, 19, 33689947] ⟨3840653959, 3, [(2, 1), (3, 1), (19, 1), (33689947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_33689947
  · decide +kernel

theorem prime_3955808359 : Nat.Prime 3955808359 := by
  apply nodeValid_prime [2, 3, 219767131] ⟨3955808359, 6, [(2, 1), (3, 2), (219767131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_219767131
  · decide +kernel

theorem prime_4750808767 : Nat.Prime 4750808767 := by
  apply nodeValid_prime [2, 3, 11, 71981951] ⟨4750808767, 3, [(2, 1), (3, 1), (11, 1), (71981951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_71981951
  · decide +kernel

theorem prime_9303709673 : Nat.Prime 9303709673 := by
  apply nodeValid_prime [2, 271, 509, 8431] ⟨9303709673, 3, [(2, 3), (271, 1), (509, 1), (8431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_509
    · exact prime_8431
  · decide +kernel

theorem prime_10988549101 : Nat.Prime 10988549101 := by
  apply nodeValid_prime [2, 3, 5, 1356611] ⟨10988549101, 2, [(2, 2), (3, 4), (5, 2), (1356611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1356611
  · decide +kernel

theorem prime_28804905427 : Nat.Prime 28804905427 := by
  apply nodeValid_prime [2, 3, 11, 19, 1427, 16097] ⟨28804905427, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (1427, 1), (16097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_1427
    · exact prime_16097
  · decide +kernel

theorem prime_54651674501 : Nat.Prime 54651674501 := by
  apply nodeValid_prime [2, 5, 29, 3769081] ⟨54651674501, 2, [(2, 2), (5, 3), (29, 1), (3769081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3769081
  · decide +kernel

theorem prime_55675009451 : Nat.Prime 55675009451 := by
  apply nodeValid_prime [2, 5, 1113500189] ⟨55675009451, 2, [(2, 1), (5, 2), (1113500189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1113500189
  · decide +kernel

theorem prime_56117529761 : Nat.Prime 56117529761 := by
  apply nodeValid_prime [2, 5, 1181, 296981] ⟨56117529761, 6, [(2, 5), (5, 1), (1181, 1), (296981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1181
    · exact prime_296981
  · decide +kernel

theorem prime_56562414521 : Nat.Prime 56562414521 := by
  apply nodeValid_prime [2, 5, 33301, 42463] ⟨56562414521, 3, [(2, 3), (5, 1), (33301, 1), (42463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33301
    · exact prime_42463
  · decide +kernel

theorem prime_56562419213 : Nat.Prime 56562419213 := by
  apply nodeValid_prime [2, 13, 233, 4668407] ⟨56562419213, 2, [(2, 2), (13, 1), (233, 1), (4668407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_233
    · exact prime_4668407
  · decide +kernel

theorem prime_57009699941 : Nat.Prime 57009699941 := by
  apply nodeValid_prime [2, 5, 2850484997] ⟨57009699941, 2, [(2, 2), (5, 1), (2850484997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2850484997
  · decide +kernel

theorem prime_57609808979 : Nat.Prime 57609808979 := by
  apply nodeValid_prime [2, 61, 472211549] ⟨57609808979, 2, [(2, 1), (61, 1), (472211549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_472211549
  · decide +kernel

theorem prime_109013079337 : Nat.Prime 109013079337 := by
  apply nodeValid_prime [2, 3, 7, 5651, 114827] ⟨109013079337, 10, [(2, 3), (3, 1), (7, 1), (5651, 1), (114827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5651
    · exact prime_114827
  · decide +kernel

theorem prime_109013079407 : Nat.Prime 109013079407 := by
  apply nodeValid_prime [2, 7, 11, 707877139] ⟨109013079407, 5, [(2, 1), (7, 1), (11, 1), (707877139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_707877139
  · decide +kernel

theorem prime_109013086471 : Nat.Prime 109013086471 := by
  apply nodeValid_prime [2, 3, 5, 151, 24064699] ⟨109013086471, 6, [(2, 1), (3, 1), (5, 1), (151, 1), (24064699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_24064699
  · decide +kernel

theorem prime_109303348513 : Nat.Prime 109303348513 := by
  apply nodeValid_prime [2, 3, 17, 73, 397, 2311] ⟨109303348513, 5, [(2, 5), (3, 1), (17, 1), (73, 1), (397, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_73
    · exact prime_397
    · exact prime_2311
  · decide +kernel

theorem prime_109303349003 : Nat.Prime 109303349003 := by
  apply nodeValid_prime [2, 54651674501] ⟨109303349003, 2, [(2, 1), (54651674501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54651674501
  · decide +kernel

theorem prime_109303366993 : Nat.Prime 109303366993 := by
  apply nodeValid_prime [2, 3, 23, 8243, 12011] ⟨109303366993, 10, [(2, 4), (3, 1), (23, 1), (8243, 1), (12011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_8243
    · exact prime_12011
  · decide +kernel

theorem prime_109594167391 : Nat.Prime 109594167391 := by
  apply nodeValid_prime [2, 3, 5, 1223, 995677] ⟨109594167391, 6, [(2, 1), (3, 2), (5, 1), (1223, 1), (995677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1223
    · exact prime_995677
  · decide +kernel

theorem prime_109594179523 : Nat.Prime 109594179523 := by
  apply nodeValid_prime [2, 3, 225502427] ⟨109594179523, 2, [(2, 1), (3, 5), (225502427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_225502427
  · decide +kernel

theorem prime_109594180141 : Nat.Prime 109594180141 := by
  apply nodeValid_prime [2, 3, 5, 29, 62985161] ⟨109594180141, 6, [(2, 2), (3, 1), (5, 1), (29, 1), (62985161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_62985161
  · decide +kernel

theorem prime_109885491011 : Nat.Prime 109885491011 := by
  apply nodeValid_prime [2, 5, 10988549101] ⟨109885491011, 2, [(2, 1), (5, 1), (10988549101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10988549101
  · decide +kernel

theorem prime_109885491857 : Nat.Prime 109885491857 := by
  apply nodeValid_prime [2, 7, 67, 14643589] ⟨109885491857, 5, [(2, 4), (7, 1), (67, 1), (14643589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_14643589
  · decide +kernel

theorem prime_109885493867 : Nat.Prime 109885493867 := by
  apply nodeValid_prime [2, 67, 820040999] ⟨109885493867, 2, [(2, 1), (67, 1), (820040999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_820040999
  · decide +kernel

theorem prime_110177347409 : Nat.Prime 110177347409 := by
  apply nodeValid_prime [2, 157, 43860409] ⟨110177347409, 3, [(2, 4), (157, 1), (43860409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_43860409
  · decide +kernel

theorem prime_110177347493 : Nat.Prime 110177347493 := by
  apply nodeValid_prime [2, 15671, 1757663] ⟨110177347493, 2, [(2, 2), (15671, 1), (1757663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15671
    · exact prime_1757663
  · decide +kernel

theorem prime_110177349391 : Nat.Prime 110177349391 := by
  apply nodeValid_prime [2, 3, 5, 15113491] ⟨110177349391, 3, [(2, 1), (3, 6), (5, 1), (15113491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15113491
  · decide +kernel

theorem prime_110469729829 : Nat.Prime 110469729829 := by
  apply nodeValid_prime [2, 3, 467, 3181, 6197] ⟨110469729829, 6, [(2, 2), (3, 1), (467, 1), (3181, 1), (6197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_3181
    · exact prime_6197
  · decide +kernel

theorem prime_110469760649 : Nat.Prime 110469760649 := by
  apply nodeValid_prime [2, 13, 211, 2207, 2281] ⟨110469760649, 3, [(2, 3), (13, 1), (211, 1), (2207, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_211
    · exact prime_2207
    · exact prime_2281
  · decide +kernel

theorem prime_110469761249 : Nat.Prime 110469761249 := by
  apply nodeValid_prime [2, 7, 11, 29, 1545983] ⟨110469761249, 6, [(2, 5), (7, 1), (11, 1), (29, 1), (1545983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_1545983
  · decide +kernel

theorem prime_110762634053 : Nat.Prime 110762634053 := by
  apply nodeValid_prime [2, 7, 3955808359] ⟨110762634053, 2, [(2, 2), (7, 1), (3955808359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3955808359
  · decide +kernel

theorem prime_110762644591 : Nat.Prime 110762644591 := by
  apply nodeValid_prime [2, 3, 5, 13, 31556309] ⟨110762644591, 3, [(2, 1), (3, 3), (5, 1), (13, 1), (31556309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_31556309
  · decide +kernel

theorem prime_110762644711 : Nat.Prime 110762644711 := by
  apply nodeValid_prime [2, 3, 5, 3692088157] ⟨110762644711, 6, [(2, 1), (3, 1), (5, 1), (3692088157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3692088157
  · decide +kernel

theorem prime_111056063089 : Nat.Prime 111056063089 := by
  apply nodeValid_prime [2, 3, 19, 31, 193, 20353] ⟨111056063089, 7, [(2, 4), (3, 1), (19, 1), (31, 1), (193, 1), (20353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_193
    · exact prime_20353
  · decide +kernel

theorem prime_111056091943 : Nat.Prime 111056091943 := by
  apply nodeValid_prime [2, 3, 2843, 6510499] ⟨111056091943, 3, [(2, 1), (3, 1), (2843, 1), (6510499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2843
    · exact prime_6510499
  · decide +kernel

theorem prime_111056092597 : Nat.Prime 111056092597 := by
  apply nodeValid_prime [2, 3, 79, 83, 470473] ⟨111056092597, 11, [(2, 2), (3, 2), (79, 1), (83, 1), (470473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_83
    · exact prime_470473
  · decide +kernel

theorem prime_111350015743 : Nat.Prime 111350015743 := by
  apply nodeValid_prime [2, 3, 7, 17, 103, 1514101] ⟨111350015743, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (103, 1), (1514101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_103
    · exact prime_1514101
  · decide +kernel

theorem prime_111350017619 : Nat.Prime 111350017619 := by
  apply nodeValid_prime [2, 7, 113, 70385599] ⟨111350017619, 2, [(2, 1), (7, 1), (113, 1), (70385599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_70385599
  · decide +kernel

theorem prime_111350018903 : Nat.Prime 111350018903 := by
  apply nodeValid_prime [2, 55675009451] ⟨111350018903, 5, [(2, 1), (55675009451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_55675009451
  · decide +kernel

theorem prime_111644504417 : Nat.Prime 111644504417 := by
  apply nodeValid_prime [2, 3488890763] ⟨111644504417, 3, [(2, 5), (3488890763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3488890763
  · decide +kernel

theorem prime_111644516077 : Nat.Prime 111644516077 := by
  apply nodeValid_prime [2, 3, 9303709673] ⟨111644516077, 2, [(2, 2), (3, 1), (9303709673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9303709673
  · decide +kernel

theorem prime_111644516383 : Nat.Prime 111644516383 := by
  apply nodeValid_prime [2, 3, 7, 19, 4019, 4973] ⟨111644516383, 5, [(2, 1), (3, 1), (7, 2), (19, 1), (4019, 1), (4973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_4019
    · exact prime_4973
  · decide +kernel

theorem prime_111939516763 : Nat.Prime 111939516763 := by
  apply nodeValid_prime [2, 3, 47, 53, 773, 9689] ⟨111939516763, 2, [(2, 1), (3, 1), (47, 1), (53, 1), (773, 1), (9689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_53
    · exact prime_773
    · exact prime_9689
  · decide +kernel

theorem prime_111939516817 : Nat.Prime 111939516817 := by
  apply nodeValid_prime [2, 3, 47807, 48781] ⟨111939516817, 5, [(2, 4), (3, 1), (47807, 1), (48781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47807
    · exact prime_48781
  · decide +kernel

theorem prime_111939520481 : Nat.Prime 111939520481 := by
  apply nodeValid_prime [2, 5, 21341, 32783] ⟨111939520481, 3, [(2, 5), (5, 1), (21341, 1), (32783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_21341
    · exact prime_32783
  · decide +kernel

theorem prime_112235059523 : Nat.Prime 112235059523 := by
  apply nodeValid_prime [2, 56117529761] ⟨112235059523, 2, [(2, 1), (56117529761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56117529761
  · decide +kernel

theorem prime_112235060711 : Nat.Prime 112235060711 := by
  apply nodeValid_prime [2, 5, 12113, 926567] ⟨112235060711, 11, [(2, 1), (5, 1), (12113, 1), (926567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12113
    · exact prime_926567
  · decide +kernel

theorem prime_112235061247 : Nat.Prime 112235061247 := by
  apply nodeValid_prime [2, 3, 7, 11, 4957817] ⟨112235061247, 3, [(2, 1), (3, 1), (7, 3), (11, 1), (4957817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_4957817
  · decide +kernel

theorem prime_112531123429 : Nat.Prime 112531123429 := by
  apply nodeValid_prime [2, 3, 151, 313, 198413] ⟨112531123429, 2, [(2, 2), (3, 1), (151, 1), (313, 1), (198413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_313
    · exact prime_198413
  · decide +kernel

theorem prime_112531136681 : Nat.Prime 112531136681 := by
  apply nodeValid_prime [2, 5, 2813278417] ⟨112531136681, 3, [(2, 3), (5, 1), (2813278417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2813278417
  · decide +kernel

theorem prime_112531136891 : Nat.Prime 112531136891 := by
  apply nodeValid_prime [2, 5, 71, 83, 1909573] ⟨112531136891, 6, [(2, 1), (5, 1), (71, 1), (83, 1), (1909573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_83
    · exact prime_1909573
  · decide +kernel

theorem prime_112827715313 : Nat.Prime 112827715313 := by
  apply nodeValid_prime [2, 13, 79, 83, 82727] ⟨112827715313, 3, [(2, 4), (13, 1), (79, 1), (83, 1), (82727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_83
    · exact prime_82727
  · decide +kernel

theorem prime_112827719449 : Nat.Prime 112827719449 := by
  apply nodeValid_prime [2, 3, 2207, 78893] ⟨112827719449, 31, [(2, 3), (3, 4), (2207, 1), (78893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2207
    · exact prime_78893
  · decide +kernel

theorem prime_112827719503 : Nat.Prime 112827719503 := by
  apply nodeValid_prime [2, 3, 97, 21540229] ⟨112827719503, 3, [(2, 1), (3, 3), (97, 1), (21540229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_21540229
  · decide +kernel

theorem prime_113124827441 : Nat.Prime 113124827441 := by
  apply nodeValid_prime [2, 5, 1414060343] ⟨113124827441, 3, [(2, 4), (5, 1), (1414060343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1414060343
  · decide +kernel

theorem prime_113124829043 : Nat.Prime 113124829043 := by
  apply nodeValid_prime [2, 56562414521] ⟨113124829043, 2, [(2, 1), (56562414521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56562414521
  · decide +kernel

theorem prime_113124838427 : Nat.Prime 113124838427 := by
  apply nodeValid_prime [2, 56562419213] ⟨113124838427, 2, [(2, 1), (56562419213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56562419213
  · decide +kernel

theorem prime_113422496507 : Nat.Prime 113422496507 := by
  apply nodeValid_prime [2, 11, 199, 25907377] ⟨113422496507, 2, [(2, 1), (11, 1), (199, 1), (25907377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_199
    · exact prime_25907377
  · decide +kernel

theorem prime_113422502489 : Nat.Prime 113422502489 := by
  apply nodeValid_prime [2, 43, 409, 806153] ⟨113422502489, 3, [(2, 3), (43, 1), (409, 1), (806153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_409
    · exact prime_806153
  · decide +kernel

theorem prime_113422502569 : Nat.Prime 113422502569 := by
  apply nodeValid_prime [2, 3, 61, 197, 393271] ⟨113422502569, 7, [(2, 3), (3, 1), (61, 1), (197, 1), (393271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_197
    · exact prime_393271
  · decide +kernel

theorem prime_113720684057 : Nat.Prime 113720684057 := by
  apply nodeValid_prime [2, 7, 2657, 764293] ⟨113720684057, 3, [(2, 3), (7, 1), (2657, 1), (764293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2657
    · exact prime_764293
  · decide +kernel

theorem prime_113720686637 : Nat.Prime 113720686637 := by
  apply nodeValid_prime [2, 89, 319440131] ⟨113720686637, 2, [(2, 2), (89, 1), (319440131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_319440131
  · decide +kernel

theorem prime_113720687279 : Nat.Prime 113720687279 := by
  apply nodeValid_prime [2, 11, 43, 120212143] ⟨113720687279, 11, [(2, 1), (11, 1), (43, 1), (120212143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_120212143
  · decide +kernel

theorem prime_114019399883 : Nat.Prime 114019399883 := by
  apply nodeValid_prime [2, 57009699941] ⟨114019399883, 2, [(2, 1), (57009699941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57009699941
  · decide +kernel

theorem prime_114019410409 : Nat.Prime 114019410409 := by
  apply nodeValid_prime [2, 3, 4750808767] ⟨114019410409, 13, [(2, 3), (3, 1), (4750808767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4750808767
  · decide +kernel

theorem prime_114019411223 : Nat.Prime 114019411223 := by
  apply nodeValid_prime [2, 233347, 244313] ⟨114019411223, 5, [(2, 1), (233347, 1), (244313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233347
    · exact prime_244313
  · decide +kernel

theorem prime_114318650401 : Nat.Prime 114318650401 := by
  apply nodeValid_prime [2, 3, 5, 31, 823, 1867] ⟨114318650401, 11, [(2, 5), (3, 1), (5, 2), (31, 1), (823, 1), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_823
    · exact prime_1867
  · decide +kernel

theorem prime_114318659369 : Nat.Prime 114318659369 := by
  apply nodeValid_prime [2, 4127, 3462523] ⟨114318659369, 3, [(2, 3), (4127, 1), (3462523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4127
    · exact prime_3462523
  · decide +kernel

theorem prime_114318659737 : Nat.Prime 114318659737 := by
  apply nodeValid_prime [2, 3, 15661, 101383] ⟨114318659737, 10, [(2, 3), (3, 2), (15661, 1), (101383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15661
    · exact prime_101383
  · decide +kernel

theorem prime_114618439667 : Nat.Prime 114618439667 := by
  apply nodeValid_prime [2, 373, 153644021] ⟨114618439667, 2, [(2, 1), (373, 1), (153644021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_153644021
  · decide +kernel

theorem prime_114618448757 : Nat.Prime 114618448757 := by
  apply nodeValid_prime [2, 7, 431, 1009, 9413] ⟨114618448757, 2, [(2, 2), (7, 1), (431, 1), (1009, 1), (9413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_431
    · exact prime_1009
    · exact prime_9413
  · decide +kernel

theorem prime_114618448811 : Nat.Prime 114618448811 := by
  apply nodeValid_prime [2, 5, 1319, 8689799] ⟨114618448811, 6, [(2, 1), (5, 1), (1319, 1), (8689799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1319
    · exact prime_8689799
  · decide +kernel

theorem prime_114918761393 : Nat.Prime 114918761393 := by
  apply nodeValid_prime [2, 487, 14748301] ⟨114918761393, 3, [(2, 4), (487, 1), (14748301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_14748301
  · decide +kernel

theorem prime_114918763171 : Nat.Prime 114918763171 := by
  apply nodeValid_prime [2, 3, 5, 281, 383, 35593] ⟨114918763171, 2, [(2, 1), (3, 1), (5, 1), (281, 1), (383, 1), (35593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_281
    · exact prime_383
    · exact prime_35593
  · decide +kernel

theorem prime_114918764281 : Nat.Prime 114918764281 := by
  apply nodeValid_prime [2, 3, 5, 957656369] ⟨114918764281, 7, [(2, 3), (3, 1), (5, 1), (957656369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_957656369
  · decide +kernel

theorem prime_115219617959 : Nat.Prime 115219617959 := by
  apply nodeValid_prime [2, 57609808979] ⟨115219617959, 17, [(2, 1), (57609808979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57609808979
  · decide +kernel

theorem prime_115219618771 : Nat.Prime 115219618771 := by
  apply nodeValid_prime [2, 3, 5, 3840653959] ⟨115219618771, 10, [(2, 1), (3, 1), (5, 1), (3840653959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3840653959
  · decide +kernel

theorem prime_115219621709 : Nat.Prime 115219621709 := by
  apply nodeValid_prime [2, 28804905427] ⟨115219621709, 2, [(2, 2), (28804905427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28804905427
  · decide +kernel

theorem prime_115521017333 : Nat.Prime 115521017333 := by
  apply nodeValid_prime [2, 7, 107, 38558417] ⟨115521017333, 2, [(2, 2), (7, 1), (107, 1), (38558417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
    · exact prime_38558417
  · decide +kernel

theorem prime_115521024427 : Nat.Prime 115521024427 := by
  apply nodeValid_prime [2, 3, 17, 1132559063] ⟨115521024427, 3, [(2, 1), (3, 1), (17, 1), (1132559063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1132559063
  · decide +kernel

theorem prime_115521024763 : Nat.Prime 115521024763 := by
  apply nodeValid_prime [2, 3, 11, 13, 617, 72739] ⟨115521024763, 2, [(2, 1), (3, 2), (11, 1), (13, 1), (617, 1), (72739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_617
    · exact prime_72739
  · decide +kernel

theorem prime_115822938251 : Nat.Prime 115822938251 := by
  apply nodeValid_prime [2, 5, 463291753] ⟨115822938251, 2, [(2, 1), (5, 3), (463291753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_463291753
  · decide +kernel

theorem prime_115822938421 : Nat.Prime 115822938421 := by
  apply nodeValid_prime [2, 3, 5, 7, 31, 329473] ⟨115822938421, 6, [(2, 2), (3, 4), (5, 1), (7, 1), (31, 1), (329473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_329473
  · decide +kernel

theorem prime_115822943477 : Nat.Prime 115822943477 := by
  apply nodeValid_prime [2, 11261, 2571329] ⟨115822943477, 2, [(2, 2), (11261, 1), (2571329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11261
    · exact prime_2571329
  · decide +kernel

theorem prime_116125405951 : Nat.Prime 116125405951 := by
  apply nodeValid_prime [2, 3, 5, 23917, 32369] ⟨116125405951, 7, [(2, 1), (3, 1), (5, 2), (23917, 1), (32369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23917
    · exact prime_32369
  · decide +kernel

theorem prime_116125443349 : Nat.Prime 116125443349 := by
  apply nodeValid_prime [2, 3, 2137, 4528367] ⟨116125443349, 2, [(2, 2), (3, 1), (2137, 1), (4528367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2137
    · exact prime_4528367
  · decide +kernel

theorem prime_116125443619 : Nat.Prime 116125443619 := by
  apply nodeValid_prime [2, 3, 29, 53, 307, 41017] ⟨116125443619, 2, [(2, 1), (3, 1), (29, 1), (53, 1), (307, 1), (41017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_53
    · exact prime_307
    · exact prime_41017
  · decide +kernel

end Sude.Lucas.Generated
