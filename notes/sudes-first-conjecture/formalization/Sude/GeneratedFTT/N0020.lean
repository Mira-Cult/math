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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2677 : Nat.Prime 2677 := by
  apply nodeValid_prime [2, 3, 223] ⟨2677, 2, [(2, 2), (3, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
  · decide +kernel

theorem prime_3119 : Nat.Prime 3119 := by
  apply nodeValid_prime [2, 1559] ⟨3119, 7, [(2, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1559
  · decide +kernel

theorem prime_5581 : Nat.Prime 5581 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨5581, 6, [(2, 2), (3, 2), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_7673 : Nat.Prime 7673 := by
  apply nodeValid_prime [2, 7, 137] ⟨7673, 3, [(2, 3), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_7829 : Nat.Prime 7829 := by
  apply nodeValid_prime [2, 19, 103] ⟨7829, 2, [(2, 2), (19, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_103
  · decide +kernel

theorem prime_8093 : Nat.Prime 8093 := by
  apply nodeValid_prime [2, 7, 17] ⟨8093, 2, [(2, 2), (7, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_8837 : Nat.Prime 8837 := by
  apply nodeValid_prime [2, 47] ⟨8837, 2, [(2, 2), (47, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_47
  · decide +kernel

theorem prime_9221 : Nat.Prime 9221 := by
  apply nodeValid_prime [2, 5, 461] ⟨9221, 2, [(2, 2), (5, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_461
  · decide +kernel

theorem prime_9283 : Nat.Prime 9283 := by
  apply nodeValid_prime [2, 3, 7, 13, 17] ⟨9283, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_9941 : Nat.Prime 9941 := by
  apply nodeValid_prime [2, 5, 7, 71] ⟨9941, 2, [(2, 2), (5, 1), (7, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_10687 : Nat.Prime 10687 := by
  apply nodeValid_prime [2, 3, 13, 137] ⟨10687, 5, [(2, 1), (3, 1), (13, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_137
  · decide +kernel

theorem prime_11369 : Nat.Prime 11369 := by
  apply nodeValid_prime [2, 7, 29] ⟨11369, 3, [(2, 3), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_12689 : Nat.Prime 12689 := by
  apply nodeValid_prime [2, 13, 61] ⟨12689, 3, [(2, 4), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_14251 : Nat.Prime 14251 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨14251, 3, [(2, 1), (3, 1), (5, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_16187 : Nat.Prime 16187 := by
  apply nodeValid_prime [2, 8093] ⟨16187, 2, [(2, 1), (8093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8093
  · decide +kernel

theorem prime_16333 : Nat.Prime 16333 := by
  apply nodeValid_prime [2, 3, 1361] ⟨16333, 2, [(2, 2), (3, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1361
  · decide +kernel

theorem prime_16729 : Nat.Prime 16729 := by
  apply nodeValid_prime [2, 3, 17, 41] ⟨16729, 13, [(2, 3), (3, 1), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_16879 : Nat.Prime 16879 := by
  apply nodeValid_prime [2, 3, 29, 97] ⟨16879, 3, [(2, 1), (3, 1), (29, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_97
  · decide +kernel

theorem prime_17401 : Nat.Prime 17401 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨17401, 11, [(2, 3), (3, 1), (5, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_18443 : Nat.Prime 18443 := by
  apply nodeValid_prime [2, 9221] ⟨18443, 2, [(2, 1), (9221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9221
  · decide +kernel

theorem prime_19319 : Nat.Prime 19319 := by
  apply nodeValid_prime [2, 13, 743] ⟨19319, 11, [(2, 1), (13, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_743
  · decide +kernel

theorem prime_22739 : Nat.Prime 22739 := by
  apply nodeValid_prime [2, 11369] ⟨22739, 2, [(2, 1), (11369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11369
  · decide +kernel

theorem prime_23833 : Nat.Prime 23833 := by
  apply nodeValid_prime [2, 3, 331] ⟨23833, 5, [(2, 3), (3, 2), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
  · decide +kernel

theorem prime_25189 : Nat.Prime 25189 := by
  apply nodeValid_prime [2, 3, 2099] ⟨25189, 2, [(2, 2), (3, 1), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2099
  · decide +kernel

theorem prime_26083 : Nat.Prime 26083 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨26083, 7, [(2, 1), (3, 4), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_28151 : Nat.Prime 28151 := by
  apply nodeValid_prime [2, 5, 563] ⟨28151, 7, [(2, 1), (5, 2), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_563
  · decide +kernel

theorem prime_28279 : Nat.Prime 28279 := by
  apply nodeValid_prime [2, 3, 1571] ⟨28279, 3, [(2, 1), (3, 2), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1571
  · decide +kernel

theorem prime_31253 : Nat.Prime 31253 := by
  apply nodeValid_prime [2, 13, 601] ⟨31253, 2, [(2, 2), (13, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_601
  · decide +kernel

theorem prime_31771 : Nat.Prime 31771 := by
  apply nodeValid_prime [2, 3, 5, 353] ⟨31771, 10, [(2, 1), (3, 2), (5, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
  · decide +kernel

theorem prime_35149 : Nat.Prime 35149 := by
  apply nodeValid_prime [2, 3, 29, 101] ⟨35149, 2, [(2, 2), (3, 1), (29, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_101
  · decide +kernel

theorem prime_36887 : Nat.Prime 36887 := by
  apply nodeValid_prime [2, 18443] ⟨36887, 5, [(2, 1), (18443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18443
  · decide +kernel

theorem prime_37517 : Nat.Prime 37517 := by
  apply nodeValid_prime [2, 83, 113] ⟨37517, 2, [(2, 2), (83, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_113
  · decide +kernel

theorem prime_38639 : Nat.Prime 38639 := by
  apply nodeValid_prime [2, 19319] ⟨38639, 29, [(2, 1), (19319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19319
  · decide +kernel

theorem prime_40009 : Nat.Prime 40009 := by
  apply nodeValid_prime [2, 3, 1667] ⟨40009, 11, [(2, 3), (3, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1667
  · decide +kernel

theorem prime_52673 : Nat.Prime 52673 := by
  apply nodeValid_prime [2, 823] ⟨52673, 3, [(2, 6), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_823
  · decide +kernel

theorem prime_56311 : Nat.Prime 56311 := by
  apply nodeValid_prime [2, 3, 5, 1877] ⟨56311, 6, [(2, 1), (3, 1), (5, 1), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1877
  · decide +kernel

theorem prime_63299 : Nat.Prime 63299 := by
  apply nodeValid_prime [2, 31649] ⟨63299, 2, [(2, 1), (31649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31649
  · decide +kernel

theorem prime_69821 : Nat.Prime 69821 := by
  apply nodeValid_prime [2, 5, 3491] ⟨69821, 7, [(2, 2), (5, 1), (3491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3491
  · decide +kernel

theorem prime_77279 : Nat.Prime 77279 := by
  apply nodeValid_prime [2, 38639] ⟨77279, 11, [(2, 1), (38639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38639
  · decide +kernel

theorem prime_93113 : Nat.Prime 93113 := by
  apply nodeValid_prime [2, 103, 113] ⟨93113, 3, [(2, 3), (103, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_113
  · decide +kernel

theorem prime_93949 : Nat.Prime 93949 := by
  apply nodeValid_prime [2, 3, 7829] ⟨93949, 2, [(2, 2), (3, 1), (7829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7829
  · decide +kernel

theorem prime_100459 : Nat.Prime 100459 := by
  apply nodeValid_prime [2, 3, 5581] ⟨100459, 2, [(2, 1), (3, 2), (5581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5581
  · decide +kernel

theorem prime_108917 : Nat.Prime 108917 := by
  apply nodeValid_prime [2, 73, 373] ⟨108917, 2, [(2, 2), (73, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_373
  · decide +kernel

theorem prime_115327 : Nat.Prime 115327 := by
  apply nodeValid_prime [2, 3, 43, 149] ⟨115327, 3, [(2, 1), (3, 2), (43, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_149
  · decide +kernel

theorem prime_122167 : Nat.Prime 122167 := by
  apply nodeValid_prime [2, 3, 11, 617] ⟨122167, 3, [(2, 1), (3, 2), (11, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_617
  · decide +kernel

theorem prime_122477 : Nat.Prime 122477 := by
  apply nodeValid_prime [2, 67, 457] ⟨122477, 2, [(2, 2), (67, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_457
  · decide +kernel

theorem prime_132911 : Nat.Prime 132911 := by
  apply nodeValid_prime [2, 5, 13291] ⟨132911, 7, [(2, 1), (5, 1), (13291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13291
  · decide +kernel

theorem prime_140891 : Nat.Prime 140891 := by
  apply nodeValid_prime [2, 5, 73, 193] ⟨140891, 2, [(2, 1), (5, 1), (73, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_193
  · decide +kernel

theorem prime_155783 : Nat.Prime 155783 := by
  apply nodeValid_prime [2, 11, 73, 97] ⟨155783, 5, [(2, 1), (11, 1), (73, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_97
  · decide +kernel

theorem prime_170057 : Nat.Prime 170057 := by
  apply nodeValid_prime [2, 29, 733] ⟨170057, 3, [(2, 3), (29, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_733
  · decide +kernel

theorem prime_178939 : Nat.Prime 178939 := by
  apply nodeValid_prime [2, 3, 9941] ⟨178939, 2, [(2, 1), (3, 2), (9941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9941
  · decide +kernel

theorem prime_181397 : Nat.Prime 181397 := by
  apply nodeValid_prime [2, 101, 449] ⟨181397, 2, [(2, 2), (101, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_449
  · decide +kernel

theorem prime_186227 : Nat.Prime 186227 := by
  apply nodeValid_prime [2, 93113] ⟨186227, 2, [(2, 1), (93113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93113
  · decide +kernel

theorem prime_187711 : Nat.Prime 187711 := by
  apply nodeValid_prime [2, 3, 5, 6257] ⟨187711, 21, [(2, 1), (3, 1), (5, 1), (6257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6257
  · decide +kernel

theorem prime_247711 : Nat.Prime 247711 := by
  apply nodeValid_prime [2, 3, 5, 23, 359] ⟨247711, 6, [(2, 1), (3, 1), (5, 1), (23, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_359
  · decide +kernel

theorem prime_285997 : Nat.Prime 285997 := by
  apply nodeValid_prime [2, 3, 23833] ⟨285997, 5, [(2, 2), (3, 1), (23833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23833
  · decide +kernel

theorem prime_286483 : Nat.Prime 286483 := by
  apply nodeValid_prime [2, 3, 7, 19, 359] ⟨286483, 5, [(2, 1), (3, 1), (7, 1), (19, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_359
  · decide +kernel

theorem prime_292837 : Nat.Prime 292837 := by
  apply nodeValid_prime [2, 3, 23, 1061] ⟨292837, 7, [(2, 2), (3, 1), (23, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1061
  · decide +kernel

theorem prime_301153 : Nat.Prime 301153 := by
  apply nodeValid_prime [2, 3, 3137] ⟨301153, 5, [(2, 5), (3, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3137
  · decide +kernel

theorem prime_327581 : Nat.Prime 327581 := by
  apply nodeValid_prime [2, 5, 11, 1489] ⟨327581, 2, [(2, 2), (5, 1), (11, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1489
  · decide +kernel

theorem prime_337867 : Nat.Prime 337867 := by
  apply nodeValid_prime [2, 3, 56311] ⟨337867, 2, [(2, 1), (3, 1), (56311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56311
  · decide +kernel

theorem prime_342733 : Nat.Prime 342733 := by
  apply nodeValid_prime [2, 3, 13] ⟨342733, 2, [(2, 2), (3, 1), (13, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_353341 : Nat.Prime 353341 := by
  apply nodeValid_prime [2, 3, 5, 13, 151] ⟨353341, 2, [(2, 2), (3, 2), (5, 1), (13, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_151
  · decide +kernel

theorem prime_374461 : Nat.Prime 374461 := by
  apply nodeValid_prime [2, 3, 5, 79] ⟨374461, 2, [(2, 2), (3, 1), (5, 1), (79, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_417751 : Nat.Prime 417751 := by
  apply nodeValid_prime [2, 3, 5, 557] ⟨417751, 3, [(2, 1), (3, 1), (5, 3), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_557
  · decide +kernel

theorem prime_436651 : Nat.Prime 436651 := by
  apply nodeValid_prime [2, 3, 5, 41, 71] ⟨436651, 3, [(2, 1), (3, 1), (5, 2), (41, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_71
  · decide +kernel

theorem prime_461309 : Nat.Prime 461309 := by
  apply nodeValid_prime [2, 115327] ⟨461309, 2, [(2, 2), (115327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115327
  · decide +kernel

theorem prime_580717 : Nat.Prime 580717 := by
  apply nodeValid_prime [2, 3, 19, 283] ⟨580717, 2, [(2, 2), (3, 3), (19, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_283
  · decide +kernel

theorem prime_679183 : Nat.Prime 679183 := by
  apply nodeValid_prime [2, 3, 7, 103, 157] ⟨679183, 3, [(2, 1), (3, 1), (7, 1), (103, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_157
  · decide +kernel

theorem prime_737423 : Nat.Prime 737423 := by
  apply nodeValid_prime [2, 7, 52673] ⟨737423, 5, [(2, 1), (7, 1), (52673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_52673
  · decide +kernel

theorem prime_845347 : Nat.Prime 845347 := by
  apply nodeValid_prime [2, 3, 140891] ⟨845347, 3, [(2, 1), (3, 1), (140891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_140891
  · decide +kernel

theorem prime_1009259 : Nat.Prime 1009259 := by
  apply nodeValid_prime [2, 29, 17401] ⟨1009259, 2, [(2, 1), (29, 1), (17401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_17401
  · decide +kernel

theorem prime_1317247 : Nat.Prime 1317247 := by
  apply nodeValid_prime [2, 3, 7, 79, 397] ⟨1317247, 3, [(2, 1), (3, 1), (7, 1), (79, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_397
  · decide +kernel

theorem prime_1347757 : Nat.Prime 1347757 := by
  apply nodeValid_prime [2, 3, 31, 3623] ⟨1347757, 5, [(2, 2), (3, 1), (31, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3623
  · decide +kernel

theorem prime_1376191 : Nat.Prime 1376191 := by
  apply nodeValid_prime [2, 3, 5, 1699] ⟨1376191, 3, [(2, 1), (3, 4), (5, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1699
  · decide +kernel

theorem prime_2274977 : Nat.Prime 2274977 := by
  apply nodeValid_prime [2, 11, 23, 281] ⟨2274977, 3, [(2, 5), (11, 1), (23, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_281
  · decide +kernel

theorem prime_2322869 : Nat.Prime 2322869 := by
  apply nodeValid_prime [2, 580717] ⟨2322869, 2, [(2, 2), (580717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_580717
  · decide +kernel

theorem prime_2658559 : Nat.Prime 2658559 := by
  apply nodeValid_prime [2, 3, 7, 63299] ⟨2658559, 13, [(2, 1), (3, 1), (7, 1), (63299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_63299
  · decide +kernel

theorem prime_2812853 : Nat.Prime 2812853 := by
  apply nodeValid_prime [2, 7, 100459] ⟨2812853, 2, [(2, 2), (7, 1), (100459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_100459
  · decide +kernel

theorem prime_2823329 : Nat.Prime 2823329 := by
  apply nodeValid_prime [2, 83, 1063] ⟨2823329, 3, [(2, 5), (83, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_1063
  · decide +kernel

theorem prime_2967407 : Nat.Prime 2967407 := by
  apply nodeValid_prime [2, 13, 61, 1871] ⟨2967407, 5, [(2, 1), (13, 1), (61, 1), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_61
    · exact prime_1871
  · decide +kernel

theorem prime_3189499 : Nat.Prime 3189499 := by
  apply nodeValid_prime [2, 3, 13, 103, 397] ⟨3189499, 10, [(2, 1), (3, 1), (13, 1), (103, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
    · exact prime_397
  · decide +kernel

theorem prime_3361037 : Nat.Prime 3361037 := by
  apply nodeValid_prime [2, 7, 17, 23, 307] ⟨3361037, 2, [(2, 2), (7, 1), (17, 1), (23, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_307
  · decide +kernel

theorem prime_3378671 : Nat.Prime 3378671 := by
  apply nodeValid_prime [2, 5, 337867] ⟨3378671, 7, [(2, 1), (5, 1), (337867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_337867
  · decide +kernel

theorem prime_3628897 : Nat.Prime 3628897 := by
  apply nodeValid_prime [2, 3, 103, 367] ⟨3628897, 11, [(2, 5), (3, 1), (103, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_367
  · decide +kernel

theorem prime_4110047 : Nat.Prime 4110047 := by
  apply nodeValid_prime [2, 73, 28151] ⟨4110047, 5, [(2, 1), (73, 1), (28151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_28151
  · decide +kernel

theorem prime_4127489 : Nat.Prime 4127489 := by
  apply nodeValid_prime [2, 23, 701] ⟨4127489, 3, [(2, 8), (23, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_701
  · decide +kernel

theorem prime_4566797 : Nat.Prime 4566797 := by
  apply nodeValid_prime [2, 13, 31, 2833] ⟨4566797, 2, [(2, 2), (13, 1), (31, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_2833
  · decide +kernel

theorem prime_4944523 : Nat.Prime 4944523 := by
  apply nodeValid_prime [2, 3, 11, 19, 3943] ⟨4944523, 14, [(2, 1), (3, 1), (11, 1), (19, 1), (3943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_3943
  · decide +kernel

theorem prime_5108387 : Nat.Prime 5108387 := by
  apply nodeValid_prime [2, 239, 10687] ⟨5108387, 2, [(2, 1), (239, 1), (10687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_10687
  · decide +kernel

theorem prime_5619683 : Nat.Prime 5619683 := by
  apply nodeValid_prime [2, 23, 122167] ⟨5619683, 2, [(2, 1), (23, 1), (122167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_122167
  · decide +kernel

theorem prime_6001351 : Nat.Prime 6001351 := by
  apply nodeValid_prime [2, 3, 5, 40009] ⟨6001351, 6, [(2, 1), (3, 1), (5, 2), (40009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_40009
  · decide +kernel

theorem prime_6757343 : Nat.Prime 6757343 := by
  apply nodeValid_prime [2, 3378671] ⟨6757343, 5, [(2, 1), (3378671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3378671
  · decide +kernel

theorem prime_7161013 : Nat.Prime 7161013 := by
  apply nodeValid_prime [2, 3, 17, 11701] ⟨7161013, 2, [(2, 2), (3, 2), (17, 1), (11701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_11701
  · decide +kernel

theorem prime_7773761 : Nat.Prime 7773761 := by
  apply nodeValid_prime [2, 5, 17, 1429] ⟨7773761, 3, [(2, 6), (5, 1), (17, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1429
  · decide +kernel

theorem prime_9147977 : Nat.Prime 9147977 := by
  apply nodeValid_prime [2, 31, 36887] ⟨9147977, 3, [(2, 3), (31, 1), (36887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_36887
  · decide +kernel

theorem prime_10025269 : Nat.Prime 10025269 := by
  apply nodeValid_prime [2, 3, 11, 53, 1433] ⟨10025269, 6, [(2, 2), (3, 1), (11, 1), (53, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_1433
  · decide +kernel

theorem prime_11239367 : Nat.Prime 11239367 := by
  apply nodeValid_prime [2, 5619683] ⟨11239367, 5, [(2, 1), (5619683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5619683
  · decide +kernel

theorem prime_31160027 : Nat.Prime 31160027 := by
  apply nodeValid_prime [2, 83, 187711] ⟨31160027, 2, [(2, 1), (83, 1), (187711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_187711
  · decide +kernel

theorem prime_37971103 : Nat.Prime 37971103 := by
  apply nodeValid_prime [2, 3, 13, 37, 59, 223] ⟨37971103, 3, [(2, 1), (3, 1), (13, 1), (37, 1), (59, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_59
    · exact prime_223
  · decide +kernel

theorem prime_55995209 : Nat.Prime 55995209 := by
  apply nodeValid_prime [2, 37, 101, 1873] ⟨55995209, 3, [(2, 3), (37, 1), (101, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_101
    · exact prime_1873
  · decide +kernel

theorem prime_60013511 : Nat.Prime 60013511 := by
  apply nodeValid_prime [2, 5, 6001351] ⟨60013511, 19, [(2, 1), (5, 1), (6001351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6001351
  · decide +kernel

theorem prime_60498667 : Nat.Prime 60498667 := by
  apply nodeValid_prime [2, 3, 3361037] ⟨60498667, 2, [(2, 1), (3, 2), (3361037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3361037
  · decide +kernel

theorem prime_63062873 : Nat.Prime 63062873 := by
  apply nodeValid_prime [2, 23, 342733] ⟨63062873, 3, [(2, 3), (23, 1), (342733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_342733
  · decide +kernel

theorem prime_79332703 : Nat.Prime 79332703 := by
  apply nodeValid_prime [2, 3, 71, 186227] ⟨79332703, 3, [(2, 1), (3, 1), (71, 1), (186227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_186227
  · decide +kernel

theorem prime_105125047 : Nat.Prime 105125047 := by
  apply nodeValid_prime [2, 3, 13, 1347757] ⟨105125047, 10, [(2, 1), (3, 1), (13, 1), (1347757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1347757
  · decide +kernel

theorem prime_116819477 : Nat.Prime 116819477 := by
  apply nodeValid_prime [2, 43, 679183] ⟨116819477, 2, [(2, 2), (43, 1), (679183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_679183
  · decide +kernel

theorem prime_120027023 : Nat.Prime 120027023 := by
  apply nodeValid_prime [2, 60013511] ⟨120027023, 5, [(2, 1), (60013511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60013511
  · decide +kernel

theorem prime_193888223 : Nat.Prime 193888223 := by
  apply nodeValid_prime [2, 11, 613, 1307] ⟨193888223, 5, [(2, 1), (11, 2), (613, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_613
    · exact prime_1307
  · decide +kernel

theorem prime_224834083 : Nat.Prime 224834083 := by
  apply nodeValid_prime [2, 3, 11, 109, 31253] ⟨224834083, 5, [(2, 1), (3, 1), (11, 1), (109, 1), (31253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_109
    · exact prime_31253
  · decide +kernel

theorem prime_240054047 : Nat.Prime 240054047 := by
  apply nodeValid_prime [2, 120027023] ⟨240054047, 5, [(2, 1), (120027023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120027023
  · decide +kernel

theorem prime_249280217 : Nat.Prime 249280217 := by
  apply nodeValid_prime [2, 31160027] ⟨249280217, 3, [(2, 3), (31160027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31160027
  · decide +kernel

theorem prime_297697823 : Nat.Prime 297697823 := by
  apply nodeValid_prime [2, 113, 1317247] ⟨297697823, 5, [(2, 1), (113, 1), (1317247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_1317247
  · decide +kernel

theorem prime_447961673 : Nat.Prime 447961673 := by
  apply nodeValid_prime [2, 55995209] ⟨447961673, 3, [(2, 3), (55995209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_55995209
  · decide +kernel

theorem prime_457422067 : Nat.Prime 457422067 := by
  apply nodeValid_prime [2, 3, 433, 6521] ⟨457422067, 2, [(2, 1), (3, 4), (433, 1), (6521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_433
    · exact prime_6521
  · decide +kernel

theorem prime_583792873 : Nat.Prime 583792873 := by
  apply nodeValid_prime [2, 3, 13, 239, 7829] ⟨583792873, 5, [(2, 3), (3, 1), (13, 1), (239, 1), (7829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_239
    · exact prime_7829
  · decide +kernel

theorem prime_590862187 : Nat.Prime 590862187 := by
  apply nodeValid_prime [2, 3, 109, 301153] ⟨590862187, 3, [(2, 1), (3, 2), (109, 1), (301153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_301153
  · decide +kernel

theorem prime_967978673 : Nat.Prime 967978673 := by
  apply nodeValid_prime [2, 60498667] ⟨967978673, 3, [(2, 4), (60498667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60498667
  · decide +kernel

theorem prime_1101652973 : Nat.Prime 1101652973 := by
  apply nodeValid_prime [2, 7, 17, 109, 1249] ⟨1101652973, 5, [(2, 2), (7, 1), (17, 2), (109, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_109
    · exact prime_1249
  · decide +kernel

theorem prime_1102980427 : Nat.Prime 1102980427 := by
  apply nodeValid_prime [2, 3, 421, 436651] ⟨1102980427, 2, [(2, 1), (3, 1), (421, 1), (436651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
    · exact prime_436651
  · decide +kernel

theorem prime_1624467067 : Nat.Prime 1624467067 := by
  apply nodeValid_prime [2, 3, 53, 5108387] ⟨1624467067, 2, [(2, 1), (3, 1), (53, 1), (5108387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_5108387
  · decide +kernel

theorem prime_1684015513 : Nat.Prime 1684015513 := by
  apply nodeValid_prime [2, 3, 17, 4127489] ⟨1684015513, 5, [(2, 3), (3, 1), (17, 1), (4127489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4127489
  · decide +kernel

theorem prime_2389790933 : Nat.Prime 2389790933 := by
  apply nodeValid_prime [2, 2089, 285997] ⟨2389790933, 2, [(2, 2), (2089, 1), (285997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2089
    · exact prime_285997
  · decide +kernel

theorem prime_2684468513 : Nat.Prime 2684468513 := by
  apply nodeValid_prime [2, 11, 863, 8837] ⟨2684468513, 3, [(2, 5), (11, 1), (863, 1), (8837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_863
    · exact prime_8837
  · decide +kernel

theorem prime_3430665317 : Nat.Prime 3430665317 := by
  apply nodeValid_prime [2, 13, 29, 2274977] ⟨3430665317, 2, [(2, 2), (13, 1), (29, 1), (2274977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_2274977
  · decide +kernel

theorem prime_3783772381 : Nat.Prime 3783772381 := by
  apply nodeValid_prime [2, 3, 5, 63062873] ⟨3783772381, 2, [(2, 2), (3, 1), (5, 1), (63062873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_63062873
  · decide +kernel

theorem prime_4779581867 : Nat.Prime 4779581867 := by
  apply nodeValid_prime [2, 2389790933] ⟨4779581867, 2, [(2, 1), (2389790933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2389790933
  · decide +kernel

theorem prime_5382706363 : Nat.Prime 5382706363 := by
  apply nodeValid_prime [2, 3, 11, 17, 151, 31771] ⟨5382706363, 2, [(2, 1), (3, 1), (11, 1), (17, 1), (151, 1), (31771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_151
    · exact prime_31771
  · decide +kernel

theorem prime_5545503679 : Nat.Prime 5545503679 := by
  apply nodeValid_prime [2, 3, 11, 13, 1613, 4007] ⟨5545503679, 7, [(2, 1), (3, 1), (11, 1), (13, 1), (1613, 1), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1613
    · exact prime_4007
  · decide +kernel

theorem prime_5723495233 : Nat.Prime 5723495233 := by
  apply nodeValid_prime [2, 3, 7, 13, 327581] ⟨5723495233, 23, [(2, 6), (3, 1), (7, 1), (13, 1), (327581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_327581
  · decide +kernel

theorem prime_23038214743 : Nat.Prime 23038214743 := by
  apply nodeValid_prime [2, 3, 19, 29, 2322869] ⟨23038214743, 3, [(2, 1), (3, 2), (19, 1), (29, 1), (2322869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_2322869
  · decide +kernel

theorem prime_23134712737 : Nat.Prime 23134712737 := by
  apply nodeValid_prime [2, 3, 31, 7773761] ⟨23134712737, 10, [(2, 5), (3, 1), (31, 1), (7773761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_7773761
  · decide +kernel

theorem prime_37205323777 : Nat.Prime 37205323777 := by
  apply nodeValid_prime [2, 3, 1009259] ⟨37205323777, 7, [(2, 12), (3, 2), (1009259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1009259
  · decide +kernel

theorem prime_37441624841 : Nat.Prime 37441624841 := by
  apply nodeValid_prime [2, 5, 17, 2111, 26083] ⟨37441624841, 3, [(2, 3), (5, 1), (17, 1), (2111, 1), (26083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2111
    · exact prime_26083
  · decide +kernel

theorem prime_37837723811 : Nat.Prime 37837723811 := by
  apply nodeValid_prime [2, 5, 3783772381] ⟨37837723811, 2, [(2, 1), (5, 1), (3783772381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3783772381
  · decide +kernel

theorem prime_115432153121 : Nat.Prime 115432153121 := by
  apply nodeValid_prime [2, 5, 19, 37971103] ⟨115432153121, 3, [(2, 5), (5, 1), (19, 1), (37971103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_37971103
  · decide +kernel

theorem prime_221820146297 : Nat.Prime 221820146297 := by
  apply nodeValid_prime [2, 7, 433, 9147977] ⟨221820146297, 3, [(2, 3), (7, 1), (433, 1), (9147977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_433
    · exact prime_9147977
  · decide +kernel

theorem prime_221820147113 : Nat.Prime 221820147113 := by
  apply nodeValid_prime [2, 2467, 11239367] ⟨221820147113, 3, [(2, 3), (2467, 1), (11239367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2467
    · exact prime_11239367
  · decide +kernel

theorem prime_221820147161 : Nat.Prime 221820147161 := by
  apply nodeValid_prime [2, 5, 5545503679] ⟨221820147161, 3, [(2, 3), (5, 1), (5545503679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5545503679
  · decide +kernel

theorem prime_222290047523 : Nat.Prime 222290047523 := by
  apply nodeValid_prime [2, 463, 240054047] ⟨222290047523, 2, [(2, 1), (463, 1), (240054047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_463
    · exact prime_240054047
  · decide +kernel

theorem prime_222290047717 : Nat.Prime 222290047717 := by
  apply nodeValid_prime [2, 3, 11, 1684015513] ⟨222290047717, 2, [(2, 2), (3, 1), (11, 1), (1684015513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1684015513
  · decide +kernel

theorem prime_222290060873 : Nat.Prime 222290060873 := by
  apply nodeValid_prime [2, 11, 19, 1123, 118387] ⟨222290060873, 3, [(2, 3), (11, 1), (19, 1), (1123, 1), (118387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1123
    · exact prime_118387
  · decide +kernel

theorem prime_222760650197 : Nat.Prime 222760650197 := by
  apply nodeValid_prime [2, 7, 1609, 4944523] ⟨222760650197, 2, [(2, 2), (7, 1), (1609, 1), (4944523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1609
    · exact prime_4944523
  · decide +kernel

theorem prime_222760658101 : Nat.Prime 222760658101 := by
  apply nodeValid_prime [2, 3, 5, 263, 2823329] ⟨222760658101, 2, [(2, 2), (3, 1), (5, 2), (263, 1), (2823329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
    · exact prime_2823329
  · decide +kernel

theorem prime_222760658611 : Nat.Prime 222760658611 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 2658559] ⟨222760658611, 2, [(2, 1), (3, 2), (5, 1), (7, 2), (19, 1), (2658559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_2658559
  · decide +kernel

theorem prime_223231915061 : Nat.Prime 223231915061 := by
  apply nodeValid_prime [2, 5, 7, 11, 107, 1151] ⟨223231915061, 2, [(2, 2), (5, 1), (7, 1), (11, 2), (107, 2), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_107
    · exact prime_1151
  · decide +kernel

theorem prime_223231942111 : Nat.Prime 223231942111 := by
  apply nodeValid_prime [2, 3, 5, 5407, 1376191] ⟨223231942111, 3, [(2, 1), (3, 1), (5, 1), (5407, 1), (1376191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5407
    · exact prime_1376191
  · decide +kernel

theorem prime_223231942663 : Nat.Prime 223231942663 := by
  apply nodeValid_prime [2, 3, 37205323777] ⟨223231942663, 5, [(2, 1), (3, 1), (37205323777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37205323777
  · decide +kernel

theorem prime_223703852467 : Nat.Prime 223703852467 := by
  apply nodeValid_prime [2, 3, 3719, 10025269] ⟨223703852467, 2, [(2, 1), (3, 1), (3719, 1), (10025269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3719
    · exact prime_10025269
  · decide +kernel

theorem prime_223703861449 : Nat.Prime 223703861449 := by
  apply nodeValid_prime [2, 3, 59, 929, 170057] ⟨223703861449, 14, [(2, 3), (3, 1), (59, 1), (929, 1), (170057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_929
    · exact prime_170057
  · decide +kernel

theorem prime_223703862337 : Nat.Prime 223703862337 := by
  apply nodeValid_prime [2, 3, 239, 521, 3119] ⟨223703862337, 11, [(2, 6), (3, 2), (239, 1), (521, 1), (3119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_521
    · exact prime_3119
  · decide +kernel

theorem prime_224176455247 : Nat.Prime 224176455247 := by
  apply nodeValid_prime [2, 3, 23, 1624467067] ⟨224176455247, 5, [(2, 1), (3, 1), (23, 1), (1624467067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1624467067
  · decide +kernel

theorem prime_224176455611 : Nat.Prime 224176455611 := by
  apply nodeValid_prime [2, 5, 17, 35149, 37517] ⟨224176455611, 2, [(2, 1), (5, 1), (17, 1), (35149, 1), (37517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_35149
    · exact prime_37517
  · decide +kernel

theorem prime_224176463233 : Nat.Prime 224176463233 := by
  apply nodeValid_prime [2, 3, 583792873] ⟨224176463233, 10, [(2, 7), (3, 1), (583792873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_583792873
  · decide +kernel

theorem prime_224649733393 : Nat.Prime 224649733393 := by
  apply nodeValid_prime [2, 3, 7, 37, 71, 28279] ⟨224649733393, 5, [(2, 4), (3, 3), (7, 1), (37, 1), (71, 1), (28279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_71
    · exact prime_28279
  · decide +kernel

theorem prime_224649749047 : Nat.Prime 224649749047 := by
  apply nodeValid_prime [2, 3, 37441624841] ⟨224649749047, 3, [(2, 1), (3, 1), (37441624841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37441624841
  · decide +kernel

theorem prime_225123710659 : Nat.Prime 225123710659 := by
  apply nodeValid_prime [2, 3, 7, 11, 997, 69821] ⟨225123710659, 2, [(2, 1), (3, 1), (7, 2), (11, 1), (997, 1), (69821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_997
    · exact prime_69821
  · decide +kernel

theorem prime_225123714379 : Nat.Prime 225123714379 := by
  apply nodeValid_prime [2, 3, 17, 179, 4110047] ⟨225123714379, 2, [(2, 1), (3, 2), (17, 1), (179, 1), (4110047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_179
    · exact prime_4110047
  · decide +kernel

theorem prime_225123714817 : Nat.Prime 225123714817 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 292837] ⟨225123714817, 10, [(2, 8), (3, 1), (7, 1), (11, 1), (13, 1), (292837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_292837
  · decide +kernel

theorem prime_225598334453 : Nat.Prime 225598334453 := by
  apply nodeValid_prime [2, 223, 1021, 247711] ⟨225598334453, 2, [(2, 2), (223, 1), (1021, 1), (247711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_1021
    · exact prime_247711
  · decide +kernel

theorem prime_225598334953 : Nat.Prime 225598334953 := by
  apply nodeValid_prime [2, 3, 37, 719, 353341] ⟨225598334953, 7, [(2, 3), (3, 1), (37, 1), (719, 1), (353341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_719
    · exact prime_353341
  · decide +kernel

theorem prime_225598350863 : Nat.Prime 225598350863 := by
  apply nodeValid_prime [2, 29, 37, 105125047] ⟨225598350863, 5, [(2, 1), (29, 1), (37, 1), (105125047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_105125047
  · decide +kernel

theorem prime_226073667247 : Nat.Prime 226073667247 := by
  apply nodeValid_prime [2, 3, 7, 5382706363] ⟨226073667247, 5, [(2, 1), (3, 1), (7, 1), (5382706363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5382706363
  · decide +kernel

theorem prime_226073667409 : Nat.Prime 226073667409 := by
  apply nodeValid_prime [2, 3, 17, 41, 6757343] ⟨226073667409, 11, [(2, 4), (3, 1), (17, 1), (41, 1), (6757343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_6757343
  · decide +kernel

theorem prime_226073668019 : Nat.Prime 226073668019 := by
  apply nodeValid_prime [2, 11, 53, 193888223] ⟨226073668019, 6, [(2, 1), (11, 1), (53, 1), (193888223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_193888223
  · decide +kernel

theorem prime_226549653923 : Nat.Prime 226549653923 := by
  apply nodeValid_prime [2, 113, 2677, 374461] ⟨226549653923, 2, [(2, 1), (113, 1), (2677, 1), (374461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_2677
    · exact prime_374461
  · decide +kernel

theorem prime_226549654823 : Nat.Prime 226549654823 := by
  apply nodeValid_prime [2, 59, 647, 2967407] ⟨226549654823, 5, [(2, 1), (59, 1), (647, 1), (2967407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_647
    · exact prime_2967407
  · decide +kernel

theorem prime_226549665577 : Nat.Prime 226549665577 := by
  apply nodeValid_prime [2, 3, 13, 53, 4566797] ⟨226549665577, 5, [(2, 3), (3, 2), (13, 1), (53, 1), (4566797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_4566797
  · decide +kernel

theorem prime_227026304693 : Nat.Prime 227026304693 := by
  apply nodeValid_prime [2, 11, 3011, 155783] ⟨227026304693, 2, [(2, 2), (11, 2), (3011, 1), (155783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3011
    · exact prime_155783
  · decide +kernel

theorem prime_227026306649 : Nat.Prime 227026306649 := by
  apply nodeValid_prime [2, 263, 881, 122477] ⟨227026306649, 3, [(2, 3), (263, 1), (881, 1), (122477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_881
    · exact prime_122477
  · decide +kernel

theorem prime_227026342867 : Nat.Prime 227026342867 := by
  apply nodeValid_prime [2, 3, 37837723811] ⟨227026342867, 2, [(2, 1), (3, 1), (37837723811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37837723811
  · decide +kernel

theorem prime_227503698047 : Nat.Prime 227503698047 := by
  apply nodeValid_prime [2, 1597, 7673, 9283] ⟨227503698047, 5, [(2, 1), (1597, 1), (7673, 1), (9283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1597
    · exact prime_7673
    · exact prime_9283
  · decide +kernel

theorem prime_227503759531 : Nat.Prime 227503759531 := by
  apply nodeValid_prime [2, 3, 5, 17, 967, 461309] ⟨227503759531, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (967, 1), (461309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_967
    · exact prime_461309
  · decide +kernel

theorem prime_227503760357 : Nat.Prime 227503760357 := by
  apply nodeValid_prime [2, 19, 16729, 178939] ⟨227503760357, 2, [(2, 2), (19, 1), (16729, 1), (178939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_16729
    · exact prime_178939
  · decide +kernel

theorem prime_227981735651 : Nat.Prime 227981735651 := by
  apply nodeValid_prime [2, 5, 1621, 2812853] ⟨227981735651, 2, [(2, 1), (5, 2), (1621, 1), (2812853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1621
    · exact prime_2812853
  · decide +kernel

theorem prime_227981759737 : Nat.Prime 227981759737 := by
  apply nodeValid_prime [2, 3, 22739, 417751] ⟨227981759737, 10, [(2, 3), (3, 1), (22739, 1), (417751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22739
    · exact prime_417751
  · decide +kernel

theorem prime_227981760163 : Nat.Prime 227981760163 := by
  apply nodeValid_prime [2, 3, 13, 224834083] ⟨227981760163, 12, [(2, 1), (3, 1), (13, 2), (224834083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_224834083
  · decide +kernel

theorem prime_228460451651 : Nat.Prime 228460451651 := by
  apply nodeValid_prime [2, 5, 25189, 181397] ⟨228460451651, 2, [(2, 1), (5, 2), (25189, 1), (181397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25189
    · exact prime_181397
  · decide +kernel

theorem prime_228460452079 : Nat.Prime 228460452079 := by
  apply nodeValid_prime [2, 3, 132911, 286483] ⟨228460452079, 3, [(2, 1), (3, 1), (132911, 1), (286483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132911
    · exact prime_286483
  · decide +kernel

theorem prime_228460453231 : Nat.Prime 228460453231 := by
  apply nodeValid_prime [2, 3, 5, 17, 447961673] ⟨228460453231, 15, [(2, 1), (3, 1), (5, 1), (17, 1), (447961673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_447961673
  · decide +kernel

theorem prime_228939808549 : Nat.Prime 228939808549 := by
  apply nodeValid_prime [2, 3, 11, 18461, 93949] ⟨228939808549, 2, [(2, 2), (3, 1), (11, 1), (18461, 1), (93949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_18461
    · exact prime_93949
  · decide +kernel

theorem prime_228939809321 : Nat.Prime 228939809321 := by
  apply nodeValid_prime [2, 5, 5723495233] ⟨228939809321, 6, [(2, 3), (5, 1), (5723495233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5723495233
  · decide +kernel

theorem prime_228939853937 : Nat.Prime 228939853937 := by
  apply nodeValid_prime [2, 3943, 3628897] ⟨228939853937, 3, [(2, 4), (3943, 1), (3628897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3943
    · exact prime_3628897
  · decide +kernel

theorem prime_229419928817 : Nat.Prime 229419928817 := by
  apply nodeValid_prime [2, 13, 1102980427] ⟨229419928817, 3, [(2, 4), (13, 1), (1102980427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1102980427
  · decide +kernel

theorem prime_229419929617 : Nat.Prime 229419929617 := by
  apply nodeValid_prime [2, 3, 4779581867] ⟨229419929617, 5, [(2, 4), (3, 1), (4779581867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4779581867
  · decide +kernel

theorem prime_229419936959 : Nat.Prime 229419936959 := by
  apply nodeValid_prime [2, 83, 12689, 108917] ⟨229419936959, 11, [(2, 1), (83, 1), (12689, 1), (108917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_12689
    · exact prime_108917
  · decide +kernel

theorem prime_229900710887 : Nat.Prime 229900710887 := by
  apply nodeValid_prime [2, 7, 11, 23, 53, 127, 9643] ⟨229900710887, 5, [(2, 1), (7, 1), (11, 1), (23, 1), (53, 1), (127, 1), (9643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_53
    · exact prime_127
    · exact prime_9643
  · decide +kernel

theorem prime_229900730737 : Nat.Prime 229900730737 := by
  apply nodeValid_prime [2, 3, 41, 116819477] ⟨229900730737, 5, [(2, 4), (3, 1), (41, 1), (116819477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_116819477
  · decide +kernel

theorem prime_229900731509 : Nat.Prime 229900731509 := by
  apply nodeValid_prime [2, 7, 37, 283, 21193] ⟨229900731509, 2, [(2, 2), (7, 1), (37, 2), (283, 1), (21193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_283
    · exact prime_21193
  · decide +kernel

theorem prime_230382145547 : Nat.Prime 230382145547 := by
  apply nodeValid_prime [2, 7, 73, 2917, 77279] ⟨230382145547, 5, [(2, 1), (7, 1), (73, 1), (2917, 1), (77279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_2917
    · exact prime_77279
  · decide +kernel

theorem prime_230382147431 : Nat.Prime 230382147431 := by
  apply nodeValid_prime [2, 5, 23038214743] ⟨230382147431, 13, [(2, 1), (5, 1), (23038214743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23038214743
  · decide +kernel

theorem prime_230382169513 : Nat.Prime 230382169513 := by
  apply nodeValid_prime [2, 3, 11, 79332703] ⟨230382169513, 7, [(2, 3), (3, 1), (11, 2), (79332703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79332703
  · decide +kernel

theorem prime_230864290367 : Nat.Prime 230864290367 := by
  apply nodeValid_prime [2, 23, 47, 59, 127, 14251] ⟨230864290367, 5, [(2, 1), (23, 1), (47, 1), (59, 1), (127, 1), (14251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_59
    · exact prime_127
    · exact prime_14251
  · decide +kernel

theorem prime_230864292119 : Nat.Prime 230864292119 := by
  apply nodeValid_prime [2, 43, 2684468513] ⟨230864292119, 13, [(2, 1), (43, 1), (2684468513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2684468513
  · decide +kernel

theorem prime_230864306243 : Nat.Prime 230864306243 := by
  apply nodeValid_prime [2, 115432153121] ⟨230864306243, 2, [(2, 1), (115432153121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115432153121
  · decide +kernel

theorem prime_231347120467 : Nat.Prime 231347120467 := by
  apply nodeValid_prime [2, 3, 7, 11, 157, 3189499] ⟨231347120467, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (157, 1), (3189499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_157
    · exact prime_3189499
  · decide +kernel

theorem prime_231347124331 : Nat.Prime 231347124331 := by
  apply nodeValid_prime [2, 3, 5, 7, 1101652973] ⟨231347124331, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (1101652973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1101652973
  · decide +kernel

theorem prime_231347127371 : Nat.Prime 231347127371 := by
  apply nodeValid_prime [2, 5, 23134712737] ⟨231347127371, 6, [(2, 1), (5, 1), (23134712737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23134712737
  · decide +kernel

theorem prime_231830601811 : Nat.Prime 231830601811 := by
  apply nodeValid_prime [2, 3, 5, 31, 249280217] ⟨231830601811, 2, [(2, 1), (3, 1), (5, 1), (31, 1), (249280217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_249280217
  · decide +kernel

theorem prime_231830602001 : Nat.Prime 231830602001 := by
  apply nodeValid_prime [2, 5, 47, 151, 16333] ⟨231830602001, 7, [(2, 4), (5, 3), (47, 1), (151, 1), (16333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_151
    · exact prime_16333
  · decide +kernel

theorem prime_231830634863 : Nat.Prime 231830634863 := by
  apply nodeValid_prime [2, 16187, 7161013] ⟨231830634863, 5, [(2, 1), (16187, 1), (7161013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16187
    · exact prime_7161013
  · decide +kernel

theorem prime_232314825419 : Nat.Prime 232314825419 := by
  apply nodeValid_prime [2, 13, 67, 7901, 16879] ⟨232314825419, 2, [(2, 1), (13, 1), (67, 1), (7901, 1), (16879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_7901
    · exact prime_16879
  · decide +kernel

theorem prime_232314881153 : Nat.Prime 232314881153 := by
  apply nodeValid_prime [2, 19, 113, 845347] ⟨232314881153, 3, [(2, 7), (19, 1), (113, 1), (845347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_113
    · exact prime_845347
  · decide +kernel

theorem prime_232314881521 : Nat.Prime 232314881521 := by
  apply nodeValid_prime [2, 3, 5, 967978673] ⟨232314881521, 11, [(2, 4), (3, 1), (5, 1), (967978673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_967978673
  · decide +kernel

theorem prime_232799697587 : Nat.Prime 232799697587 := by
  apply nodeValid_prime [2, 17, 23, 297697823] ⟨232799697587, 2, [(2, 1), (17, 1), (23, 1), (297697823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_297697823
  · decide +kernel

theorem prime_232799701679 : Nat.Prime 232799701679 := by
  apply nodeValid_prime [2, 197, 590862187] ⟨232799701679, 19, [(2, 1), (197, 1), (590862187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_590862187
  · decide +kernel

theorem prime_232799703767 : Nat.Prime 232799703767 := by
  apply nodeValid_prime [2, 7, 743, 1553, 14411] ⟨232799703767, 5, [(2, 1), (7, 1), (743, 1), (1553, 1), (14411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_743
    · exact prime_1553
    · exact prime_14411
  · decide +kernel

theorem prime_233285240897 : Nat.Prime 233285240897 := by
  apply nodeValid_prime [2, 4943, 737423] ⟨233285240897, 3, [(2, 6), (4943, 1), (737423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4943
    · exact prime_737423
  · decide +kernel

theorem prime_233285241557 : Nat.Prime 233285241557 := by
  apply nodeValid_prime [2, 17, 3430665317] ⟨233285241557, 2, [(2, 2), (17, 1), (3430665317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3430665317
  · decide +kernel

theorem prime_233285254171 : Nat.Prime 233285254171 := by
  apply nodeValid_prime [2, 3, 5, 17, 457422067] ⟨233285254171, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (457422067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_457422067
  · decide +kernel

end Sude.Lucas.Generated
