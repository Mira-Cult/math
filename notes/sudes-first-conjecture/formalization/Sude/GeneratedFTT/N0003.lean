import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_223 : Nat.Prime 223 := by
  apply nodeValid_prime [2, 3, 37] ⟨223, 3, [(2, 1), (3, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_317 : Nat.Prime 317 := by
  apply nodeValid_prime [2, 79] ⟨317, 2, [(2, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_79
  · decide +kernel

theorem prime_401 : Nat.Prime 401 := by
  apply nodeValid_prime [2, 5] ⟨401, 3, [(2, 4), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_541 : Nat.Prime 541 := by
  apply nodeValid_prime [2, 3, 5] ⟨541, 2, [(2, 2), (3, 3), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_691 : Nat.Prime 691 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨691, 3, [(2, 1), (3, 1), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_727 : Nat.Prime 727 := by
  apply nodeValid_prime [2, 3, 11] ⟨727, 5, [(2, 1), (3, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_733 : Nat.Prime 733 := by
  apply nodeValid_prime [2, 3, 61] ⟨733, 6, [(2, 2), (3, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel

theorem prime_761 : Nat.Prime 761 := by
  apply nodeValid_prime [2, 5, 19] ⟨761, 6, [(2, 3), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_809 : Nat.Prime 809 := by
  apply nodeValid_prime [2, 101] ⟨809, 3, [(2, 3), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_101
  · decide +kernel

theorem prime_857 : Nat.Prime 857 := by
  apply nodeValid_prime [2, 107] ⟨857, 3, [(2, 3), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_107
  · decide +kernel

theorem prime_881 : Nat.Prime 881 := by
  apply nodeValid_prime [2, 5, 11] ⟨881, 3, [(2, 4), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_941 : Nat.Prime 941 := by
  apply nodeValid_prime [2, 5, 47] ⟨941, 2, [(2, 2), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_1009 : Nat.Prime 1009 := by
  apply nodeValid_prime [2, 3, 7] ⟨1009, 11, [(2, 4), (3, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_1013 : Nat.Prime 1013 := by
  apply nodeValid_prime [2, 11, 23] ⟨1013, 3, [(2, 2), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_1039 : Nat.Prime 1039 := by
  apply nodeValid_prime [2, 3, 173] ⟨1039, 3, [(2, 1), (3, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
  · decide +kernel

theorem prime_1093 : Nat.Prime 1093 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨1093, 5, [(2, 2), (3, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_1103 : Nat.Prime 1103 := by
  apply nodeValid_prime [2, 19, 29] ⟨1103, 5, [(2, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_1163 : Nat.Prime 1163 := by
  apply nodeValid_prime [2, 7, 83] ⟨1163, 5, [(2, 1), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_1301 : Nat.Prime 1301 := by
  apply nodeValid_prime [2, 5, 13] ⟨1301, 2, [(2, 2), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_1321 : Nat.Prime 1321 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨1321, 13, [(2, 3), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_1423 : Nat.Prime 1423 := by
  apply nodeValid_prime [2, 3, 79] ⟨1423, 3, [(2, 1), (3, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_1459 : Nat.Prime 1459 := by
  apply nodeValid_prime [2, 3] ⟨1459, 3, [(2, 1), (3, 6)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_1487 : Nat.Prime 1487 := by
  apply nodeValid_prime [2, 743] ⟨1487, 5, [(2, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_743
  · decide +kernel

theorem prime_1607 : Nat.Prime 1607 := by
  apply nodeValid_prime [2, 11, 73] ⟨1607, 5, [(2, 1), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_1777 : Nat.Prime 1777 := by
  apply nodeValid_prime [2, 3, 37] ⟨1777, 5, [(2, 4), (3, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_1861 : Nat.Prime 1861 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨1861, 2, [(2, 2), (3, 1), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_2027 : Nat.Prime 2027 := by
  apply nodeValid_prime [2, 1013] ⟨2027, 2, [(2, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1013
  · decide +kernel

theorem prime_2207 : Nat.Prime 2207 := by
  apply nodeValid_prime [2, 1103] ⟨2207, 5, [(2, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1103
  · decide +kernel

theorem prime_2347 : Nat.Prime 2347 := by
  apply nodeValid_prime [2, 3, 17, 23] ⟨2347, 3, [(2, 1), (3, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_2689 : Nat.Prime 2689 := by
  apply nodeValid_prime [2, 3, 7] ⟨2689, 19, [(2, 7), (3, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_2777 : Nat.Prime 2777 := by
  apply nodeValid_prime [2, 347] ⟨2777, 3, [(2, 3), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_347
  · decide +kernel

theorem prime_3061 : Nat.Prime 3061 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨3061, 6, [(2, 2), (3, 2), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_3163 : Nat.Prime 3163 := by
  apply nodeValid_prime [2, 3, 17, 31] ⟨3163, 3, [(2, 1), (3, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_3499 : Nat.Prime 3499 := by
  apply nodeValid_prime [2, 3, 11, 53] ⟨3499, 2, [(2, 1), (3, 1), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_3559 : Nat.Prime 3559 := by
  apply nodeValid_prime [2, 3, 593] ⟨3559, 3, [(2, 1), (3, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_593
  · decide +kernel

theorem prime_3701 : Nat.Prime 3701 := by
  apply nodeValid_prime [2, 5, 37] ⟨3701, 2, [(2, 2), (5, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_4019 : Nat.Prime 4019 := by
  apply nodeValid_prime [2, 7, 41] ⟨4019, 2, [(2, 1), (7, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_4177 : Nat.Prime 4177 := by
  apply nodeValid_prime [2, 3, 29] ⟨4177, 5, [(2, 4), (3, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_4261 : Nat.Prime 4261 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨4261, 2, [(2, 2), (3, 1), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_4357 : Nat.Prime 4357 := by
  apply nodeValid_prime [2, 3, 11] ⟨4357, 2, [(2, 2), (3, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_4397 : Nat.Prime 4397 := by
  apply nodeValid_prime [2, 7, 157] ⟨4397, 2, [(2, 2), (7, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_157
  · decide +kernel

theorem prime_4481 : Nat.Prime 4481 := by
  apply nodeValid_prime [2, 5, 7] ⟨4481, 3, [(2, 7), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_4591 : Nat.Prime 4591 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨4591, 11, [(2, 1), (3, 3), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_4973 : Nat.Prime 4973 := by
  apply nodeValid_prime [2, 11, 113] ⟨4973, 2, [(2, 2), (11, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
  · decide +kernel

theorem prime_5147 : Nat.Prime 5147 := by
  apply nodeValid_prime [2, 31, 83] ⟨5147, 2, [(2, 1), (31, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_83
  · decide +kernel

theorem prime_5209 : Nat.Prime 5209 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨5209, 17, [(2, 3), (3, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_5479 : Nat.Prime 5479 := by
  apply nodeValid_prime [2, 3, 11, 83] ⟨5479, 3, [(2, 1), (3, 1), (11, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
  · decide +kernel

theorem prime_5573 : Nat.Prime 5573 := by
  apply nodeValid_prime [2, 7, 199] ⟨5573, 2, [(2, 2), (7, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_199
  · decide +kernel

theorem prime_5647 : Nat.Prime 5647 := by
  apply nodeValid_prime [2, 3, 941] ⟨5647, 3, [(2, 1), (3, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_941
  · decide +kernel

theorem prime_6907 : Nat.Prime 6907 := by
  apply nodeValid_prime [2, 3, 1151] ⟨6907, 2, [(2, 1), (3, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1151
  · decide +kernel

theorem prime_7193 : Nat.Prime 7193 := by
  apply nodeValid_prime [2, 29, 31] ⟨7193, 3, [(2, 3), (29, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_31
  · decide +kernel

theorem prime_7927 : Nat.Prime 7927 := by
  apply nodeValid_prime [2, 3, 1321] ⟨7927, 3, [(2, 1), (3, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1321
  · decide +kernel

theorem prime_8017 : Nat.Prime 8017 := by
  apply nodeValid_prime [2, 3, 167] ⟨8017, 5, [(2, 4), (3, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
  · decide +kernel

theorem prime_8311 : Nat.Prime 8311 := by
  apply nodeValid_prime [2, 3, 5, 277] ⟨8311, 3, [(2, 1), (3, 1), (5, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_277
  · decide +kernel

theorem prime_8663 : Nat.Prime 8663 := by
  apply nodeValid_prime [2, 61, 71] ⟨8663, 5, [(2, 1), (61, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_71
  · decide +kernel

theorem prime_9311 : Nat.Prime 9311 := by
  apply nodeValid_prime [2, 5, 7, 19] ⟨9311, 7, [(2, 1), (5, 1), (7, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_9643 : Nat.Prime 9643 := by
  apply nodeValid_prime [2, 3, 1607] ⟨9643, 2, [(2, 1), (3, 1), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1607
  · decide +kernel

theorem prime_9721 : Nat.Prime 9721 := by
  apply nodeValid_prime [2, 3, 5] ⟨9721, 7, [(2, 3), (3, 5), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_9791 : Nat.Prime 9791 := by
  apply nodeValid_prime [2, 5, 11, 89] ⟨9791, 11, [(2, 1), (5, 1), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_10139 : Nat.Prime 10139 := by
  apply nodeValid_prime [2, 37, 137] ⟨10139, 2, [(2, 1), (37, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_137
  · decide +kernel

theorem prime_10391 : Nat.Prime 10391 := by
  apply nodeValid_prime [2, 5, 1039] ⟨10391, 19, [(2, 1), (5, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1039
  · decide +kernel

theorem prime_10789 : Nat.Prime 10789 := by
  apply nodeValid_prime [2, 3, 29, 31] ⟨10789, 2, [(2, 2), (3, 1), (29, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
  · decide +kernel

theorem prime_11261 : Nat.Prime 11261 := by
  apply nodeValid_prime [2, 5, 563] ⟨11261, 2, [(2, 2), (5, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_563
  · decide +kernel

theorem prime_14431 : Nat.Prime 14431 := by
  apply nodeValid_prime [2, 3, 5, 13, 37] ⟨14431, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_14479 : Nat.Prime 14479 := by
  apply nodeValid_prime [2, 3, 19, 127] ⟨14479, 3, [(2, 1), (3, 1), (19, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_127
  · decide +kernel

theorem prime_16699 : Nat.Prime 16699 := by
  apply nodeValid_prime [2, 3, 11, 23] ⟨16699, 3, [(2, 1), (3, 1), (11, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_18307 : Nat.Prime 18307 := by
  apply nodeValid_prime [2, 3, 113] ⟨18307, 11, [(2, 1), (3, 4), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
  · decide +kernel

theorem prime_19559 : Nat.Prime 19559 := by
  apply nodeValid_prime [2, 7, 11, 127] ⟨19559, 13, [(2, 1), (7, 1), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_21149 : Nat.Prime 21149 := by
  apply nodeValid_prime [2, 17, 311] ⟨21149, 3, [(2, 2), (17, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_311
  · decide +kernel

theorem prime_21589 : Nat.Prime 21589 := by
  apply nodeValid_prime [2, 3, 7, 257] ⟨21589, 2, [(2, 2), (3, 1), (7, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_257
  · decide +kernel

theorem prime_23561 : Nat.Prime 23561 := by
  apply nodeValid_prime [2, 5, 19, 31] ⟨23561, 3, [(2, 3), (5, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_25969 : Nat.Prime 25969 := by
  apply nodeValid_prime [2, 3, 541] ⟨25969, 7, [(2, 4), (3, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
  · decide +kernel

theorem prime_27337 : Nat.Prime 27337 := by
  apply nodeValid_prime [2, 3, 17, 67] ⟨27337, 5, [(2, 3), (3, 1), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_32069 : Nat.Prime 32069 := by
  apply nodeValid_prime [2, 8017] ⟨32069, 2, [(2, 2), (8017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8017
  · decide +kernel

theorem prime_32797 : Nat.Prime 32797 := by
  apply nodeValid_prime [2, 3, 911] ⟨32797, 2, [(2, 2), (3, 2), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_911
  · decide +kernel

theorem prime_37217 : Nat.Prime 37217 := by
  apply nodeValid_prime [2, 1163] ⟨37217, 3, [(2, 5), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1163
  · decide +kernel

theorem prime_39727 : Nat.Prime 39727 := by
  apply nodeValid_prime [2, 3, 2207] ⟨39727, 3, [(2, 1), (3, 2), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2207
  · decide +kernel

theorem prime_40483 : Nat.Prime 40483 := by
  apply nodeValid_prime [2, 3, 13, 173] ⟨40483, 2, [(2, 1), (3, 2), (13, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_173
  · decide +kernel

theorem prime_41177 : Nat.Prime 41177 := by
  apply nodeValid_prime [2, 5147] ⟨41177, 3, [(2, 3), (5147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5147
  · decide +kernel

theorem prime_42299 : Nat.Prime 42299 := by
  apply nodeValid_prime [2, 21149] ⟨42299, 2, [(2, 1), (21149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21149
  · decide +kernel

theorem prime_42499 : Nat.Prime 42499 := by
  apply nodeValid_prime [2, 3, 787] ⟨42499, 2, [(2, 1), (3, 3), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_787
  · decide +kernel

theorem prime_42793 : Nat.Prime 42793 := by
  apply nodeValid_prime [2, 3, 1783] ⟨42793, 5, [(2, 3), (3, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1783
  · decide +kernel

theorem prime_52501 : Nat.Prime 52501 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨52501, 10, [(2, 2), (3, 1), (5, 4), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_53377 : Nat.Prime 53377 := by
  apply nodeValid_prime [2, 3, 139] ⟨53377, 5, [(2, 7), (3, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_57917 : Nat.Prime 57917 := by
  apply nodeValid_prime [2, 14479] ⟨57917, 2, [(2, 2), (14479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14479
  · decide +kernel

theorem prime_62347 : Nat.Prime 62347 := by
  apply nodeValid_prime [2, 3, 10391] ⟨62347, 3, [(2, 1), (3, 1), (10391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10391
  · decide +kernel

theorem prime_68771 : Nat.Prime 68771 := by
  apply nodeValid_prime [2, 5, 13, 23] ⟨68771, 10, [(2, 1), (5, 1), (13, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_81737 : Nat.Prime 81737 := by
  apply nodeValid_prime [2, 17, 601] ⟨81737, 3, [(2, 3), (17, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_601
  · decide +kernel

theorem prime_112403 : Nat.Prime 112403 := by
  apply nodeValid_prime [2, 43, 1307] ⟨112403, 2, [(2, 1), (43, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1307
  · decide +kernel

theorem prime_158909 : Nat.Prime 158909 := by
  apply nodeValid_prime [2, 39727] ⟨158909, 2, [(2, 2), (39727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39727
  · decide +kernel

theorem prime_197753 : Nat.Prime 197753 := by
  apply nodeValid_prime [2, 19, 1301] ⟨197753, 3, [(2, 3), (19, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1301
  · decide +kernel

theorem prime_232709 : Nat.Prime 232709 := by
  apply nodeValid_prime [2, 7, 8311] ⟨232709, 2, [(2, 2), (7, 1), (8311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8311
  · decide +kernel

theorem prime_253229 : Nat.Prime 253229 := by
  apply nodeValid_prime [2, 29, 37, 59] ⟨253229, 2, [(2, 2), (29, 1), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_258157 : Nat.Prime 258157 := by
  apply nodeValid_prime [2, 3, 71, 101] ⟨258157, 2, [(2, 2), (3, 2), (71, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_101
  · decide +kernel

theorem prime_259691 : Nat.Prime 259691 := by
  apply nodeValid_prime [2, 5, 25969] ⟨259691, 2, [(2, 1), (5, 1), (25969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25969
  · decide +kernel

theorem prime_265091 : Nat.Prime 265091 := by
  apply nodeValid_prime [2, 5, 7, 541] ⟨265091, 6, [(2, 1), (5, 1), (7, 2), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_541
  · decide +kernel

theorem prime_295441 : Nat.Prime 295441 := by
  apply nodeValid_prime [2, 3, 5, 1231] ⟨295441, 19, [(2, 4), (3, 1), (5, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1231
  · decide +kernel

theorem prime_296971 : Nat.Prime 296971 := by
  apply nodeValid_prime [2, 3, 5, 19, 521] ⟨296971, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_521
  · decide +kernel

theorem prime_329209 : Nat.Prime 329209 := by
  apply nodeValid_prime [2, 3, 11, 29, 43] ⟨329209, 14, [(2, 3), (3, 1), (11, 1), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_337721 : Nat.Prime 337721 := by
  apply nodeValid_prime [2, 5, 8443] ⟨337721, 3, [(2, 3), (5, 1), (8443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8443
  · decide +kernel

theorem prime_349519 : Nat.Prime 349519 := by
  apply nodeValid_prime [2, 3, 13, 4481] ⟨349519, 6, [(2, 1), (3, 1), (13, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4481
  · decide +kernel

theorem prime_427939 : Nat.Prime 427939 := by
  apply nodeValid_prime [2, 3, 7, 23, 443] ⟨427939, 3, [(2, 1), (3, 1), (7, 1), (23, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_443
  · decide +kernel

theorem prime_465419 : Nat.Prime 465419 := by
  apply nodeValid_prime [2, 232709] ⟨465419, 2, [(2, 1), (232709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_232709
  · decide +kernel

theorem prime_477409 : Nat.Prime 477409 := by
  apply nodeValid_prime [2, 3, 4973] ⟨477409, 19, [(2, 5), (3, 1), (4973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4973
  · decide +kernel

theorem prime_487391 : Nat.Prime 487391 := by
  apply nodeValid_prime [2, 5, 17, 47, 61] ⟨487391, 7, [(2, 1), (5, 1), (17, 1), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_519383 : Nat.Prime 519383 := by
  apply nodeValid_prime [2, 259691] ⟨519383, 5, [(2, 1), (259691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_259691
  · decide +kernel

theorem prime_647371 : Nat.Prime 647371 := by
  apply nodeValid_prime [2, 3, 5, 7193] ⟨647371, 3, [(2, 1), (3, 2), (5, 1), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7193
  · decide +kernel

theorem prime_842587 : Nat.Prime 842587 := by
  apply nodeValid_prime [2, 3, 317, 443] ⟨842587, 7, [(2, 1), (3, 1), (317, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
    · exact prime_443
  · decide +kernel

theorem prime_868349 : Nat.Prime 868349 := by
  apply nodeValid_prime [2, 13, 16699] ⟨868349, 2, [(2, 2), (13, 1), (16699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_16699
  · decide +kernel

theorem prime_883121 : Nat.Prime 883121 := by
  apply nodeValid_prime [2, 5, 7, 19, 83] ⟨883121, 3, [(2, 4), (5, 1), (7, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_939119 : Nat.Prime 939119 := by
  apply nodeValid_prime [2, 499, 941] ⟨939119, 11, [(2, 1), (499, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_499
    · exact prime_941
  · decide +kernel

theorem prime_986983 : Nat.Prime 986983 := by
  apply nodeValid_prime [2, 3, 271, 607] ⟨986983, 3, [(2, 1), (3, 1), (271, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_607
  · decide +kernel

theorem prime_1061807 : Nat.Prime 1061807 := by
  apply nodeValid_prime [2, 29, 18307] ⟨1061807, 5, [(2, 1), (29, 1), (18307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_18307
  · decide +kernel

theorem prime_1352963 : Nat.Prime 1352963 := by
  apply nodeValid_prime [2, 13, 17, 3061] ⟨1352963, 2, [(2, 1), (13, 1), (17, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_3061
  · decide +kernel

theorem prime_1641403 : Nat.Prime 1641403 := by
  apply nodeValid_prime [2, 3, 7, 1861] ⟨1641403, 7, [(2, 1), (3, 2), (7, 2), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1861
  · decide +kernel

theorem prime_1766243 : Nat.Prime 1766243 := by
  apply nodeValid_prime [2, 883121] ⟨1766243, 2, [(2, 1), (883121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_883121
  · decide +kernel

theorem prime_1987549 : Nat.Prime 1987549 := by
  apply nodeValid_prime [2, 3, 89, 1861] ⟨1987549, 2, [(2, 2), (3, 1), (89, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_1861
  · decide +kernel

theorem prime_2095493 : Nat.Prime 2095493 := by
  apply nodeValid_prime [2, 7, 67, 1117] ⟨2095493, 2, [(2, 2), (7, 1), (67, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_1117
  · decide +kernel

theorem prime_2103403 : Nat.Prime 2103403 := by
  apply nodeValid_prime [2, 3, 7, 61, 821] ⟨2103403, 2, [(2, 1), (3, 1), (7, 1), (61, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_821
  · decide +kernel

theorem prime_2232271 : Nat.Prime 2232271 := by
  apply nodeValid_prime [2, 3, 5, 17, 1459] ⟨2232271, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1459
  · decide +kernel

theorem prime_2876117 : Nat.Prime 2876117 := by
  apply nodeValid_prime [2, 83, 8663] ⟨2876117, 2, [(2, 2), (83, 1), (8663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_8663
  · decide +kernel

theorem prime_4063699 : Nat.Prime 4063699 := by
  apply nodeValid_prime [2, 3, 61, 3701] ⟨4063699, 2, [(2, 1), (3, 2), (61, 1), (3701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_3701
  · decide +kernel

theorem prime_4705751 : Nat.Prime 4705751 := by
  apply nodeValid_prime [2, 5, 7, 2689] ⟨4705751, 13, [(2, 1), (5, 3), (7, 1), (2689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2689
  · decide +kernel

theorem prime_5701763 : Nat.Prime 5701763 := by
  apply nodeValid_prime [2, 11, 23561] ⟨5701763, 5, [(2, 1), (11, 2), (23561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23561
  · decide +kernel

theorem prime_8425871 : Nat.Prime 8425871 := by
  apply nodeValid_prime [2, 5, 842587] ⟨8425871, 11, [(2, 1), (5, 1), (842587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_842587
  · decide +kernel

theorem prime_9797279 : Nat.Prime 9797279 := by
  apply nodeValid_prime [2, 41, 163, 733] ⟨9797279, 7, [(2, 1), (41, 1), (163, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_163
    · exact prime_733
  · decide +kernel

theorem prime_10080193 : Nat.Prime 10080193 := by
  apply nodeValid_prime [2, 3, 52501] ⟨10080193, 10, [(2, 6), (3, 1), (52501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52501
  · decide +kernel

theorem prime_10689013 : Nat.Prime 10689013 := by
  apply nodeValid_prime [2, 3, 97, 3061] ⟨10689013, 2, [(2, 2), (3, 2), (97, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_3061
  · decide +kernel

theorem prime_11139361 : Nat.Prime 11139361 := by
  apply nodeValid_prime [2, 3, 5, 23, 1009] ⟨11139361, 11, [(2, 5), (3, 1), (5, 1), (23, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1009
  · decide +kernel

theorem prime_13609691 : Nat.Prime 13609691 := by
  apply nodeValid_prime [2, 5, 17, 223, 359] ⟨13609691, 2, [(2, 1), (5, 1), (17, 1), (223, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_223
    · exact prime_359
  · decide +kernel

theorem prime_16373407 : Nat.Prime 16373407 := by
  apply nodeValid_prime [2, 3, 7, 97, 4019] ⟨16373407, 5, [(2, 1), (3, 1), (7, 1), (97, 1), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_4019
  · decide +kernel

theorem prime_20263387 : Nat.Prime 20263387 := by
  apply nodeValid_prime [2, 3, 11, 13, 19, 113] ⟨20263387, 2, [(2, 1), (3, 1), (11, 2), (13, 1), (19, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_113
  · decide +kernel

theorem prime_20992159 : Nat.Prime 20992159 := by
  apply nodeValid_prime [2, 3, 11, 97, 1093] ⟨20992159, 3, [(2, 1), (3, 2), (11, 1), (97, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_1093
  · decide +kernel

theorem prime_21236141 : Nat.Prime 21236141 := by
  apply nodeValid_prime [2, 5, 1061807] ⟨21236141, 2, [(2, 2), (5, 1), (1061807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1061807
  · decide +kernel

theorem prime_23044631 : Nat.Prime 23044631 := by
  apply nodeValid_prime [2, 5, 7, 329209] ⟨23044631, 7, [(2, 1), (5, 1), (7, 1), (329209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_329209
  · decide +kernel

theorem prime_39147539 : Nat.Prime 39147539 := by
  apply nodeValid_prime [2, 41, 477409] ⟨39147539, 2, [(2, 1), (41, 1), (477409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_477409
  · decide +kernel

theorem prime_44279083 : Nat.Prime 44279083 := by
  apply nodeValid_prime [2, 3, 19, 103, 419] ⟨44279083, 3, [(2, 1), (3, 3), (19, 1), (103, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_103
    · exact prime_419
  · decide +kernel

theorem prime_48255737 : Nat.Prime 48255737 := by
  apply nodeValid_prime [2, 149, 40483] ⟨48255737, 3, [(2, 3), (149, 1), (40483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_40483
  · decide +kernel

theorem prime_50149277 : Nat.Prime 50149277 := by
  apply nodeValid_prime [2, 641, 19559] ⟨50149277, 2, [(2, 2), (641, 1), (19559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_19559
  · decide +kernel

theorem prime_56598361 : Nat.Prime 56598361 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 71, 73] ⟨56598361, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (71, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_71
    · exact prime_73
  · decide +kernel

theorem prime_59209663 : Nat.Prime 59209663 := by
  apply nodeValid_prime [2, 3, 19, 519383] ⟨59209663, 7, [(2, 1), (3, 1), (19, 1), (519383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_519383
  · decide +kernel

theorem prime_68514463 : Nat.Prime 68514463 := by
  apply nodeValid_prime [2, 3, 683, 5573] ⟨68514463, 3, [(2, 1), (3, 2), (683, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_5573
  · decide +kernel

theorem prime_69026809 : Nat.Prime 69026809 := by
  apply nodeValid_prime [2, 3, 2876117] ⟨69026809, 7, [(2, 3), (3, 1), (2876117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2876117
  · decide +kernel

theorem prime_110593009 : Nat.Prime 110593009 := by
  apply nodeValid_prime [2, 3, 29, 71, 373] ⟨110593009, 11, [(2, 4), (3, 2), (29, 1), (71, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_71
    · exact prime_373
  · decide +kernel

theorem prime_150963551 : Nat.Prime 150963551 := by
  apply nodeValid_prime [2, 5, 19, 158909] ⟨150963551, 7, [(2, 1), (5, 2), (19, 1), (158909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_158909
  · decide +kernel

theorem prime_178879411 : Nat.Prime 178879411 := by
  apply nodeValid_prime [2, 3, 5, 1987549] ⟨178879411, 3, [(2, 1), (3, 2), (5, 1), (1987549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1987549
  · decide +kernel

theorem prime_200597149 : Nat.Prime 200597149 := by
  apply nodeValid_prime [2, 3, 113, 5479] ⟨200597149, 2, [(2, 2), (3, 4), (113, 1), (5479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_5479
  · decide +kernel

theorem prime_210483473 : Nat.Prime 210483473 := by
  apply nodeValid_prime [2, 211, 62347] ⟨210483473, 3, [(2, 4), (211, 1), (62347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_62347
  · decide +kernel

theorem prime_301927103 : Nat.Prime 301927103 := by
  apply nodeValid_prime [2, 150963551] ⟨301927103, 5, [(2, 1), (150963551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_150963551
  · decide +kernel

theorem prime_528254737 : Nat.Prime 528254737 := by
  apply nodeValid_prime [2, 3, 17, 647371] ⟨528254737, 10, [(2, 4), (3, 1), (17, 1), (647371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_647371
  · decide +kernel

theorem prime_726664193 : Nat.Prime 726664193 := by
  apply nodeValid_prime [2, 73, 9721] ⟨726664193, 3, [(2, 10), (73, 1), (9721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_9721
  · decide +kernel

theorem prime_1071490081 : Nat.Prime 1071490081 := by
  apply nodeValid_prime [2, 3, 5, 2232271] ⟨1071490081, 17, [(2, 5), (3, 1), (5, 1), (2232271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2232271
  · decide +kernel

theorem prime_1847783969 : Nat.Prime 1847783969 := by
  apply nodeValid_prime [2, 997, 57917] ⟨1847783969, 3, [(2, 5), (997, 1), (57917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_997
    · exact prime_57917
  · decide +kernel

theorem prime_1865152609 : Nat.Prime 1865152609 := by
  apply nodeValid_prime [2, 3, 11, 1766243] ⟨1865152609, 7, [(2, 5), (3, 1), (11, 1), (1766243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1766243
  · decide +kernel

theorem prime_2309757739 : Nat.Prime 2309757739 := by
  apply nodeValid_prime [2, 3, 1303, 295441] ⟨2309757739, 3, [(2, 1), (3, 1), (1303, 1), (295441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1303
    · exact prime_295441
  · decide +kernel

theorem prime_3719442973 : Nat.Prime 3719442973 := by
  apply nodeValid_prime [2, 3, 7, 44279083] ⟨3719442973, 2, [(2, 2), (3, 1), (7, 1), (44279083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_44279083
  · decide +kernel

theorem prime_4414672159 : Nat.Prime 4414672159 := by
  apply nodeValid_prime [2, 3, 13, 56598361] ⟨4414672159, 6, [(2, 1), (3, 1), (13, 1), (56598361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_56598361
  · decide +kernel

theorem prime_4559262107 : Nat.Prime 4559262107 := by
  apply nodeValid_prime [2, 7, 761, 427939] ⟨4559262107, 2, [(2, 1), (7, 1), (761, 1), (427939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_761
    · exact prime_427939
  · decide +kernel

theorem prime_4966506203 : Nat.Prime 4966506203 := by
  apply nodeValid_prime [2, 7, 263, 379, 3559] ⟨4966506203, 2, [(2, 1), (7, 1), (263, 1), (379, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_263
    · exact prime_379
    · exact prime_3559
  · decide +kernel

theorem prime_5494152683 : Nat.Prime 5494152683 := by
  apply nodeValid_prime [2, 257, 10689013] ⟨5494152683, 2, [(2, 1), (257, 1), (10689013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_10689013
  · decide +kernel

theorem prime_9933012407 : Nat.Prime 9933012407 := by
  apply nodeValid_prime [2, 4966506203] ⟨9933012407, 5, [(2, 1), (4966506203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4966506203
  · decide +kernel

theorem prime_10228468447 : Nat.Prime 10228468447 := by
  apply nodeValid_prime [2, 3, 7, 271, 42793] ⟨10228468447, 3, [(2, 1), (3, 2), (7, 2), (271, 1), (42793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_271
    · exact prime_42793
  · decide +kernel

theorem prime_40913873789 : Nat.Prime 40913873789 := by
  apply nodeValid_prime [2, 10228468447] ⟨40913873789, 2, [(2, 2), (10228468447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10228468447
  · decide +kernel

theorem prime_41033357399 : Nat.Prime 41033357399 := by
  apply nodeValid_prime [2, 11, 1865152609] ⟨41033357399, 11, [(2, 1), (11, 1), (1865152609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1865152609
  · decide +kernel

theorem prime_76689481457 : Nat.Prime 76689481457 := by
  apply nodeValid_prime [2, 7, 17, 37, 241, 4517] ⟨76689481457, 5, [(2, 4), (7, 1), (17, 1), (37, 1), (241, 1), (4517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_37
    · exact prime_241
    · exact prime_4517
  · decide +kernel

theorem prime_76689484163 : Nat.Prime 76689484163 := by
  apply nodeValid_prime [2, 127, 301927103] ⟨76689484163, 2, [(2, 1), (127, 1), (301927103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_301927103
  · decide +kernel

theorem prime_76689484769 : Nat.Prime 76689484769 := by
  apply nodeValid_prime [2, 13, 19, 29, 83, 139] ⟨76689484769, 3, [(2, 5), (13, 1), (19, 1), (29, 2), (83, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_29
    · exact prime_83
    · exact prime_139
  · decide +kernel

theorem prime_76918137563 : Nat.Prime 76918137563 := by
  apply nodeValid_prime [2, 7, 5494152683] ⟨76918137563, 2, [(2, 1), (7, 1), (5494152683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5494152683
  · decide +kernel

theorem prime_76918137649 : Nat.Prime 76918137649 := by
  apply nodeValid_prime [2, 3, 11, 53, 79, 3163] ⟨76918137649, 7, [(2, 4), (3, 1), (11, 2), (53, 1), (79, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_79
    · exact prime_3163
  · decide +kernel

theorem prime_76918146731 : Nat.Prime 76918146731 := by
  apply nodeValid_prime [2, 5, 43, 178879411] ⟨76918146731, 2, [(2, 1), (5, 1), (43, 1), (178879411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_178879411
  · decide +kernel

theorem prime_77147274877 : Nat.Prime 77147274877 := by
  apply nodeValid_prime [2, 3, 7, 109, 8425871] ⟨77147274877, 2, [(2, 2), (3, 1), (7, 1), (109, 1), (8425871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
    · exact prime_8425871
  · decide +kernel

theorem prime_77147285339 : Nat.Prime 77147285339 := by
  apply nodeValid_prime [2, 563, 68514463] ⟨77147285339, 2, [(2, 1), (563, 1), (68514463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_68514463
  · decide +kernel

theorem prime_77147285833 : Nat.Prime 77147285833 := by
  apply nodeValid_prime [2, 3, 1071490081] ⟨77147285833, 10, [(2, 3), (3, 2), (1071490081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1071490081
  · decide +kernel

theorem prime_77376865399 : Nat.Prime 77376865399 := by
  apply nodeValid_prime [2, 3, 7, 43, 89, 68771] ⟨77376865399, 3, [(2, 1), (3, 1), (7, 2), (43, 1), (89, 1), (68771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_89
    · exact prime_68771
  · decide +kernel

theorem prime_77376881297 : Nat.Prime 77376881297 := by
  apply nodeValid_prime [2, 11, 13, 131, 258157] ⟨77376881297, 3, [(2, 4), (11, 1), (13, 1), (131, 1), (258157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_131
    · exact prime_258157
  · decide +kernel

theorem prime_77376881809 : Nat.Prime 77376881809 := by
  apply nodeValid_prime [2, 3, 2027, 265091] ⟨77376881809, 7, [(2, 4), (3, 2), (2027, 1), (265091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2027
    · exact prime_265091
  · decide +kernel

theorem prime_77606915923 : Nat.Prime 77606915923 := by
  apply nodeValid_prime [2, 3, 4591, 939119] ⟨77606915923, 2, [(2, 1), (3, 2), (4591, 1), (939119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4591
    · exact prime_939119
  · decide +kernel

theorem prime_77606924293 : Nat.Prime 77606924293 := by
  apply nodeValid_prime [2, 3, 41, 5647, 9311] ⟨77606924293, 2, [(2, 2), (3, 2), (41, 1), (5647, 1), (9311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_5647
    · exact prime_9311
  · decide +kernel

theorem prime_77606926699 : Nat.Prime 77606926699 := by
  apply nodeValid_prime [2, 3, 7, 1847783969] ⟨77606926699, 3, [(2, 1), (3, 1), (7, 1), (1847783969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1847783969
  · decide +kernel

theorem prime_77837427313 : Nat.Prime 77837427313 := by
  apply nodeValid_prime [2, 3, 31, 53, 986983] ⟨77837427313, 5, [(2, 4), (3, 1), (31, 1), (53, 1), (986983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
    · exact prime_986983
  · decide +kernel

theorem prime_77837428387 : Nat.Prime 77837428387 := by
  apply nodeValid_prime [2, 3, 17, 83, 229, 1487] ⟨77837428387, 3, [(2, 1), (3, 4), (17, 1), (83, 1), (229, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_83
    · exact prime_229
    · exact prime_1487
  · decide +kernel

theorem prime_77837428489 : Nat.Prime 77837428489 := by
  apply nodeValid_prime [2, 3, 17, 67, 42499] ⟨77837428489, 11, [(2, 3), (3, 1), (17, 1), (67, 2), (42499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
    · exact prime_42499
  · decide +kernel

theorem prime_78068404577 : Nat.Prime 78068404577 := by
  apply nodeValid_prime [2, 149, 16373407] ⟨78068404577, 3, [(2, 5), (149, 1), (16373407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_16373407
  · decide +kernel

theorem prime_78068409091 : Nat.Prime 78068409091 := by
  apply nodeValid_prime [2, 3, 5, 7, 79, 4705751] ⟨78068409091, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (79, 1), (4705751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_79
    · exact prime_4705751
  · decide +kernel

theorem prime_78068409487 : Nat.Prime 78068409487 := by
  apply nodeValid_prime [2, 3, 7927, 1641403] ⟨78068409487, 5, [(2, 1), (3, 1), (7927, 1), (1641403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7927
    · exact prime_1641403
  · decide +kernel

theorem prime_78299850373 : Nat.Prime 78299850373 := by
  apply nodeValid_prime [2, 3, 59, 110593009] ⟨78299850373, 2, [(2, 2), (3, 1), (59, 1), (110593009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_110593009
  · decide +kernel

theorem prime_78299851957 : Nat.Prime 78299851957 := by
  apply nodeValid_prime [2, 3, 31, 210483473] ⟨78299851957, 6, [(2, 2), (3, 1), (31, 1), (210483473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_210483473
  · decide +kernel

theorem prime_78299853769 : Nat.Prime 78299853769 := by
  apply nodeValid_prime [2, 3, 37, 9797279] ⟨78299853769, 13, [(2, 3), (3, 3), (37, 1), (9797279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_9797279
  · decide +kernel

theorem prime_78531763127 : Nat.Prime 78531763127 := by
  apply nodeValid_prime [2, 17, 2309757739] ⟨78531763127, 5, [(2, 1), (17, 1), (2309757739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2309757739
  · decide +kernel

theorem prime_78531765283 : Nat.Prime 78531765283 := by
  apply nodeValid_prime [2, 3, 53377, 81737] ⟨78531765283, 3, [(2, 1), (3, 2), (53377, 1), (81737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53377
    · exact prime_81737
  · decide +kernel

theorem prime_78531765337 : Nat.Prime 78531765337 := by
  apply nodeValid_prime [2, 3, 17, 2347, 27337] ⟨78531765337, 5, [(2, 3), (3, 2), (17, 1), (2347, 1), (27337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2347
    · exact prime_27337
  · decide +kernel

theorem prime_78764145457 : Nat.Prime 78764145457 := by
  apply nodeValid_prime [2, 3, 37, 53, 727, 1151] ⟨78764145457, 10, [(2, 4), (3, 1), (37, 1), (53, 1), (727, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_53
    · exact prime_727
    · exact prime_1151
  · decide +kernel

theorem prime_78764154083 : Nat.Prime 78764154083 := by
  apply nodeValid_prime [2, 6907, 5701763] ⟨78764154083, 2, [(2, 1), (6907, 1), (5701763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6907
    · exact prime_5701763
  · decide +kernel

theorem prime_78764154191 : Nat.Prime 78764154191 := by
  apply nodeValid_prime [2, 5, 79, 887, 112403] ⟨78764154191, 7, [(2, 1), (5, 1), (79, 1), (887, 1), (112403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_887
    · exact prime_112403
  · decide +kernel

theorem prime_78996994553 : Nat.Prime 78996994553 := by
  apply nodeValid_prime [2, 7, 4177, 337721] ⟨78996994553, 3, [(2, 3), (7, 1), (4177, 1), (337721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4177
    · exact prime_337721
  · decide +kernel

theorem prime_78996995069 : Nat.Prime 78996995069 := by
  apply nodeValid_prime [2, 857, 23044631] ⟨78996995069, 2, [(2, 2), (857, 1), (23044631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_857
    · exact prime_23044631
  · decide +kernel

theorem prime_78996997021 : Nat.Prime 78996997021 := by
  apply nodeValid_prime [2, 3, 5, 29, 881, 1777] ⟨78996997021, 7, [(2, 2), (3, 1), (5, 1), (29, 2), (881, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_881
    · exact prime_1777
  · decide +kernel

theorem prime_79230312781 : Nat.Prime 79230312781 := by
  apply nodeValid_prime [2, 3, 5, 32069, 41177] ⟨79230312781, 2, [(2, 2), (3, 1), (5, 1), (32069, 1), (41177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_32069
    · exact prime_41177
  · decide +kernel

theorem prime_79230316981 : Nat.Prime 79230316981 := by
  apply nodeValid_prime [2, 3, 5, 131, 10080193] ⟨79230316981, 2, [(2, 2), (3, 1), (5, 1), (131, 1), (10080193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_10080193
  · decide +kernel

theorem prime_79230317267 : Nat.Prime 79230317267 := by
  apply nodeValid_prime [2, 17, 31, 5209, 14431] ⟨79230317267, 2, [(2, 1), (17, 1), (31, 1), (5209, 1), (14431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_5209
    · exact prime_14431
  · decide +kernel

theorem prime_79464094123 : Nat.Prime 79464094123 := by
  apply nodeValid_prime [2, 3, 7, 23, 277, 296971] ⟨79464094123, 2, [(2, 1), (3, 1), (7, 1), (23, 1), (277, 1), (296971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_277
    · exact prime_296971
  · decide +kernel

theorem prime_79464098863 : Nat.Prime 79464098863 := by
  apply nodeValid_prime [2, 3, 4414672159] ⟨79464098863, 5, [(2, 1), (3, 2), (4414672159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4414672159
  · decide +kernel

theorem prime_79464099257 : Nat.Prime 79464099257 := by
  apply nodeValid_prime [2, 9933012407] ⟨79464099257, 3, [(2, 3), (9933012407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9933012407
  · decide +kernel

theorem prime_79698343001 : Nat.Prime 79698343001 := by
  apply nodeValid_prime [2, 5, 83, 89, 10789] ⟨79698343001, 3, [(2, 3), (5, 3), (83, 1), (89, 1), (10789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_89
    · exact prime_10789
  · decide +kernel

theorem prime_79698349561 : Nat.Prime 79698349561 := by
  apply nodeValid_prime [2, 3, 5, 1427, 465419] ⟨79698349561, 21, [(2, 3), (3, 1), (5, 1), (1427, 1), (465419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1427
    · exact prime_465419
  · decide +kernel

theorem prime_79698350497 : Nat.Prime 79698350497 := by
  apply nodeValid_prime [2, 3, 61, 13609691] ⟨79698350497, 5, [(2, 5), (3, 1), (61, 1), (13609691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_13609691
  · decide +kernel

theorem prime_79933044823 : Nat.Prime 79933044823 := by
  apply nodeValid_prime [2, 3, 193, 69026809] ⟨79933044823, 3, [(2, 1), (3, 1), (193, 1), (69026809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_69026809
  · decide +kernel

theorem prime_79933045051 : Nat.Prime 79933045051 := by
  apply nodeValid_prime [2, 3, 5, 59209663] ⟨79933045051, 2, [(2, 1), (3, 3), (5, 2), (59209663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59209663
  · decide +kernel

theorem prime_79933061231 : Nat.Prime 79933061231 := by
  apply nodeValid_prime [2, 5, 11, 726664193] ⟨79933061231, 7, [(2, 1), (5, 1), (11, 1), (726664193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_726664193
  · decide +kernel

theorem prime_80168249737 : Nat.Prime 80168249737 := by
  apply nodeValid_prime [2, 3, 4397, 253229] ⟨80168249737, 5, [(2, 3), (3, 2), (4397, 1), (253229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4397
    · exact prime_253229
  · decide +kernel

theorem prime_80168275189 : Nat.Prime 80168275189 := by
  apply nodeValid_prime [2, 3, 11261, 197753] ⟨80168275189, 2, [(2, 2), (3, 2), (11261, 1), (197753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11261
    · exact prime_197753
  · decide +kernel

theorem prime_80168276233 : Nat.Prime 80168276233 := by
  apply nodeValid_prime [2, 3, 11, 3499, 9643] ⟨80168276233, 7, [(2, 3), (3, 3), (11, 1), (3499, 1), (9643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3499
    · exact prime_9643
  · decide +kernel

theorem prime_80403907307 : Nat.Prime 80403907307 := by
  apply nodeValid_prime [2, 67, 691, 868349] ⟨80403907307, 2, [(2, 1), (67, 1), (691, 1), (868349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_691
    · exact prime_868349
  · decide +kernel

theorem prime_80403907699 : Nat.Prime 80403907699 := by
  apply nodeValid_prime [2, 3, 401, 11139361] ⟨80403907699, 2, [(2, 1), (3, 2), (401, 1), (11139361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_11139361
  · decide +kernel

theorem prime_80403909301 : Nat.Prime 80403909301 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 19, 131, 251] ⟨80403909301, 6, [(2, 2), (3, 2), (5, 2), (11, 1), (13, 1), (19, 1), (131, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_131
    · exact prime_251
  · decide +kernel

theorem prime_80640037417 : Nat.Prime 80640037417 := by
  apply nodeValid_prime [2, 3, 67, 50149277] ⟨80640037417, 19, [(2, 3), (3, 1), (67, 1), (50149277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_50149277
  · decide +kernel

theorem prime_80640053183 : Nat.Prime 80640053183 := by
  apply nodeValid_prime [2, 13, 43, 257, 21589] ⟨80640053183, 5, [(2, 1), (13, 2), (43, 1), (257, 1), (21589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_257
    · exact prime_21589
  · decide +kernel

theorem prime_80640053899 : Nat.Prime 80640053899 := by
  apply nodeValid_prime [2, 3, 67, 200597149] ⟨80640053899, 2, [(2, 1), (3, 1), (67, 1), (200597149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_200597149
  · decide +kernel

theorem prime_80876614873 : Nat.Prime 80876614873 := by
  apply nodeValid_prime [2, 3, 37, 2777, 32797] ⟨80876614873, 5, [(2, 3), (3, 1), (37, 1), (2777, 1), (32797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2777
    · exact prime_32797
  · decide +kernel

theorem prime_80876615213 : Nat.Prime 80876615213 := by
  apply nodeValid_prime [2, 419, 48255737] ⟨80876615213, 2, [(2, 2), (419, 1), (48255737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_48255737
  · decide +kernel

theorem prime_80876634871 : Nat.Prime 80876634871 := by
  apply nodeValid_prime [2, 3, 5, 17, 4261, 37217] ⟨80876634871, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (4261, 1), (37217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_4261
    · exact prime_37217
  · decide +kernel

theorem prime_81113700587 : Nat.Prime 81113700587 := by
  apply nodeValid_prime [2, 37, 809, 1117, 1213] ⟨81113700587, 2, [(2, 1), (37, 1), (809, 1), (1117, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_809
    · exact prime_1117
    · exact prime_1213
  · decide +kernel

theorem prime_81113700809 : Nat.Prime 81113700809 := by
  apply nodeValid_prime [2, 7, 37, 39147539] ⟨81113700809, 13, [(2, 3), (7, 1), (37, 1), (39147539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_39147539
  · decide +kernel

theorem prime_81113702377 : Nat.Prime 81113702377 := by
  apply nodeValid_prime [2, 3, 7, 23, 20992159] ⟨81113702377, 10, [(2, 3), (3, 1), (7, 1), (23, 1), (20992159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_20992159
  · decide +kernel

theorem prime_81351229247 : Nat.Prime 81351229247 := by
  apply nodeValid_prime [2, 7, 47, 59, 2095493] ⟨81351229247, 5, [(2, 1), (7, 1), (47, 1), (59, 1), (2095493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_59
    · exact prime_2095493
  · decide +kernel

theorem prime_81351229499 : Nat.Prime 81351229499 := by
  apply nodeValid_prime [2, 7, 11, 528254737] ⟨81351229499, 2, [(2, 1), (7, 1), (11, 1), (528254737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_528254737
  · decide +kernel

theorem prime_81351246289 : Nat.Prime 81351246289 := by
  apply nodeValid_prime [2, 3, 13, 373, 349519] ⟨81351246289, 14, [(2, 4), (3, 1), (13, 1), (373, 1), (349519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_373
    · exact prime_349519
  · decide +kernel

theorem prime_81589253401 : Nat.Prime 81589253401 := by
  apply nodeValid_prime [2, 3, 5, 31, 487391] ⟨81589253401, 7, [(2, 3), (3, 3), (5, 2), (31, 1), (487391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_487391
  · decide +kernel

theorem prime_81589253723 : Nat.Prime 81589253723 := by
  apply nodeValid_prime [2, 17, 113, 21236141] ⟨81589253723, 2, [(2, 1), (17, 1), (113, 1), (21236141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_113
    · exact prime_21236141
  · decide +kernel

theorem prime_81589264609 : Nat.Prime 81589264609 := by
  apply nodeValid_prime [2, 3, 61, 1423, 9791] ⟨81589264609, 7, [(2, 5), (3, 1), (61, 1), (1423, 1), (9791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_1423
    · exact prime_9791
  · decide +kernel

theorem prime_81827745407 : Nat.Prime 81827745407 := by
  apply nodeValid_prime [2, 11, 3719442973] ⟨81827745407, 5, [(2, 1), (11, 1), (3719442973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3719442973
  · decide +kernel

theorem prime_81827747579 : Nat.Prime 81827747579 := by
  apply nodeValid_prime [2, 40913873789] ⟨81827747579, 2, [(2, 1), (40913873789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40913873789
  · decide +kernel

theorem prime_81827753893 : Nat.Prime 81827753893 := by
  apply nodeValid_prime [2, 3, 37, 4357, 42299] ⟨81827753893, 2, [(2, 2), (3, 1), (37, 1), (4357, 1), (42299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4357
    · exact prime_42299
  · decide +kernel

theorem prime_82066714799 : Nat.Prime 82066714799 := by
  apply nodeValid_prime [2, 41033357399] ⟨82066714799, 11, [(2, 1), (41033357399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41033357399
  · decide +kernel

theorem prime_82066717351 : Nat.Prime 82066717351 := by
  apply nodeValid_prime [2, 3, 5, 20263387] ⟨82066717351, 3, [(2, 1), (3, 4), (5, 2), (20263387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20263387
  · decide +kernel

theorem prime_82066717927 : Nat.Prime 82066717927 := by
  apply nodeValid_prime [2, 3, 4559262107] ⟨82066717927, 3, [(2, 1), (3, 2), (4559262107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4559262107
  · decide +kernel

theorem prime_82306151143 : Nat.Prime 82306151143 := by
  apply nodeValid_prime [2, 3, 10139, 1352963] ⟨82306151143, 3, [(2, 1), (3, 1), (10139, 1), (1352963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10139
    · exact prime_1352963
  · decide +kernel

theorem prime_82306159391 : Nat.Prime 82306159391 := by
  apply nodeValid_prime [2, 5, 7, 13, 43, 2103403] ⟨82306159391, 7, [(2, 1), (5, 1), (7, 1), (13, 1), (43, 1), (2103403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_2103403
  · decide +kernel

theorem prime_82306159547 : Nat.Prime 82306159547 := by
  apply nodeValid_prime [2, 13, 19, 41, 4063699] ⟨82306159547, 2, [(2, 1), (13, 1), (19, 1), (41, 1), (4063699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_41
    · exact prime_4063699
  · decide +kernel

end Sude.Lucas.Generated
