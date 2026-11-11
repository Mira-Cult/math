import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_313 : Nat.Prime 313 := by
  apply nodeValid_prime [2, 3, 13] ⟨313, 10, [(2, 3), (3, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_439 : Nat.Prime 439 := by
  apply nodeValid_prime [2, 3, 73] ⟨439, 15, [(2, 1), (3, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_461 : Nat.Prime 461 := by
  apply nodeValid_prime [2, 5, 23] ⟨461, 2, [(2, 2), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_523 : Nat.Prime 523 := by
  apply nodeValid_prime [2, 3, 29] ⟨523, 2, [(2, 1), (3, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_547 : Nat.Prime 547 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨547, 2, [(2, 1), (3, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_587 : Nat.Prime 587 := by
  apply nodeValid_prime [2, 293] ⟨587, 2, [(2, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_293
  · decide +kernel

theorem prime_617 : Nat.Prime 617 := by
  apply nodeValid_prime [2, 7, 11] ⟨617, 3, [(2, 3), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_619 : Nat.Prime 619 := by
  apply nodeValid_prime [2, 3, 103] ⟨619, 2, [(2, 1), (3, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_643 : Nat.Prime 643 := by
  apply nodeValid_prime [2, 3, 107] ⟨643, 11, [(2, 1), (3, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
  · decide +kernel

theorem prime_647 : Nat.Prime 647 := by
  apply nodeValid_prime [2, 17, 19] ⟨647, 5, [(2, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_661 : Nat.Prime 661 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨661, 2, [(2, 2), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_773 : Nat.Prime 773 := by
  apply nodeValid_prime [2, 193] ⟨773, 2, [(2, 2), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193
  · decide +kernel

theorem prime_877 : Nat.Prime 877 := by
  apply nodeValid_prime [2, 3, 73] ⟨877, 2, [(2, 2), (3, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_929 : Nat.Prime 929 := by
  apply nodeValid_prime [2, 29] ⟨929, 3, [(2, 5), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29
  · decide +kernel

theorem prime_967 : Nat.Prime 967 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨967, 5, [(2, 1), (3, 1), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_1019 : Nat.Prime 1019 := by
  apply nodeValid_prime [2, 509] ⟨1019, 2, [(2, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_509
  · decide +kernel

theorem prime_1171 : Nat.Prime 1171 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨1171, 2, [(2, 1), (3, 2), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_1217 : Nat.Prime 1217 := by
  apply nodeValid_prime [2, 19] ⟨1217, 3, [(2, 6), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19
  · decide +kernel

theorem prime_1277 : Nat.Prime 1277 := by
  apply nodeValid_prime [2, 11, 29] ⟨1277, 2, [(2, 2), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_1433 : Nat.Prime 1433 := by
  apply nodeValid_prime [2, 179] ⟨1433, 3, [(2, 3), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_179
  · decide +kernel

theorem prime_1439 : Nat.Prime 1439 := by
  apply nodeValid_prime [2, 719] ⟨1439, 7, [(2, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_719
  · decide +kernel

theorem prime_1471 : Nat.Prime 1471 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨1471, 6, [(2, 1), (3, 1), (5, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_1567 : Nat.Prime 1567 := by
  apply nodeValid_prime [2, 3, 29] ⟨1567, 3, [(2, 1), (3, 3), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_1609 : Nat.Prime 1609 := by
  apply nodeValid_prime [2, 3, 67] ⟨1609, 7, [(2, 3), (3, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
  · decide +kernel

theorem prime_1693 : Nat.Prime 1693 := by
  apply nodeValid_prime [2, 3, 47] ⟨1693, 2, [(2, 2), (3, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_2099 : Nat.Prime 2099 := by
  apply nodeValid_prime [2, 1049] ⟨2099, 2, [(2, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1049
  · decide +kernel

theorem prime_2111 : Nat.Prime 2111 := by
  apply nodeValid_prime [2, 5, 211] ⟨2111, 7, [(2, 1), (5, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
  · decide +kernel

theorem prime_2113 : Nat.Prime 2113 := by
  apply nodeValid_prime [2, 3, 11] ⟨2113, 5, [(2, 6), (3, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_2389 : Nat.Prime 2389 := by
  apply nodeValid_prime [2, 3, 199] ⟨2389, 2, [(2, 2), (3, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
  · decide +kernel

theorem prime_2441 : Nat.Prime 2441 := by
  apply nodeValid_prime [2, 5, 61] ⟨2441, 6, [(2, 3), (5, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_2617 : Nat.Prime 2617 := by
  apply nodeValid_prime [2, 3, 109] ⟨2617, 5, [(2, 3), (3, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_2693 : Nat.Prime 2693 := by
  apply nodeValid_prime [2, 673] ⟨2693, 2, [(2, 2), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_673
  · decide +kernel

theorem prime_2767 : Nat.Prime 2767 := by
  apply nodeValid_prime [2, 3, 461] ⟨2767, 3, [(2, 1), (3, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
  · decide +kernel

theorem prime_3067 : Nat.Prime 3067 := by
  apply nodeValid_prime [2, 3, 7, 73] ⟨3067, 2, [(2, 1), (3, 1), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_3083 : Nat.Prime 3083 := by
  apply nodeValid_prime [2, 23, 67] ⟨3083, 2, [(2, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_3089 : Nat.Prime 3089 := by
  apply nodeValid_prime [2, 193] ⟨3089, 3, [(2, 4), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193
  · decide +kernel

theorem prime_3209 : Nat.Prime 3209 := by
  apply nodeValid_prime [2, 401] ⟨3209, 3, [(2, 3), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_401
  · decide +kernel

theorem prime_3299 : Nat.Prime 3299 := by
  apply nodeValid_prime [2, 17, 97] ⟨3299, 2, [(2, 1), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_3769 : Nat.Prime 3769 := by
  apply nodeValid_prime [2, 3, 157] ⟨3769, 7, [(2, 3), (3, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
  · decide +kernel

theorem prime_3911 : Nat.Prime 3911 := by
  apply nodeValid_prime [2, 5, 17, 23] ⟨3911, 13, [(2, 1), (5, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_4337 : Nat.Prime 4337 := by
  apply nodeValid_prime [2, 271] ⟨4337, 3, [(2, 4), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_271
  · decide +kernel

theorem prime_4423 : Nat.Prime 4423 := by
  apply nodeValid_prime [2, 3, 11, 67] ⟨4423, 3, [(2, 1), (3, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_4441 : Nat.Prime 4441 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨4441, 21, [(2, 3), (3, 1), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_4637 : Nat.Prime 4637 := by
  apply nodeValid_prime [2, 19, 61] ⟨4637, 2, [(2, 2), (19, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_4969 : Nat.Prime 4969 := by
  apply nodeValid_prime [2, 3, 23] ⟨4969, 11, [(2, 3), (3, 3), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_5107 : Nat.Prime 5107 := by
  apply nodeValid_prime [2, 3, 23, 37] ⟨5107, 2, [(2, 1), (3, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_5387 : Nat.Prime 5387 := by
  apply nodeValid_prime [2, 2693] ⟨5387, 2, [(2, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2693
  · decide +kernel

theorem prime_5701 : Nat.Prime 5701 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨5701, 2, [(2, 2), (3, 1), (5, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_5827 : Nat.Prime 5827 := by
  apply nodeValid_prime [2, 3, 971] ⟨5827, 2, [(2, 1), (3, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_971
  · decide +kernel

theorem prime_6101 : Nat.Prime 6101 := by
  apply nodeValid_prime [2, 5, 61] ⟨6101, 2, [(2, 2), (5, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_6269 : Nat.Prime 6269 := by
  apply nodeValid_prime [2, 1567] ⟨6269, 2, [(2, 2), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1567
  · decide +kernel

theorem prime_6733 : Nat.Prime 6733 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨6733, 2, [(2, 2), (3, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_6977 : Nat.Prime 6977 := by
  apply nodeValid_prime [2, 109] ⟨6977, 3, [(2, 6), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_109
  · decide +kernel

theorem prime_7351 : Nat.Prime 7351 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨7351, 6, [(2, 1), (3, 1), (5, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_7639 : Nat.Prime 7639 := by
  apply nodeValid_prime [2, 3, 19, 67] ⟨7639, 7, [(2, 1), (3, 1), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_7823 : Nat.Prime 7823 := by
  apply nodeValid_prime [2, 3911] ⟨7823, 5, [(2, 1), (3911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3911
  · decide +kernel

theorem prime_8753 : Nat.Prime 8753 := by
  apply nodeValid_prime [2, 547] ⟨8753, 3, [(2, 4), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_547
  · decide +kernel

theorem prime_9209 : Nat.Prime 9209 := by
  apply nodeValid_prime [2, 1151] ⟨9209, 3, [(2, 3), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1151
  · decide +kernel

theorem prime_9491 : Nat.Prime 9491 := by
  apply nodeValid_prime [2, 5, 13, 73] ⟨9491, 2, [(2, 1), (5, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_10177 : Nat.Prime 10177 := by
  apply nodeValid_prime [2, 3, 53] ⟨10177, 7, [(2, 6), (3, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
  · decide +kernel

theorem prime_10427 : Nat.Prime 10427 := by
  apply nodeValid_prime [2, 13, 401] ⟨10427, 2, [(2, 1), (13, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_401
  · decide +kernel

theorem prime_10711 : Nat.Prime 10711 := by
  apply nodeValid_prime [2, 3, 5, 7, 17] ⟨10711, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_12203 : Nat.Prime 12203 := by
  apply nodeValid_prime [2, 6101] ⟨12203, 2, [(2, 1), (6101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6101
  · decide +kernel

theorem prime_13187 : Nat.Prime 13187 := by
  apply nodeValid_prime [2, 19, 347] ⟨13187, 2, [(2, 1), (19, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_347
  · decide +kernel

theorem prime_13933 : Nat.Prime 13933 := by
  apply nodeValid_prime [2, 3, 43] ⟨13933, 2, [(2, 2), (3, 4), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_14009 : Nat.Prime 14009 := by
  apply nodeValid_prime [2, 17, 103] ⟨14009, 3, [(2, 3), (17, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
  · decide +kernel

theorem prime_16319 : Nat.Prime 16319 := by
  apply nodeValid_prime [2, 41, 199] ⟨16319, 7, [(2, 1), (41, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_199
  · decide +kernel

theorem prime_16603 : Nat.Prime 16603 := by
  apply nodeValid_prime [2, 3, 2767] ⟨16603, 2, [(2, 1), (3, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2767
  · decide +kernel

theorem prime_17807 : Nat.Prime 17807 := by
  apply nodeValid_prime [2, 29, 307] ⟨17807, 5, [(2, 1), (29, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_307
  · decide +kernel

theorem prime_19163 : Nat.Prime 19163 := by
  apply nodeValid_prime [2, 11, 13, 67] ⟨19163, 2, [(2, 1), (11, 1), (13, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_22571 : Nat.Prime 22571 := by
  apply nodeValid_prime [2, 5, 37, 61] ⟨22571, 6, [(2, 1), (5, 1), (37, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_61
  · decide +kernel

theorem prime_26393 : Nat.Prime 26393 := by
  apply nodeValid_prime [2, 3299] ⟨26393, 3, [(2, 3), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3299
  · decide +kernel

theorem prime_28019 : Nat.Prime 28019 := by
  apply nodeValid_prime [2, 14009] ⟨28019, 2, [(2, 1), (14009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14009
  · decide +kernel

theorem prime_31649 : Nat.Prime 31649 := by
  apply nodeValid_prime [2, 23, 43] ⟨31649, 3, [(2, 5), (23, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
  · decide +kernel

theorem prime_31859 : Nat.Prime 31859 := by
  apply nodeValid_prime [2, 17, 937] ⟨31859, 2, [(2, 1), (17, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_937
  · decide +kernel

theorem prime_36997 : Nat.Prime 36997 := by
  apply nodeValid_prime [2, 3, 3083] ⟨36997, 2, [(2, 2), (3, 1), (3083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3083
  · decide +kernel

theorem prime_37181 : Nat.Prime 37181 := by
  apply nodeValid_prime [2, 5, 11, 13] ⟨37181, 2, [(2, 2), (5, 1), (11, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_44201 : Nat.Prime 44201 := by
  apply nodeValid_prime [2, 5, 13, 17] ⟨44201, 6, [(2, 3), (5, 2), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_44927 : Nat.Prime 44927 := by
  apply nodeValid_prime [2, 7, 3209] ⟨44927, 7, [(2, 1), (7, 1), (3209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3209
  · decide +kernel

theorem prime_44983 : Nat.Prime 44983 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨44983, 3, [(2, 1), (3, 3), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_48821 : Nat.Prime 48821 := by
  apply nodeValid_prime [2, 5, 2441] ⟨48821, 2, [(2, 2), (5, 1), (2441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2441
  · decide +kernel

theorem prime_55733 : Nat.Prime 55733 := by
  apply nodeValid_prime [2, 13933] ⟨55733, 2, [(2, 2), (13933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13933
  · decide +kernel

theorem prime_65581 : Nat.Prime 65581 := by
  apply nodeValid_prime [2, 3, 5, 1093] ⟨65581, 2, [(2, 2), (3, 1), (5, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1093
  · decide +kernel

theorem prime_71143 : Nat.Prime 71143 := by
  apply nodeValid_prime [2, 3, 71, 167] ⟨71143, 6, [(2, 1), (3, 1), (71, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_167
  · decide +kernel

theorem prime_72907 : Nat.Prime 72907 := by
  apply nodeValid_prime [2, 3, 29, 419] ⟨72907, 2, [(2, 1), (3, 1), (29, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_419
  · decide +kernel

theorem prime_73673 : Nat.Prime 73673 := by
  apply nodeValid_prime [2, 9209] ⟨73673, 3, [(2, 3), (9209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9209
  · decide +kernel

theorem prime_79939 : Nat.Prime 79939 := by
  apply nodeValid_prime [2, 3, 4441] ⟨79939, 3, [(2, 1), (3, 2), (4441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4441
  · decide +kernel

theorem prime_90749 : Nat.Prime 90749 := by
  apply nodeValid_prime [2, 7, 463] ⟨90749, 2, [(2, 2), (7, 2), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_463
  · decide +kernel

theorem prime_92431 : Nat.Prime 92431 := by
  apply nodeValid_prime [2, 3, 5, 13, 79] ⟨92431, 6, [(2, 1), (3, 2), (5, 1), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_104369 : Nat.Prime 104369 := by
  apply nodeValid_prime [2, 11, 593] ⟨104369, 3, [(2, 4), (11, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_593
  · decide +kernel

theorem prime_106033 : Nat.Prime 106033 := by
  apply nodeValid_prime [2, 3, 47] ⟨106033, 5, [(2, 4), (3, 1), (47, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_133519 : Nat.Prime 133519 := by
  apply nodeValid_prime [2, 3, 7, 11, 17] ⟨133519, 7, [(2, 1), (3, 1), (7, 1), (11, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_157433 : Nat.Prime 157433 := by
  apply nodeValid_prime [2, 11, 1789] ⟨157433, 3, [(2, 3), (11, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1789
  · decide +kernel

theorem prime_158359 : Nat.Prime 158359 := by
  apply nodeValid_prime [2, 3, 26393] ⟨158359, 11, [(2, 1), (3, 1), (26393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26393
  · decide +kernel

theorem prime_169079 : Nat.Prime 169079 := by
  apply nodeValid_prime [2, 7, 13, 929] ⟨169079, 11, [(2, 1), (7, 1), (13, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_929
  · decide +kernel

theorem prime_180569 : Nat.Prime 180569 := by
  apply nodeValid_prime [2, 22571] ⟨180569, 3, [(2, 3), (22571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22571
  · decide +kernel

theorem prime_181499 : Nat.Prime 181499 := by
  apply nodeValid_prime [2, 90749] ⟨181499, 2, [(2, 1), (90749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90749
  · decide +kernel

theorem prime_191519 : Nat.Prime 191519 := by
  apply nodeValid_prime [2, 31, 3089] ⟨191519, 11, [(2, 1), (31, 1), (3089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3089
  · decide +kernel

theorem prime_208739 : Nat.Prime 208739 := by
  apply nodeValid_prime [2, 104369] ⟨208739, 2, [(2, 1), (104369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_104369
  · decide +kernel

theorem prime_210233 : Nat.Prime 210233 := by
  apply nodeValid_prime [2, 11, 2389] ⟨210233, 3, [(2, 3), (11, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2389
  · decide +kernel

theorem prime_254179 : Nat.Prime 254179 := by
  apply nodeValid_prime [2, 3, 523] ⟨254179, 2, [(2, 1), (3, 5), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
  · decide +kernel

theorem prime_285937 : Nat.Prime 285937 := by
  apply nodeValid_prime [2, 3, 7, 23, 37] ⟨285937, 13, [(2, 4), (3, 1), (7, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_317959 : Nat.Prime 317959 := by
  apply nodeValid_prime [2, 3, 197, 269] ⟨317959, 3, [(2, 1), (3, 1), (197, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_269
  · decide +kernel

theorem prime_366721 : Nat.Prime 366721 := by
  apply nodeValid_prime [2, 3, 5, 191] ⟨366721, 7, [(2, 7), (3, 1), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_417479 : Nat.Prime 417479 := by
  apply nodeValid_prime [2, 208739] ⟨417479, 17, [(2, 1), (208739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_208739
  · decide +kernel

theorem prime_472457 : Nat.Prime 472457 := by
  apply nodeValid_prime [2, 73, 809] ⟨472457, 3, [(2, 3), (73, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_809
  · decide +kernel

theorem prime_542687 : Nat.Prime 542687 := by
  apply nodeValid_prime [2, 31, 8753] ⟨542687, 5, [(2, 1), (31, 1), (8753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_8753
  · decide +kernel

theorem prime_565441 : Nat.Prime 565441 := by
  apply nodeValid_prime [2, 3, 5, 19, 31] ⟨565441, 22, [(2, 6), (3, 1), (5, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_771937 : Nat.Prime 771937 := by
  apply nodeValid_prime [2, 3, 11, 17, 43] ⟨771937, 5, [(2, 5), (3, 1), (11, 1), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_775087 : Nat.Prime 775087 := by
  apply nodeValid_prime [2, 3, 13, 19, 523] ⟨775087, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_523
  · decide +kernel

theorem prime_853717 : Nat.Prime 853717 := by
  apply nodeValid_prime [2, 3, 71143] ⟨853717, 2, [(2, 2), (3, 1), (71143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71143
  · decide +kernel

theorem prime_985571 : Nat.Prime 985571 := by
  apply nodeValid_prime [2, 5, 67, 1471] ⟨985571, 2, [(2, 1), (5, 1), (67, 1), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_1471
  · decide +kernel

theorem prime_990503 : Nat.Prime 990503 := by
  apply nodeValid_prime [2, 79, 6269] ⟨990503, 5, [(2, 1), (79, 1), (6269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_6269
  · decide +kernel

theorem prime_1176701 : Nat.Prime 1176701 := by
  apply nodeValid_prime [2, 5, 7, 41] ⟨1176701, 3, [(2, 2), (5, 2), (7, 1), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_1221029 : Nat.Prime 1221029 := by
  apply nodeValid_prime [2, 31, 43, 229] ⟨1221029, 2, [(2, 2), (31, 1), (43, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_229
  · decide +kernel

theorem prime_1702553 : Nat.Prime 1702553 := by
  apply nodeValid_prime [2, 19, 23, 487] ⟨1702553, 3, [(2, 3), (19, 1), (23, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_487
  · decide +kernel

theorem prime_1971143 : Nat.Prime 1971143 := by
  apply nodeValid_prime [2, 985571] ⟨1971143, 5, [(2, 1), (985571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_985571
  · decide +kernel

theorem prime_2026751 : Nat.Prime 2026751 := by
  apply nodeValid_prime [2, 5, 11, 67] ⟨2026751, 11, [(2, 1), (5, 3), (11, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_3205261 : Nat.Prime 3205261 := by
  apply nodeValid_prime [2, 3, 5, 17807] ⟨3205261, 6, [(2, 2), (3, 2), (5, 1), (17807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17807
  · decide +kernel

theorem prime_3733133 : Nat.Prime 3733133 := by
  apply nodeValid_prime [2, 13, 17, 41, 103] ⟨3733133, 2, [(2, 2), (13, 1), (17, 1), (41, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_41
    · exact prime_103
  · decide +kernel

theorem prime_3942287 : Nat.Prime 3942287 := by
  apply nodeValid_prime [2, 1971143] ⟨3942287, 5, [(2, 1), (1971143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1971143
  · decide +kernel

theorem prime_5466059 : Nat.Prime 5466059 := by
  apply nodeValid_prime [2, 13, 210233] ⟨5466059, 2, [(2, 1), (13, 1), (210233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_210233
  · decide +kernel

theorem prime_5796251 : Nat.Prime 5796251 := by
  apply nodeValid_prime [2, 5, 4637] ⟨5796251, 2, [(2, 1), (5, 4), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4637
  · decide +kernel

theorem prime_5800237 : Nat.Prime 5800237 := by
  apply nodeValid_prime [2, 3, 13, 37181] ⟨5800237, 15, [(2, 2), (3, 1), (13, 1), (37181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37181
  · decide +kernel

theorem prime_5807969 : Nat.Prime 5807969 := by
  apply nodeValid_prime [2, 181499] ⟨5807969, 3, [(2, 5), (181499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_181499
  · decide +kernel

theorem prime_6230167 : Nat.Prime 6230167 := by
  apply nodeValid_prime [2, 3, 1019] ⟨6230167, 3, [(2, 1), (3, 1), (1019, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1019
  · decide +kernel

theorem prime_7514623 : Nat.Prime 7514623 := by
  apply nodeValid_prime [2, 3, 417479] ⟨7514623, 3, [(2, 1), (3, 2), (417479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_417479
  · decide +kernel

theorem prime_7537763 : Nat.Prime 7537763 := by
  apply nodeValid_prime [2, 227, 16603] ⟨7537763, 2, [(2, 1), (227, 1), (16603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_16603
  · decide +kernel

theorem prime_7578833 : Nat.Prime 7578833 := by
  apply nodeValid_prime [2, 181, 2617] ⟨7578833, 3, [(2, 4), (181, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_2617
  · decide +kernel

theorem prime_8159131 : Nat.Prime 8159131 := by
  apply nodeValid_prime [2, 3, 5, 7, 1439] ⟨8159131, 7, [(2, 1), (3, 4), (5, 1), (7, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1439
  · decide +kernel

theorem prime_8438201 : Nat.Prime 8438201 := by
  apply nodeValid_prime [2, 5, 31, 1361] ⟨8438201, 3, [(2, 3), (5, 2), (31, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1361
  · decide +kernel

theorem prime_12790889 : Nat.Prime 12790889 := by
  apply nodeValid_prime [2, 11, 191, 761] ⟨12790889, 3, [(2, 3), (11, 1), (191, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_191
    · exact prime_761
  · decide +kernel

theorem prime_14451341 : Nat.Prime 14451341 := by
  apply nodeValid_prime [2, 5, 71, 10177] ⟨14451341, 2, [(2, 2), (5, 1), (71, 1), (10177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_10177
  · decide +kernel

theorem prime_15075527 : Nat.Prime 15075527 := by
  apply nodeValid_prime [2, 7537763] ⟨15075527, 5, [(2, 1), (7537763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7537763
  · decide +kernel

theorem prime_15366907 : Nat.Prime 15366907 := by
  apply nodeValid_prime [2, 3, 853717] ⟨15366907, 2, [(2, 1), (3, 2), (853717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853717
  · decide +kernel

theorem prime_17548771 : Nat.Prime 17548771 := by
  apply nodeValid_prime [2, 3, 5, 23, 29, 877] ⟨17548771, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (29, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_29
    · exact prime_877
  · decide +kernel

theorem prime_18868471 : Nat.Prime 18868471 := by
  apply nodeValid_prime [2, 3, 5, 17, 36997] ⟨18868471, 12, [(2, 1), (3, 1), (5, 1), (17, 1), (36997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_36997
  · decide +kernel

theorem prime_22398799 : Nat.Prime 22398799 := by
  apply nodeValid_prime [2, 3, 3733133] ⟨22398799, 3, [(2, 1), (3, 1), (3733133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3733133
  · decide +kernel

theorem prime_25581779 : Nat.Prime 25581779 := by
  apply nodeValid_prime [2, 12790889] ⟨25581779, 2, [(2, 1), (12790889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12790889
  · decide +kernel

theorem prime_27717331 : Nat.Prime 27717331 := by
  apply nodeValid_prime [2, 3, 5, 29, 31859] ⟨27717331, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (31859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_31859
  · decide +kernel

theorem prime_33921427 : Nat.Prime 33921427 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 617] ⟨33921427, 2, [(2, 1), (3, 1), (7, 2), (11, 1), (17, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_617
  · decide +kernel

theorem prime_37434113 : Nat.Prime 37434113 := by
  apply nodeValid_prime [2, 31, 53, 89] ⟨37434113, 3, [(2, 8), (31, 1), (53, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_53
    · exact prime_89
  · decide +kernel

theorem prime_65679853 : Nat.Prime 65679853 := by
  apply nodeValid_prime [2, 3, 7, 73, 10711] ⟨65679853, 2, [(2, 2), (3, 1), (7, 1), (73, 1), (10711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_10711
  · decide +kernel

theorem prime_73210429 : Nat.Prime 73210429 := by
  apply nodeValid_prime [2, 3, 349, 5827] ⟨73210429, 6, [(2, 2), (3, 2), (349, 1), (5827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_5827
  · decide +kernel

theorem prime_97909573 : Nat.Prime 97909573 := by
  apply nodeValid_prime [2, 3, 8159131] ⟨97909573, 2, [(2, 2), (3, 1), (8159131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8159131
  · decide +kernel

theorem prime_109305491 : Nat.Prime 109305491 := by
  apply nodeValid_prime [2, 5, 7, 739, 2113] ⟨109305491, 2, [(2, 1), (5, 1), (7, 1), (739, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_739
    · exact prime_2113
  · decide +kernel

theorem prime_109892611 : Nat.Prime 109892611 := by
  apply nodeValid_prime [2, 3, 5, 1221029] ⟨109892611, 2, [(2, 1), (3, 2), (5, 1), (1221029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1221029
  · decide +kernel

theorem prime_135685709 : Nat.Prime 135685709 := by
  apply nodeValid_prime [2, 33921427] ⟨135685709, 2, [(2, 2), (33921427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33921427
  · decide +kernel

theorem prime_202932797 : Nat.Prime 202932797 := by
  apply nodeValid_prime [2, 11, 809, 5701] ⟨202932797, 2, [(2, 2), (11, 1), (809, 1), (5701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_809
    · exact prime_5701
  · decide +kernel

theorem prime_220768073 : Nat.Prime 220768073 := by
  apply nodeValid_prime [2, 7, 3942287] ⟨220768073, 3, [(2, 3), (7, 1), (3942287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3942287
  · decide +kernel

theorem prime_224144597 : Nat.Prime 224144597 := by
  apply nodeValid_prime [2, 13, 19, 29, 7823] ⟨224144597, 2, [(2, 2), (13, 1), (19, 1), (29, 1), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_29
    · exact prime_7823
  · decide +kernel

theorem prime_299131907 : Nat.Prime 299131907 := by
  apply nodeValid_prime [2, 151, 990503] ⟨299131907, 2, [(2, 1), (151, 1), (990503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_990503
  · decide +kernel

theorem prime_310536833 : Nat.Prime 310536833 := by
  apply nodeValid_prime [2, 1433, 1693] ⟨310536833, 3, [(2, 7), (1433, 1), (1693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1433
    · exact prime_1693
  · decide +kernel

theorem prime_350994781 : Nat.Prime 350994781 := by
  apply nodeValid_prime [2, 3, 5, 929, 2099] ⟨350994781, 6, [(2, 2), (3, 2), (5, 1), (929, 1), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_929
    · exact prime_2099
  · decide +kernel

theorem prime_391638293 : Nat.Prime 391638293 := by
  apply nodeValid_prime [2, 97909573] ⟨391638293, 2, [(2, 2), (97909573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_97909573
  · decide +kernel

theorem prime_511635581 : Nat.Prime 511635581 := by
  apply nodeValid_prime [2, 5, 25581779] ⟨511635581, 3, [(2, 2), (5, 1), (25581779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25581779
  · decide +kernel

theorem prime_656798531 : Nat.Prime 656798531 := by
  apply nodeValid_prime [2, 5, 65679853] ⟨656798531, 10, [(2, 1), (5, 1), (65679853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_65679853
  · decide +kernel

theorem prime_914412799 : Nat.Prime 914412799 := by
  apply nodeValid_prime [2, 3, 13, 59, 107, 619] ⟨914412799, 3, [(2, 1), (3, 2), (13, 1), (59, 1), (107, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_107
    · exact prime_619
  · decide +kernel

theorem prime_1220887099 : Nat.Prime 1220887099 := by
  apply nodeValid_prime [2, 3, 1217, 55733] ⟨1220887099, 2, [(2, 1), (3, 2), (1217, 1), (55733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1217
    · exact prime_55733
  · decide +kernel

theorem prime_2587076369 : Nat.Prime 2587076369 := by
  apply nodeValid_prime [2, 59, 61, 44927] ⟨2587076369, 3, [(2, 4), (59, 1), (61, 1), (44927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_61
    · exact prime_44927
  · decide +kernel

theorem prime_3895827163 : Nat.Prime 3895827163 := by
  apply nodeValid_prime [2, 3, 37, 17548771] ⟨3895827163, 2, [(2, 1), (3, 1), (37, 1), (17548771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_17548771
  · decide +kernel

theorem prime_10378414931 : Nat.Prime 10378414931 := by
  apply nodeValid_prime [2, 5, 13, 103, 775087] ⟨10378414931, 2, [(2, 1), (5, 1), (13, 1), (103, 1), (775087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_103
    · exact prime_775087
  · decide +kernel

theorem prime_11024463077 : Nat.Prime 11024463077 := by
  apply nodeValid_prime [2, 11, 17, 139, 106033] ⟨11024463077, 3, [(2, 2), (11, 1), (17, 1), (139, 1), (106033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_139
    · exact prime_106033
  · decide +kernel

theorem prime_14080404167 : Nat.Prime 14080404167 := by
  apply nodeValid_prime [2, 31, 193, 1176701] ⟨14080404167, 7, [(2, 1), (31, 1), (193, 1), (1176701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_193
    · exact prime_1176701
  · decide +kernel

theorem prime_21365524933 : Nat.Prime 21365524933 := by
  apply nodeValid_prime [2, 3, 211, 8438201] ⟨21365524933, 2, [(2, 2), (3, 1), (211, 1), (8438201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_8438201
  · decide +kernel

theorem prime_42363329363 : Nat.Prime 42363329363 := by
  apply nodeValid_prime [2, 107, 419, 472457] ⟨42363329363, 2, [(2, 1), (107, 1), (419, 1), (472457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_419
    · exact prime_472457
  · decide +kernel

theorem prime_82546057261 : Nat.Prime 82546057261 := by
  apply nodeValid_prime [2, 3, 5, 773, 197753] ⟨82546057261, 2, [(2, 2), (3, 3), (5, 1), (773, 1), (197753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_773
    · exact prime_197753
  · decide +kernel

theorem prime_82546058591 : Nat.Prime 82546058591 := by
  apply nodeValid_prime [2, 5, 48821, 169079] ⟨82546058591, 17, [(2, 1), (5, 1), (48821, 1), (169079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_48821
    · exact prime_169079
  · decide +kernel

theorem prime_82546059137 : Nat.Prime 82546059137 := by
  apply nodeValid_prime [2, 6977, 92431] ⟨82546059137, 3, [(2, 7), (6977, 1), (92431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6977
    · exact prime_92431
  · decide +kernel

theorem prime_82786443809 : Nat.Prime 82786443809 := by
  apply nodeValid_prime [2, 2587076369] ⟨82786443809, 3, [(2, 5), (2587076369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2587076369
  · decide +kernel

theorem prime_82786458673 : Nat.Prime 82786458673 := by
  apply nodeValid_prime [2, 3, 37, 1171, 4423] ⟨82786458673, 5, [(2, 4), (3, 3), (37, 1), (1171, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1171
    · exact prime_4423
  · decide +kernel

theorem prime_82786459097 : Nat.Prime 82786459097 := by
  apply nodeValid_prime [2, 11, 151, 6230167] ⟨82786459097, 3, [(2, 3), (11, 1), (151, 1), (6230167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_151
    · exact prime_6230167
  · decide +kernel

theorem prime_83027301913 : Nat.Prime 83027301913 := by
  apply nodeValid_prime [2, 3, 17, 2111, 10711] ⟨83027301913, 5, [(2, 3), (3, 3), (17, 1), (2111, 1), (10711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2111
    · exact prime_10711
  · decide +kernel

theorem prime_83027318117 : Nat.Prime 83027318117 := by
  apply nodeValid_prime [2, 53, 391638293] ⟨83027318117, 2, [(2, 2), (53, 1), (391638293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_391638293
  · decide +kernel

theorem prime_83027319449 : Nat.Prime 83027319449 := by
  apply nodeValid_prime [2, 10378414931] ⟨83027319449, 3, [(2, 3), (10378414931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10378414931
  · decide +kernel

theorem prime_83268626843 : Nat.Prime 83268626843 := by
  apply nodeValid_prime [2, 43, 67, 14451341] ⟨83268626843, 2, [(2, 1), (43, 1), (67, 1), (14451341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_67
    · exact prime_14451341
  · decide +kernel

theorem prime_83268626921 : Nat.Prime 83268626921 := by
  apply nodeValid_prime [2, 5, 41, 6733, 7541] ⟨83268626921, 6, [(2, 3), (5, 1), (41, 1), (6733, 1), (7541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_6733
    · exact prime_7541
  · decide +kernel

theorem prime_83268634861 : Nat.Prime 83268634861 := by
  apply nodeValid_prime [2, 3, 5, 167, 227, 12203] ⟨83268634861, 10, [(2, 2), (3, 2), (5, 1), (167, 1), (227, 1), (12203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_227
    · exact prime_12203
  · decide +kernel

theorem prime_83510443957 : Nat.Prime 83510443957 := by
  apply nodeValid_prime [2, 3, 19, 71, 163, 31649] ⟨83510443957, 2, [(2, 2), (3, 1), (19, 1), (71, 1), (163, 1), (31649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_71
    · exact prime_163
    · exact prime_31649
  · decide +kernel

theorem prime_83510449403 : Nat.Prime 83510449403 := by
  apply nodeValid_prime [2, 7639, 5466059] ⟨83510449403, 2, [(2, 1), (7639, 1), (5466059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7639
    · exact prime_5466059
  · decide +kernel

theorem prime_83510450479 : Nat.Prime 83510450479 := by
  apply nodeValid_prime [2, 3, 7, 13, 67, 149, 5107] ⟨83510450479, 3, [(2, 1), (3, 2), (7, 1), (13, 1), (67, 1), (149, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_67
    · exact prime_149
    · exact prime_5107
  · decide +kernel

theorem prime_83752729813 : Nat.Prime 83752729813 := by
  apply nodeValid_prime [2, 3, 89, 109, 79939] ⟨83752729813, 6, [(2, 2), (3, 3), (89, 1), (109, 1), (79939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_109
    · exact prime_79939
  · decide +kernel

theorem prime_83752730777 : Nat.Prime 83752730777 := by
  apply nodeValid_prime [2, 11, 13, 73210429] ⟨83752730777, 3, [(2, 3), (11, 1), (13, 1), (73210429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_73210429
  · decide +kernel

theorem prime_83752730819 : Nat.Prime 83752730819 := by
  apply nodeValid_prime [2, 43, 83, 719, 16319] ⟨83752730819, 2, [(2, 1), (43, 1), (83, 1), (719, 1), (16319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_83
    · exact prime_719
    · exact prime_16319
  · decide +kernel

theorem prime_83995496251 : Nat.Prime 83995496251 := by
  apply nodeValid_prime [2, 3, 5, 22398799] ⟨83995496251, 2, [(2, 1), (3, 1), (5, 4), (22398799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22398799
  · decide +kernel

theorem prime_83995513663 : Nat.Prime 83995513663 := by
  apply nodeValid_prime [2, 3, 911, 15366907] ⟨83995513663, 6, [(2, 1), (3, 1), (911, 1), (15366907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_911
    · exact prime_15366907
  · decide +kernel

theorem prime_83995513909 : Nat.Prime 83995513909 := by
  apply nodeValid_prime [2, 3, 44201, 158359] ⟨83995513909, 2, [(2, 2), (3, 1), (44201, 1), (158359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44201
    · exact prime_158359
  · decide +kernel

theorem prime_84238739329 : Nat.Prime 84238739329 := by
  apply nodeValid_prime [2, 3, 31, 53, 133519] ⟨84238739329, 7, [(2, 7), (3, 1), (31, 1), (53, 1), (133519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
    · exact prime_133519
  · decide +kernel

theorem prime_84238747441 : Nat.Prime 84238747441 := by
  apply nodeValid_prime [2, 3, 5, 350994781] ⟨84238747441, 17, [(2, 4), (3, 1), (5, 1), (350994781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_350994781
  · decide +kernel

theorem prime_84238747469 : Nat.Prime 84238747469 := by
  apply nodeValid_prime [2, 57427, 366721] ⟨84238747469, 2, [(2, 2), (57427, 1), (366721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_57427
    · exact prime_366721
  · decide +kernel

theorem prime_84482424889 : Nat.Prime 84482424889 := by
  apply nodeValid_prime [2, 3, 127, 27717331] ⟨84482424889, 13, [(2, 3), (3, 1), (127, 1), (27717331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_27717331
  · decide +kernel

theorem prime_84482425003 : Nat.Prime 84482425003 := by
  apply nodeValid_prime [2, 3, 14080404167] ⟨84482425003, 3, [(2, 1), (3, 1), (14080404167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14080404167
  · decide +kernel

theorem prime_84482456893 : Nat.Prime 84482456893 := by
  apply nodeValid_prime [2, 3, 127, 307, 180569] ⟨84482456893, 2, [(2, 2), (3, 1), (127, 1), (307, 1), (180569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_307
    · exact prime_180569
  · decide +kernel

theorem prime_84726651773 : Nat.Prime 84726651773 := by
  apply nodeValid_prime [2, 7, 521, 5807969] ⟨84726651773, 2, [(2, 2), (7, 1), (521, 1), (5807969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_521
    · exact prime_5807969
  · decide +kernel

theorem prime_84726657667 : Nat.Prime 84726657667 := by
  apply nodeValid_prime [2, 3, 7, 224144597] ⟨84726657667, 7, [(2, 1), (3, 3), (7, 1), (224144597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_224144597
  · decide +kernel

theorem prime_84726658727 : Nat.Prime 84726658727 := by
  apply nodeValid_prime [2, 42363329363] ⟨84726658727, 5, [(2, 1), (42363329363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42363329363
  · decide +kernel

theorem prime_84971326417 : Nat.Prime 84971326417 := by
  apply nodeValid_prime [2, 3, 41, 151, 285937] ⟨84971326417, 10, [(2, 4), (3, 1), (41, 1), (151, 1), (285937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_151
    · exact prime_285937
  · decide +kernel

theorem prime_84971357579 : Nat.Prime 84971357579 := by
  apply nodeValid_prime [2, 587, 1609, 44983] ⟨84971357579, 2, [(2, 1), (587, 1), (1609, 1), (44983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_587
    · exact prime_1609
    · exact prime_44983
  · decide +kernel

theorem prime_84971358187 : Nat.Prime 84971358187 := by
  apply nodeValid_prime [2, 3, 11, 13, 29, 47, 113, 643] ⟨84971358187, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (29, 1), (47, 1), (113, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_29
    · exact prime_47
    · exact prime_113
    · exact prime_643
  · decide +kernel

theorem prime_85216476179 : Nat.Prime 85216476179 := by
  apply nodeValid_prime [2, 193, 220768073] ⟨85216476179, 2, [(2, 1), (193, 1), (220768073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_220768073
  · decide +kernel

theorem prime_85216482203 : Nat.Prime 85216482203 := by
  apply nodeValid_prime [2, 7351, 5796251] ⟨85216482203, 2, [(2, 1), (7351, 1), (5796251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7351
    · exact prime_5796251
  · decide +kernel

theorem prime_85216482229 : Nat.Prime 85216482229 := by
  apply nodeValid_prime [2, 3, 19, 661, 565441] ⟨85216482229, 11, [(2, 2), (3, 1), (19, 1), (661, 1), (565441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_661
    · exact prime_565441
  · decide +kernel

theorem prime_85462096813 : Nat.Prime 85462096813 := by
  apply nodeValid_prime [2, 3, 28019, 254179] ⟨85462096813, 2, [(2, 2), (3, 1), (28019, 1), (254179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28019
    · exact prime_254179
  · decide +kernel

theorem prime_85462096931 : Nat.Prime 85462096931 := by
  apply nodeValid_prime [2, 5, 7, 1220887099] ⟨85462096931, 2, [(2, 1), (5, 1), (7, 1), (1220887099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1220887099
  · decide +kernel

theorem prime_85462099733 : Nat.Prime 85462099733 := by
  apply nodeValid_prime [2, 21365524933] ⟨85462099733, 2, [(2, 2), (21365524933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21365524933
  · decide +kernel

theorem prime_85708165111 : Nat.Prime 85708165111 := by
  apply nodeValid_prime [2, 3, 5, 3701, 771937] ⟨85708165111, 3, [(2, 1), (3, 1), (5, 1), (3701, 1), (771937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3701
    · exact prime_771937
  · decide +kernel

theorem prime_85708165909 : Nat.Prime 85708165909 := by
  apply nodeValid_prime [2, 3, 23, 310536833] ⟨85708165909, 2, [(2, 2), (3, 1), (23, 1), (310536833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_310536833
  · decide +kernel

theorem prime_85708197587 : Nat.Prime 85708197587 := by
  apply nodeValid_prime [2, 11, 3895827163] ⟨85708197587, 2, [(2, 1), (11, 1), (3895827163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3895827163
  · decide +kernel

theorem prime_85954777609 : Nat.Prime 85954777609 := by
  apply nodeValid_prime [2, 3, 7, 511635581] ⟨85954777609, 11, [(2, 3), (3, 1), (7, 1), (511635581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_511635581
  · decide +kernel

theorem prime_85954803107 : Nat.Prime 85954803107 := by
  apply nodeValid_prime [2, 47, 914412799] ⟨85954803107, 2, [(2, 1), (47, 1), (914412799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_914412799
  · decide +kernel

theorem prime_85954803499 : Nat.Prime 85954803499 := by
  apply nodeValid_prime [2, 3, 359, 3067, 4337] ⟨85954803499, 13, [(2, 1), (3, 2), (359, 1), (3067, 1), (4337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_3067
    · exact prime_4337
  · decide +kernel

theorem prime_86201836663 : Nat.Prime 86201836663 := by
  apply nodeValid_prime [2, 3, 281, 5387, 9491] ⟨86201836663, 5, [(2, 1), (3, 1), (281, 1), (5387, 1), (9491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_5387
    · exact prime_9491
  · decide +kernel

theorem prime_86201863387 : Nat.Prime 86201863387 := by
  apply nodeValid_prime [2, 3, 953, 15075527] ⟨86201863387, 3, [(2, 1), (3, 1), (953, 1), (15075527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_953
    · exact prime_15075527
  · decide +kernel

theorem prime_86201864491 : Nat.Prime 86201864491 := by
  apply nodeValid_prime [2, 3, 5, 7, 1291, 317959] ⟨86201864491, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (1291, 1), (317959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1291
    · exact prime_317959
  · decide +kernel

theorem prime_86449371523 : Nat.Prime 86449371523 := by
  apply nodeValid_prime [2, 3, 71, 202932797] ⟨86449371523, 3, [(2, 1), (3, 1), (71, 1), (202932797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_202932797
  · decide +kernel

theorem prime_86449371661 : Nat.Prime 86449371661 := by
  apply nodeValid_prime [2, 3, 5, 41, 53, 73673] ⟨86449371661, 6, [(2, 2), (3, 3), (5, 1), (41, 1), (53, 1), (73673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_53
    · exact prime_73673
  · decide +kernel

theorem prime_86449378373 : Nat.Prime 86449378373 := by
  apply nodeValid_prime [2, 7, 47, 191519] ⟨86449378373, 2, [(2, 2), (7, 4), (47, 1), (191519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_191519
  · decide +kernel

theorem prime_86697403867 : Nat.Prime 86697403867 := by
  apply nodeValid_prime [2, 3, 23, 41, 1702553] ⟨86697403867, 5, [(2, 1), (3, 3), (23, 1), (41, 1), (1702553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_1702553
  · decide +kernel

theorem prime_86697405709 : Nat.Prime 86697405709 := by
  apply nodeValid_prime [2, 3, 193, 37434113] ⟨86697405709, 2, [(2, 2), (3, 1), (193, 1), (37434113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_37434113
  · decide +kernel

theorem prime_86697406093 : Nat.Prime 86697406093 := by
  apply nodeValid_prime [2, 3, 11, 656798531] ⟨86697406093, 2, [(2, 2), (3, 1), (11, 1), (656798531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_656798531
  · decide +kernel

theorem prime_86945909887 : Nat.Prime 86945909887 := by
  apply nodeValid_prime [2, 3, 11, 137, 3205261] ⟨86945909887, 11, [(2, 1), (3, 2), (11, 1), (137, 1), (3205261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
    · exact prime_3205261
  · decide +kernel

theorem prime_86945914369 : Nat.Prime 86945914369 := by
  apply nodeValid_prime [2, 3, 18868471] ⟨86945914369, 7, [(2, 9), (3, 2), (18868471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18868471
  · decide +kernel

theorem prime_86945914873 : Nat.Prime 86945914873 := by
  apply nodeValid_prime [2, 3, 179, 647, 10427] ⟨86945914873, 5, [(2, 3), (3, 2), (179, 1), (647, 1), (10427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_647
    · exact prime_10427
  · decide +kernel

theorem prime_87194881523 : Nat.Prime 87194881523 := by
  apply nodeValid_prime [2, 7, 439, 2026751] ⟨87194881523, 2, [(2, 1), (7, 2), (439, 1), (2026751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_439
    · exact prime_2026751
  · decide +kernel

theorem prime_87194896783 : Nat.Prime 87194896783 := by
  apply nodeValid_prime [2, 3, 7, 13187, 157433] ⟨87194896783, 3, [(2, 1), (3, 1), (7, 1), (13187, 1), (157433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13187
    · exact prime_157433
  · decide +kernel

theorem prime_87444373013 : Nat.Prime 87444373013 := by
  apply nodeValid_prime [2, 3769, 5800237] ⟨87444373013, 2, [(2, 2), (3769, 1), (5800237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3769
    · exact prime_5800237
  · decide +kernel

theorem prime_87444392801 : Nat.Prime 87444392801 := by
  apply nodeValid_prime [2, 5, 109305491] ⟨87444392801, 6, [(2, 5), (5, 2), (109305491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109305491
  · decide +kernel

theorem prime_87444393781 : Nat.Prime 87444393781 := by
  apply nodeValid_prime [2, 3, 5, 71, 313, 65581] ⟨87444393781, 6, [(2, 2), (3, 1), (5, 1), (71, 1), (313, 1), (65581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_313
    · exact prime_65581
  · decide +kernel

theorem prime_87694303321 : Nat.Prime 87694303321 := by
  apply nodeValid_prime [2, 3, 5, 13, 419, 4969] ⟨87694303321, 34, [(2, 3), (3, 4), (5, 1), (13, 1), (419, 1), (4969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_419
    · exact prime_4969
  · decide +kernel

theorem prime_87694303579 : Nat.Prime 87694303579 := by
  apply nodeValid_prime [2, 3, 7, 19, 109892611] ⟨87694303579, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (109892611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_109892611
  · decide +kernel

theorem prime_87694333817 : Nat.Prime 87694333817 := by
  apply nodeValid_prime [2, 43, 53, 251, 19163] ⟨87694333817, 3, [(2, 3), (43, 1), (53, 1), (251, 1), (19163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_53
    · exact prime_251
    · exact prime_19163
  · decide +kernel

theorem prime_87944778133 : Nat.Prime 87944778133 := by
  apply nodeValid_prime [2, 3, 967, 7578833] ⟨87944778133, 5, [(2, 2), (3, 1), (967, 1), (7578833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
    · exact prime_7578833
  · decide +kernel

theorem prime_87944780659 : Nat.Prime 87944780659 := by
  apply nodeValid_prime [2, 3, 7, 299131907] ⟨87944780659, 7, [(2, 1), (3, 1), (7, 2), (299131907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_299131907
  · decide +kernel

theorem prime_88195704617 : Nat.Prime 88195704617 := by
  apply nodeValid_prime [2, 11024463077] ⟨88195704617, 3, [(2, 3), (11024463077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11024463077
  · decide +kernel

theorem prime_88195710527 : Nat.Prime 88195710527 := by
  apply nodeValid_prime [2, 7, 11, 71, 83, 157, 619] ⟨88195710527, 5, [(2, 1), (7, 1), (11, 1), (71, 1), (83, 1), (157, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_71
    · exact prime_83
    · exact prime_157
    · exact prime_619
  · decide +kernel

theorem prime_88195710851 : Nat.Prime 88195710851 := by
  apply nodeValid_prime [2, 5, 13, 135685709] ⟨88195710851, 6, [(2, 1), (5, 2), (13, 1), (135685709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_135685709
  · decide +kernel

theorem prime_88447112711 : Nat.Prime 88447112711 := by
  apply nodeValid_prime [2, 5, 11, 107, 7514623] ⟨88447112711, 11, [(2, 1), (5, 1), (11, 1), (107, 1), (7514623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_107
    · exact prime_7514623
  · decide +kernel

theorem prime_88447127051 : Nat.Prime 88447127051 := by
  apply nodeValid_prime [2, 5, 19, 1277, 72907] ⟨88447127051, 2, [(2, 1), (5, 2), (19, 1), (1277, 1), (72907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1277
    · exact prime_72907
  · decide +kernel

theorem prime_88447127261 : Nat.Prime 88447127261 := by
  apply nodeValid_prime [2, 5, 29, 281, 542687] ⟨88447127261, 2, [(2, 2), (5, 1), (29, 1), (281, 1), (542687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_281
    · exact prime_542687
  · decide +kernel

end Sude.Lucas.Generated
