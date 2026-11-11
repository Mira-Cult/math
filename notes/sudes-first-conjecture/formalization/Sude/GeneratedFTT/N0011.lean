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

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1289 : Nat.Prime 1289 := by
  apply nodeValid_prime [2, 7, 23] ⟨1289, 6, [(2, 3), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_1499 : Nat.Prime 1499 := by
  apply nodeValid_prime [2, 7, 107] ⟨1499, 2, [(2, 1), (7, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
  · decide +kernel

theorem prime_1583 : Nat.Prime 1583 := by
  apply nodeValid_prime [2, 7, 113] ⟨1583, 5, [(2, 1), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_1621 : Nat.Prime 1621 := by
  apply nodeValid_prime [2, 3, 5] ⟨1621, 2, [(2, 2), (3, 4), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_2141 : Nat.Prime 2141 := by
  apply nodeValid_prime [2, 5, 107] ⟨2141, 2, [(2, 2), (5, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_2729 : Nat.Prime 2729 := by
  apply nodeValid_prime [2, 11, 31] ⟨2729, 3, [(2, 3), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_2803 : Nat.Prime 2803 := by
  apply nodeValid_prime [2, 3, 467] ⟨2803, 2, [(2, 1), (3, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
  · decide +kernel

theorem prime_2819 : Nat.Prime 2819 := by
  apply nodeValid_prime [2, 1409] ⟨2819, 2, [(2, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1409
  · decide +kernel

theorem prime_2999 : Nat.Prime 2999 := by
  apply nodeValid_prime [2, 1499] ⟨2999, 17, [(2, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1499
  · decide +kernel

theorem prime_3167 : Nat.Prime 3167 := by
  apply nodeValid_prime [2, 1583] ⟨3167, 5, [(2, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1583
  · decide +kernel

theorem prime_3331 : Nat.Prime 3331 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨3331, 3, [(2, 1), (3, 2), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_3761 : Nat.Prime 3761 := by
  apply nodeValid_prime [2, 5, 47] ⟨3761, 3, [(2, 4), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_4391 : Nat.Prime 4391 := by
  apply nodeValid_prime [2, 5, 439] ⟨4391, 14, [(2, 1), (5, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_4721 : Nat.Prime 4721 := by
  apply nodeValid_prime [2, 5, 59] ⟨4721, 6, [(2, 4), (5, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_6689 : Nat.Prime 6689 := by
  apply nodeValid_prime [2, 11, 19] ⟨6689, 3, [(2, 5), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_7069 : Nat.Prime 7069 := by
  apply nodeValid_prime [2, 3, 19, 31] ⟨7069, 2, [(2, 2), (3, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_7523 : Nat.Prime 7523 := by
  apply nodeValid_prime [2, 3761] ⟨7523, 2, [(2, 1), (3761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3761
  · decide +kernel

theorem prime_8467 : Nat.Prime 8467 := by
  apply nodeValid_prime [2, 3, 17, 83] ⟨8467, 2, [(2, 1), (3, 1), (17, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_83
  · decide +kernel

theorem prime_8783 : Nat.Prime 8783 := by
  apply nodeValid_prime [2, 4391] ⟨8783, 5, [(2, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4391
  · decide +kernel

theorem prime_8839 : Nat.Prime 8839 := by
  apply nodeValid_prime [2, 3, 491] ⟨8839, 3, [(2, 1), (3, 2), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_491
  · decide +kernel

theorem prime_8999 : Nat.Prime 8999 := by
  apply nodeValid_prime [2, 11, 409] ⟨8999, 7, [(2, 1), (11, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_409
  · decide +kernel

theorem prime_9511 : Nat.Prime 9511 := by
  apply nodeValid_prime [2, 3, 5, 317] ⟨9511, 3, [(2, 1), (3, 1), (5, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_317
  · decide +kernel

theorem prime_12653 : Nat.Prime 12653 := by
  apply nodeValid_prime [2, 3163] ⟨12653, 2, [(2, 2), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3163
  · decide +kernel

theorem prime_13691 : Nat.Prime 13691 := by
  apply nodeValid_prime [2, 5, 37] ⟨13691, 2, [(2, 1), (5, 1), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_16361 : Nat.Prime 16361 := by
  apply nodeValid_prime [2, 5, 409] ⟨16361, 3, [(2, 3), (5, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
  · decide +kernel

theorem prime_16433 : Nat.Prime 16433 := by
  apply nodeValid_prime [2, 13, 79] ⟨16433, 3, [(2, 4), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_17431 : Nat.Prime 17431 := by
  apply nodeValid_prime [2, 3, 5, 7, 83] ⟨17431, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_20149 : Nat.Prime 20149 := by
  apply nodeValid_prime [2, 3, 23, 73] ⟨20149, 2, [(2, 2), (3, 1), (23, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_73
  · decide +kernel

theorem prime_21143 : Nat.Prime 21143 := by
  apply nodeValid_prime [2, 11, 31] ⟨21143, 10, [(2, 1), (11, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_21247 : Nat.Prime 21247 := by
  apply nodeValid_prime [2, 3, 3541] ⟨21247, 3, [(2, 1), (3, 1), (3541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3541
  · decide +kernel

theorem prime_21649 : Nat.Prime 21649 := by
  apply nodeValid_prime [2, 3, 11, 41] ⟨21649, 14, [(2, 4), (3, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_22751 : Nat.Prime 22751 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨22751, 21, [(2, 1), (5, 3), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_23369 : Nat.Prime 23369 := by
  apply nodeValid_prime [2, 23, 127] ⟨23369, 3, [(2, 3), (23, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_127
  · decide +kernel

theorem prime_24481 : Nat.Prime 24481 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨24481, 11, [(2, 5), (3, 2), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_28277 : Nat.Prime 28277 := by
  apply nodeValid_prime [2, 7069] ⟨28277, 2, [(2, 2), (7069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7069
  · decide +kernel

theorem prime_29179 : Nat.Prime 29179 := by
  apply nodeValid_prime [2, 3, 1621] ⟨29179, 13, [(2, 1), (3, 2), (1621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1621
  · decide +kernel

theorem prime_32647 : Nat.Prime 32647 := by
  apply nodeValid_prime [2, 3, 5441] ⟨32647, 3, [(2, 1), (3, 1), (5441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5441
  · decide +kernel

theorem prime_33311 : Nat.Prime 33311 := by
  apply nodeValid_prime [2, 5, 3331] ⟨33311, 11, [(2, 1), (5, 1), (3331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3331
  · decide +kernel

theorem prime_36161 : Nat.Prime 36161 := by
  apply nodeValid_prime [2, 5, 113] ⟨36161, 3, [(2, 6), (5, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_40163 : Nat.Prime 40163 := by
  apply nodeValid_prime [2, 43, 467] ⟨40163, 2, [(2, 1), (43, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_467
  · decide +kernel

theorem prime_40427 : Nat.Prime 40427 := by
  apply nodeValid_prime [2, 17, 29, 41] ⟨40427, 2, [(2, 1), (17, 1), (29, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_41
  · decide +kernel

theorem prime_42437 : Nat.Prime 42437 := by
  apply nodeValid_prime [2, 103] ⟨42437, 2, [(2, 2), (103, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_103
  · decide +kernel

theorem prime_42571 : Nat.Prime 42571 := by
  apply nodeValid_prime [2, 3, 5, 11, 43] ⟨42571, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_42797 : Nat.Prime 42797 := by
  apply nodeValid_prime [2, 13, 823] ⟨42797, 2, [(2, 2), (13, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_823
  · decide +kernel

theorem prime_56773 : Nat.Prime 56773 := by
  apply nodeValid_prime [2, 3, 19, 83] ⟨56773, 2, [(2, 2), (3, 2), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_62191 : Nat.Prime 62191 := by
  apply nodeValid_prime [2, 3, 5, 691] ⟨62191, 3, [(2, 1), (3, 2), (5, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_691
  · decide +kernel

theorem prime_63463 : Nat.Prime 63463 := by
  apply nodeValid_prime [2, 3, 7, 1511] ⟨63463, 5, [(2, 1), (3, 1), (7, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1511
  · decide +kernel

theorem prime_72031 : Nat.Prime 72031 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨72031, 3, [(2, 1), (3, 1), (5, 1), (7, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_73291 : Nat.Prime 73291 := by
  apply nodeValid_prime [2, 3, 5, 7, 349] ⟨73291, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_349
  · decide +kernel

theorem prime_80231 : Nat.Prime 80231 := by
  apply nodeValid_prime [2, 5, 71, 113] ⟨80231, 7, [(2, 1), (5, 1), (71, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_113
  · decide +kernel

theorem prime_101797 : Nat.Prime 101797 := by
  apply nodeValid_prime [2, 3, 17, 499] ⟨101797, 2, [(2, 2), (3, 1), (17, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_499
  · decide +kernel

theorem prime_108967 : Nat.Prime 108967 := by
  apply nodeValid_prime [2, 3, 11, 13, 127] ⟨108967, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_114967 : Nat.Prime 114967 := by
  apply nodeValid_prime [2, 3, 2129] ⟨114967, 3, [(2, 1), (3, 3), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2129
  · decide +kernel

theorem prime_124823 : Nat.Prime 124823 := by
  apply nodeValid_prime [2, 139, 449] ⟨124823, 5, [(2, 1), (139, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_449
  · decide +kernel

theorem prime_131413 : Nat.Prime 131413 := by
  apply nodeValid_prime [2, 3, 47, 233] ⟨131413, 2, [(2, 2), (3, 1), (47, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_233
  · decide +kernel

theorem prime_156253 : Nat.Prime 156253 := by
  apply nodeValid_prime [2, 3, 29, 449] ⟨156253, 2, [(2, 2), (3, 1), (29, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_449
  · decide +kernel

theorem prime_200671 : Nat.Prime 200671 := by
  apply nodeValid_prime [2, 3, 5, 6689] ⟨200671, 3, [(2, 1), (3, 1), (5, 1), (6689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6689
  · decide +kernel

theorem prime_203209 : Nat.Prime 203209 := by
  apply nodeValid_prime [2, 3, 8467] ⟨203209, 7, [(2, 3), (3, 1), (8467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8467
  · decide +kernel

theorem prime_229837 : Nat.Prime 229837 := by
  apply nodeValid_prime [2, 3, 107, 179] ⟨229837, 7, [(2, 2), (3, 1), (107, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_179
  · decide +kernel

theorem prime_234167 : Nat.Prime 234167 := by
  apply nodeValid_prime [2, 191, 613] ⟨234167, 5, [(2, 1), (191, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_613
  · decide +kernel

theorem prime_261061 : Nat.Prime 261061 := by
  apply nodeValid_prime [2, 3, 5, 19, 229] ⟨261061, 10, [(2, 2), (3, 1), (5, 1), (19, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_229
  · decide +kernel

theorem prime_276671 : Nat.Prime 276671 := by
  apply nodeValid_prime [2, 5, 73, 379] ⟨276671, 23, [(2, 1), (5, 1), (73, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_379
  · decide +kernel

theorem prime_291857 : Nat.Prime 291857 := by
  apply nodeValid_prime [2, 17, 29, 37] ⟨291857, 3, [(2, 4), (17, 1), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_343823 : Nat.Prime 343823 := by
  apply nodeValid_prime [2, 353, 487] ⟨343823, 5, [(2, 1), (353, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_487
  · decide +kernel

theorem prime_519577 : Nat.Prime 519577 := by
  apply nodeValid_prime [2, 3, 21649] ⟨519577, 10, [(2, 3), (3, 1), (21649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21649
  · decide +kernel

theorem prime_583337 : Nat.Prime 583337 := by
  apply nodeValid_prime [2, 13, 71, 79] ⟨583337, 3, [(2, 3), (13, 1), (71, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71
    · exact prime_79
  · decide +kernel

theorem prime_625657 : Nat.Prime 625657 := by
  apply nodeValid_prime [2, 3, 131, 199] ⟨625657, 5, [(2, 3), (3, 1), (131, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_199
  · decide +kernel

theorem prime_665857 : Nat.Prime 665857 := by
  apply nodeValid_prime [2, 3, 17] ⟨665857, 5, [(2, 8), (3, 2), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_697643 : Nat.Prime 697643 := by
  apply nodeValid_prime [2, 11, 19, 1669] ⟨697643, 2, [(2, 1), (11, 1), (19, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1669
  · decide +kernel

theorem prime_723221 : Nat.Prime 723221 := by
  apply nodeValid_prime [2, 5, 36161] ⟨723221, 2, [(2, 2), (5, 1), (36161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_36161
  · decide +kernel

theorem prime_748717 : Nat.Prime 748717 := by
  apply nodeValid_prime [2, 3, 43, 1451] ⟨748717, 2, [(2, 2), (3, 1), (43, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1451
  · decide +kernel

theorem prime_765227 : Nat.Prime 765227 := by
  apply nodeValid_prime [2, 7, 11, 4969] ⟨765227, 5, [(2, 1), (7, 1), (11, 1), (4969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_4969
  · decide +kernel

theorem prime_788479 : Nat.Prime 788479 := by
  apply nodeValid_prime [2, 3, 131413] ⟨788479, 3, [(2, 1), (3, 1), (131413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131413
  · decide +kernel

theorem prime_1012241 : Nat.Prime 1012241 := by
  apply nodeValid_prime [2, 5, 12653] ⟨1012241, 3, [(2, 4), (5, 1), (12653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12653
  · decide +kernel

theorem prime_1014631 : Nat.Prime 1014631 := by
  apply nodeValid_prime [2, 3, 5, 31, 1091] ⟨1014631, 6, [(2, 1), (3, 1), (5, 1), (31, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1091
  · decide +kernel

theorem prime_1027129 : Nat.Prime 1027129 := by
  apply nodeValid_prime [2, 3, 42797] ⟨1027129, 7, [(2, 3), (3, 1), (42797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42797
  · decide +kernel

theorem prime_1226867 : Nat.Prime 1226867 := by
  apply nodeValid_prime [2, 23, 149, 179] ⟨1226867, 2, [(2, 1), (23, 1), (149, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_149
    · exact prime_179
  · decide +kernel

theorem prime_1351981 : Nat.Prime 1351981 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 37] ⟨1351981, 6, [(2, 2), (3, 2), (5, 1), (7, 1), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_1496797 : Nat.Prime 1496797 := by
  apply nodeValid_prime [2, 3, 7, 103, 173] ⟨1496797, 2, [(2, 2), (3, 1), (7, 1), (103, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_173
  · decide +kernel

theorem prime_1603517 : Nat.Prime 1603517 := by
  apply nodeValid_prime [2, 311, 1289] ⟨1603517, 2, [(2, 2), (311, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_1289
  · decide +kernel

theorem prime_1604621 : Nat.Prime 1604621 := by
  apply nodeValid_prime [2, 5, 80231] ⟨1604621, 2, [(2, 2), (5, 1), (80231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_80231
  · decide +kernel

theorem prime_1616519 : Nat.Prime 1616519 := by
  apply nodeValid_prime [2, 29, 47, 593] ⟨1616519, 7, [(2, 1), (29, 1), (47, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_47
    · exact prime_593
  · decide +kernel

theorem prime_5505743 : Nat.Prime 5505743 := by
  apply nodeValid_prime [2, 11, 22751] ⟨5505743, 5, [(2, 1), (11, 2), (22751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_22751
  · decide +kernel

theorem prime_5751043 : Nat.Prime 5751043 := by
  apply nodeValid_prime [2, 3, 11, 79, 1103] ⟨5751043, 3, [(2, 1), (3, 1), (11, 1), (79, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
    · exact prime_1103
  · decide +kernel

theorem prime_5992297 : Nat.Prime 5992297 := by
  apply nodeValid_prime [2, 3, 17, 19, 773] ⟨5992297, 5, [(2, 3), (3, 1), (17, 1), (19, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_773
  · decide +kernel

theorem prime_6062603 : Nat.Prime 6062603 := by
  apply nodeValid_prime [2, 7, 13, 33311] ⟨6062603, 6, [(2, 1), (7, 1), (13, 1), (33311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_33311
  · decide +kernel

theorem prime_6903643 : Nat.Prime 6903643 := by
  apply nodeValid_prime [2, 3, 47, 24481] ⟨6903643, 5, [(2, 1), (3, 1), (47, 1), (24481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_24481
  · decide +kernel

theorem prime_7012697 : Nat.Prime 7012697 := by
  apply nodeValid_prime [2, 31, 28277] ⟨7012697, 5, [(2, 3), (31, 1), (28277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_28277
  · decide +kernel

theorem prime_8183729 : Nat.Prime 8183729 := by
  apply nodeValid_prime [2, 7, 89, 821] ⟨8183729, 3, [(2, 4), (7, 1), (89, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_821
  · decide +kernel

theorem prime_10874363 : Nat.Prime 10874363 := by
  apply nodeValid_prime [2, 29, 433] ⟨10874363, 2, [(2, 1), (29, 1), (433, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_433
  · decide +kernel

theorem prime_11004853 : Nat.Prime 11004853 := by
  apply nodeValid_prime [2, 3, 439, 2089] ⟨11004853, 2, [(2, 2), (3, 1), (439, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_439
    · exact prime_2089
  · decide +kernel

theorem prime_11011487 : Nat.Prime 11011487 := by
  apply nodeValid_prime [2, 5505743] ⟨11011487, 5, [(2, 1), (5505743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5505743
  · decide +kernel

theorem prime_12125207 : Nat.Prime 12125207 := by
  apply nodeValid_prime [2, 6062603] ⟨12125207, 5, [(2, 1), (6062603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6062603
  · decide +kernel

theorem prime_14646941 : Nat.Prime 14646941 := by
  apply nodeValid_prime [2, 5, 7, 11, 9511] ⟨14646941, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (9511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_9511
  · decide +kernel

theorem prime_15776671 : Nat.Prime 15776671 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 5779] ⟨15776671, 15, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (5779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_5779
  · decide +kernel

theorem prime_16750567 : Nat.Prime 16750567 := by
  apply nodeValid_prime [2, 3, 7, 37, 3593] ⟨16750567, 5, [(2, 1), (3, 2), (7, 1), (37, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_3593
  · decide +kernel

theorem prime_20529451 : Nat.Prime 20529451 := by
  apply nodeValid_prime [2, 3, 5, 37, 137] ⟨20529451, 2, [(2, 1), (3, 4), (5, 2), (37, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_137
  · decide +kernel

theorem prime_21537161 : Nat.Prime 21537161 := by
  apply nodeValid_prime [2, 5, 191, 2819] ⟨21537161, 3, [(2, 3), (5, 1), (191, 1), (2819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
    · exact prime_2819
  · decide +kernel

theorem prime_31903363 : Nat.Prime 31903363 := by
  apply nodeValid_prime [2, 3, 197, 2999] ⟨31903363, 7, [(2, 1), (3, 3), (197, 1), (2999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_2999
  · decide +kernel

theorem prime_38637029 : Nat.Prime 38637029 := by
  apply nodeValid_prime [2, 37, 261061] ⟨38637029, 2, [(2, 2), (37, 1), (261061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_261061
  · decide +kernel

theorem prime_39023627 : Nat.Prime 39023627 := by
  apply nodeValid_prime [2, 2917, 6689] ⟨39023627, 2, [(2, 1), (2917, 1), (6689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2917
    · exact prime_6689
  · decide +kernel

theorem prime_39150569 : Nat.Prime 39150569 := by
  apply nodeValid_prime [2, 443, 11047] ⟨39150569, 3, [(2, 3), (443, 1), (11047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_11047
  · decide +kernel

theorem prime_43074323 : Nat.Prime 43074323 := by
  apply nodeValid_prime [2, 21537161] ⟨43074323, 2, [(2, 1), (21537161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21537161
  · decide +kernel

theorem prime_51916471 : Nat.Prime 51916471 := by
  apply nodeValid_prime [2, 3, 5, 17, 101797] ⟨51916471, 19, [(2, 1), (3, 1), (5, 1), (17, 1), (101797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_101797
  · decide +kernel

theorem prime_54079241 : Nat.Prime 54079241 := by
  apply nodeValid_prime [2, 5, 1351981] ⟨54079241, 3, [(2, 3), (5, 1), (1351981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1351981
  · decide +kernel

theorem prime_74467189 : Nat.Prime 74467189 := by
  apply nodeValid_prime [2, 3, 229837] ⟨74467189, 2, [(2, 2), (3, 4), (229837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229837
  · decide +kernel

theorem prime_77274059 : Nat.Prime 77274059 := by
  apply nodeValid_prime [2, 38637029] ⟨77274059, 2, [(2, 1), (38637029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38637029
  · decide +kernel

theorem prime_90493049 : Nat.Prime 90493049 := by
  apply nodeValid_prime [2, 19, 47, 53, 239] ⟨90493049, 3, [(2, 3), (19, 1), (47, 1), (53, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_53
    · exact prime_239
  · decide +kernel

theorem prime_108158483 : Nat.Prime 108158483 := by
  apply nodeValid_prime [2, 54079241] ⟨108158483, 2, [(2, 1), (54079241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54079241
  · decide +kernel

theorem prime_130111843 : Nat.Prime 130111843 := by
  apply nodeValid_prime [2, 3, 7, 73, 42437] ⟨130111843, 2, [(2, 1), (3, 1), (7, 1), (73, 1), (42437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_42437
  · decide +kernel

theorem prime_175763293 : Nat.Prime 175763293 := by
  apply nodeValid_prime [2, 3, 14646941] ⟨175763293, 2, [(2, 2), (3, 1), (14646941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14646941
  · decide +kernel

theorem prime_199799641 : Nat.Prime 199799641 := by
  apply nodeValid_prime [2, 3, 5, 17, 32647] ⟨199799641, 7, [(2, 3), (3, 2), (5, 1), (17, 1), (32647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_32647
  · decide +kernel

theorem prime_219910601 : Nat.Prime 219910601 := by
  apply nodeValid_prime [2, 5, 7, 13, 43, 281] ⟨219910601, 6, [(2, 3), (5, 2), (7, 1), (13, 1), (43, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_281
  · decide +kernel

theorem prime_505990411 : Nat.Prime 505990411 := by
  apply nodeValid_prime [2, 3, 5, 83, 203209] ⟨505990411, 3, [(2, 1), (3, 1), (5, 1), (83, 1), (203209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_203209
  · decide +kernel

theorem prime_641924083 : Nat.Prime 641924083 := by
  apply nodeValid_prime [2, 3, 19, 625657] ⟨641924083, 2, [(2, 1), (3, 3), (19, 1), (625657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_625657
  · decide +kernel

theorem prime_646017419 : Nat.Prime 646017419 := by
  apply nodeValid_prime [2, 463, 697643] ⟨646017419, 2, [(2, 1), (463, 1), (697643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_463
    · exact prime_697643
  · decide +kernel

theorem prime_723944393 : Nat.Prime 723944393 := by
  apply nodeValid_prime [2, 90493049] ⟨723944393, 3, [(2, 3), (90493049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90493049
  · decide +kernel

theorem prime_733366099 : Nat.Prime 733366099 := by
  apply nodeValid_prime [2, 3, 41, 47, 21143] ⟨733366099, 2, [(2, 1), (3, 2), (41, 1), (47, 1), (21143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_47
    · exact prime_21143
  · decide +kernel

theorem prime_780612559 : Nat.Prime 780612559 := by
  apply nodeValid_prime [2, 3, 11, 587, 20149] ⟨780612559, 3, [(2, 1), (3, 1), (11, 1), (587, 1), (20149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_587
    · exact prime_20149
  · decide +kernel

theorem prime_862236943 : Nat.Prime 862236943 := by
  apply nodeValid_prime [2, 3, 7, 20529451] ⟨862236943, 3, [(2, 1), (3, 1), (7, 1), (20529451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_20529451
  · decide +kernel

theorem prime_1103275961 : Nat.Prime 1103275961 := by
  apply nodeValid_prime [2, 5, 23, 331, 3623] ⟨1103275961, 6, [(2, 3), (5, 1), (23, 1), (331, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_331
    · exact prime_3623
  · decide +kernel

theorem prime_1130933753 : Nat.Prime 1130933753 := by
  apply nodeValid_prime [2, 13, 10874363] ⟨1130933753, 3, [(2, 3), (13, 1), (10874363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10874363
  · decide +kernel

theorem prime_1440776021 : Nat.Prime 1440776021 := by
  apply nodeValid_prime [2, 5, 71, 1014631] ⟨1440776021, 2, [(2, 2), (5, 1), (71, 1), (1014631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_1014631
  · decide +kernel

theorem prime_4078105909 : Nat.Prime 4078105909 := by
  apply nodeValid_prime [2, 3, 277, 1226867] ⟨4078105909, 2, [(2, 2), (3, 1), (277, 1), (1226867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_1226867
  · decide +kernel

theorem prime_6027376603 : Nat.Prime 6027376603 := by
  apply nodeValid_prime [2, 3, 13, 77274059] ⟨6027376603, 3, [(2, 1), (3, 1), (13, 1), (77274059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_77274059
  · decide +kernel

theorem prime_6915724919 : Nat.Prime 6915724919 := by
  apply nodeValid_prime [2, 19, 1583, 114967] ⟨6915724919, 11, [(2, 1), (19, 1), (1583, 1), (114967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1583
    · exact prime_114967
  · decide +kernel

theorem prime_7703088997 : Nat.Prime 7703088997 := by
  apply nodeValid_prime [2, 3, 641924083] ⟨7703088997, 2, [(2, 2), (3, 1), (641924083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_641924083
  · decide +kernel

theorem prime_13359846361 : Nat.Prime 13359846361 := by
  apply nodeValid_prime [2, 3, 5, 7, 131, 167, 727] ⟨13359846361, 34, [(2, 3), (3, 1), (5, 1), (7, 1), (131, 1), (167, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_131
    · exact prime_167
    · exact prime_727
  · decide +kernel

theorem prime_22544996833 : Nat.Prime 22544996833 := by
  apply nodeValid_prime [2, 3, 61, 163, 7873] ⟨22544996833, 5, [(2, 5), (3, 2), (61, 1), (163, 1), (7873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_163
    · exact prime_7873
  · decide +kernel

theorem prime_23166220577 : Nat.Prime 23166220577 := by
  apply nodeValid_prime [2, 723944393] ⟨23166220577, 3, [(2, 5), (723944393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_723944393
  · decide +kernel

theorem prime_33566339689 : Nat.Prime 33566339689 := by
  apply nodeValid_prime [2, 3, 7, 199799641] ⟨33566339689, 23, [(2, 3), (3, 1), (7, 1), (199799641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199799641
  · decide +kernel

theorem prime_34834889569 : Nat.Prime 34834889569 := by
  apply nodeValid_prime [2, 3, 23, 15776671] ⟨34834889569, 11, [(2, 5), (3, 1), (23, 1), (15776671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_15776671
  · decide +kernel

theorem prime_68139844319 : Nat.Prime 68139844319 := by
  apply nodeValid_prime [2, 7, 13, 37, 433, 23369] ⟨68139844319, 7, [(2, 1), (7, 1), (13, 1), (37, 1), (433, 1), (23369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_433
    · exact prime_23369
  · decide +kernel

theorem prime_68139851399 : Nat.Prime 68139851399 := by
  apply nodeValid_prime [2, 21247, 1603517] ⟨68139851399, 7, [(2, 1), (21247, 1), (1603517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21247
    · exact prime_1603517
  · decide +kernel

theorem prime_132271336423 : Nat.Prime 132271336423 := by
  apply nodeValid_prime [2, 3, 59, 127, 108967] ⟨132271336423, 3, [(2, 1), (3, 4), (59, 1), (127, 1), (108967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_127
    · exact prime_108967
  · decide +kernel

theorem prime_132271342999 : Nat.Prime 132271342999 := by
  apply nodeValid_prime [2, 3, 691, 31903363] ⟨132271342999, 3, [(2, 1), (3, 1), (691, 1), (31903363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_31903363
  · decide +kernel

theorem prime_132271343543 : Nat.Prime 132271343543 := by
  apply nodeValid_prime [2, 13, 17431, 291857] ⟨132271343543, 5, [(2, 1), (13, 1), (17431, 1), (291857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17431
    · exact prime_291857
  · decide +kernel

theorem prime_132602273003 : Nat.Prime 132602273003 := by
  apply nodeValid_prime [2, 17, 5209, 748717] ⟨132602273003, 2, [(2, 1), (17, 1), (5209, 1), (748717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_5209
    · exact prime_748717
  · decide +kernel

theorem prime_132602284547 : Nat.Prime 132602284547 := by
  apply nodeValid_prime [2, 1699, 39023627] ⟨132602284547, 2, [(2, 1), (1699, 1), (39023627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1699
    · exact prime_39023627
  · decide +kernel

theorem prime_132602285267 : Nat.Prime 132602285267 := by
  apply nodeValid_prime [2, 11, 6027376603] ⟨132602285267, 2, [(2, 1), (11, 1), (6027376603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6027376603
  · decide +kernel

theorem prime_132933770551 : Nat.Prime 132933770551 := by
  apply nodeValid_prime [2, 3, 5, 7, 53, 503, 1583] ⟨132933770551, 3, [(2, 1), (3, 2), (5, 2), (7, 1), (53, 1), (503, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_503
    · exact prime_1583
  · decide +kernel

theorem prime_132933775397 : Nat.Prime 132933775397 := by
  apply nodeValid_prime [2, 113, 1063, 276671] ⟨132933775397, 2, [(2, 2), (113, 1), (1063, 1), (276671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_1063
    · exact prime_276671
  · decide +kernel

theorem prime_132933775451 : Nat.Prime 132933775451 := by
  apply nodeValid_prime [2, 5, 7, 17, 43, 519577] ⟨132933775451, 6, [(2, 1), (5, 2), (7, 1), (17, 1), (43, 1), (519577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_519577
  · decide +kernel

theorem prime_133265824099 : Nat.Prime 133265824099 := by
  apply nodeValid_prime [2, 3, 11, 19, 71, 1496797] ⟨133265824099, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (71, 1), (1496797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_71
    · exact prime_1496797
  · decide +kernel

theorem prime_133265824207 : Nat.Prime 133265824207 := by
  apply nodeValid_prime [2, 3, 101, 219910601] ⟨133265824207, 6, [(2, 1), (3, 1), (101, 1), (219910601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_219910601
  · decide +kernel

theorem prime_133265826361 : Nat.Prime 133265826361 := by
  apply nodeValid_prime [2, 3, 5, 229, 1616519] ⟨133265826361, 7, [(2, 3), (3, 2), (5, 1), (229, 1), (1616519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
    · exact prime_1616519
  · decide +kernel

theorem prime_133598444179 : Nat.Prime 133598444179 := by
  apply nodeValid_prime [2, 3, 19, 29179, 40163] ⟨133598444179, 2, [(2, 1), (3, 1), (19, 1), (29179, 1), (40163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29179
    · exact prime_40163
  · decide +kernel

theorem prime_133598463517 : Nat.Prime 133598463517 := by
  apply nodeValid_prime [2, 3, 7, 17, 43, 229, 3167] ⟨133598463517, 5, [(2, 2), (3, 2), (7, 1), (17, 1), (43, 1), (229, 1), (3167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_229
    · exact prime_3167
  · decide +kernel

theorem prime_133598463611 : Nat.Prime 133598463611 := by
  apply nodeValid_prime [2, 5, 13359846361] ⟨133598463611, 2, [(2, 1), (5, 1), (13359846361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13359846361
  · decide +kernel

theorem prime_133931621651 : Nat.Prime 133931621651 := by
  apply nodeValid_prime [2, 5, 179, 1693, 8839] ⟨133931621651, 2, [(2, 1), (5, 2), (179, 1), (1693, 1), (8839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_1693
    · exact prime_8839
  · decide +kernel

theorem prime_133931629267 : Nat.Prime 133931629267 := by
  apply nodeValid_prime [2, 3, 127, 175763293] ⟨133931629267, 3, [(2, 1), (3, 1), (127, 1), (175763293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_175763293
  · decide +kernel

theorem prime_133931631193 : Nat.Prime 133931631193 := by
  apply nodeValid_prime [2, 3, 37, 149, 1012241] ⟨133931631193, 7, [(2, 3), (3, 1), (37, 1), (149, 1), (1012241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_149
    · exact prime_1012241
  · decide +kernel

theorem prime_134265358037 : Nat.Prime 134265358037 := by
  apply nodeValid_prime [2, 42571, 788479] ⟨134265358037, 2, [(2, 2), (42571, 1), (788479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_42571
    · exact prime_788479
  · decide +kernel

theorem prime_134265358757 : Nat.Prime 134265358757 := by
  apply nodeValid_prime [2, 33566339689] ⟨134265358757, 2, [(2, 2), (33566339689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33566339689
  · decide +kernel

theorem prime_134265360149 : Nat.Prime 134265360149 := by
  apply nodeValid_prime [2, 43, 780612559] ⟨134265360149, 2, [(2, 2), (43, 1), (780612559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_780612559
  · decide +kernel

theorem prime_134599654411 : Nat.Prime 134599654411 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 277, 73291] ⟨134599654411, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (277, 1), (73291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_277
    · exact prime_73291
  · decide +kernel

theorem prime_134599656223 : Nat.Prime 134599656223 := by
  apply nodeValid_prime [2, 3, 191, 39150569] ⟨134599656223, 3, [(2, 1), (3, 2), (191, 1), (39150569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_39150569
  · decide +kernel

theorem prime_134599667243 : Nat.Prime 134599667243 := by
  apply nodeValid_prime [2, 61, 1103275961] ⟨134599667243, 2, [(2, 1), (61, 1), (1103275961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_1103275961
  · decide +kernel

theorem prime_134934543847 : Nat.Prime 134934543847 := by
  apply nodeValid_prime [2, 3, 139, 5992297] ⟨134934543847, 5, [(2, 1), (3, 4), (139, 1), (5992297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_5992297
  · decide +kernel

theorem prime_134934546451 : Nat.Prime 134934546451 := by
  apply nodeValid_prime [2, 3, 5, 11, 8783, 9311] ⟨134934546451, 2, [(2, 1), (3, 1), (5, 2), (11, 1), (8783, 1), (9311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_8783
    · exact prime_9311
  · decide +kernel

theorem prime_134934546469 : Nat.Prime 134934546469 := by
  apply nodeValid_prime [2, 3, 151, 74467189] ⟨134934546469, 13, [(2, 2), (3, 1), (151, 1), (74467189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_74467189
  · decide +kernel

theorem prime_135269980943 : Nat.Prime 135269980943 := by
  apply nodeValid_prime [2, 97, 101, 6903643] ⟨135269980943, 5, [(2, 1), (97, 1), (101, 1), (6903643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_101
    · exact prime_6903643
  · decide +kernel

theorem prime_135269980999 : Nat.Prime 135269980999 := by
  apply nodeValid_prime [2, 3, 22544996833] ⟨135269980999, 15, [(2, 1), (3, 1), (22544996833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22544996833
  · decide +kernel

theorem prime_135269985601 : Nat.Prime 135269985601 := by
  apply nodeValid_prime [2, 3, 5, 47, 269, 743] ⟨135269985601, 29, [(2, 6), (3, 2), (5, 2), (47, 1), (269, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_269
    · exact prime_743
  · decide +kernel

theorem prime_135605959633 : Nat.Prime 135605959633 := by
  apply nodeValid_prime [2, 3, 11, 13, 37, 13691] ⟨135605959633, 5, [(2, 4), (3, 2), (11, 1), (13, 2), (37, 1), (13691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_37
    · exact prime_13691
  · decide +kernel

theorem prime_135605959679 : Nat.Prime 135605959679 := by
  apply nodeValid_prime [2, 7, 73, 1063, 124823] ⟨135605959679, 7, [(2, 1), (7, 1), (73, 1), (1063, 1), (124823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_1063
    · exact prime_124823
  · decide +kernel

theorem prime_135605992787 : Nat.Prime 135605992787 := by
  apply nodeValid_prime [2, 11, 83, 1031, 72031] ⟨135605992787, 5, [(2, 1), (11, 1), (83, 1), (1031, 1), (72031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83
    · exact prime_1031
    · exact prime_72031
  · decide +kernel

theorem prime_135942563389 : Nat.Prime 135942563389 := by
  apply nodeValid_prime [2, 3, 263, 43074323] ⟨135942563389, 6, [(2, 2), (3, 1), (263, 1), (43074323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_43074323
  · decide +kernel

theorem prime_135942576551 : Nat.Prime 135942576551 := by
  apply nodeValid_prime [2, 5, 11, 17, 19, 765227] ⟨135942576551, 11, [(2, 1), (5, 2), (11, 1), (17, 1), (19, 1), (765227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_765227
  · decide +kernel

theorem prime_135942577409 : Nat.Prime 135942577409 := by
  apply nodeValid_prime [2, 11, 47, 1027129] ⟨135942577409, 3, [(2, 8), (11, 1), (47, 1), (1027129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_1027129
  · decide +kernel

theorem prime_136279688581 : Nat.Prime 136279688581 := by
  apply nodeValid_prime [2, 3, 5, 7, 108158483] ⟨136279688581, 6, [(2, 2), (3, 2), (5, 1), (7, 1), (108158483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_108158483
  · decide +kernel

theorem prime_136279688639 : Nat.Prime 136279688639 := by
  apply nodeValid_prime [2, 68139844319] ⟨136279688639, 41, [(2, 1), (68139844319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68139844319
  · decide +kernel

theorem prime_136279702799 : Nat.Prime 136279702799 := by
  apply nodeValid_prime [2, 68139851399] ⟨136279702799, 7, [(2, 1), (68139851399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68139851399
  · decide +kernel

theorem prime_136617410971 : Nat.Prime 136617410971 := by
  apply nodeValid_prime [2, 3, 5, 505990411] ⟨136617410971, 2, [(2, 1), (3, 3), (5, 1), (505990411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_505990411
  · decide +kernel

theorem prime_136617434731 : Nat.Prime 136617434731 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 67, 63463] ⟨136617434731, 2, [(2, 1), (3, 3), (5, 1), (7, 1), (17, 1), (67, 1), (63463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_67
    · exact prime_63463
  · decide +kernel

theorem prime_136617435151 : Nat.Prime 136617435151 := by
  apply nodeValid_prime [2, 3, 5, 7, 130111843] ⟨136617435151, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (130111843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_130111843
  · decide +kernel

theorem prime_136955650499 : Nat.Prime 136955650499 := by
  apply nodeValid_prime [2, 1319, 51916471] ⟨136955650499, 2, [(2, 1), (1319, 1), (51916471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1319
    · exact prime_51916471
  · decide +kernel

theorem prime_136955651999 : Nat.Prime 136955651999 := by
  apply nodeValid_prime [2, 11, 31, 3229, 62191] ⟨136955651999, 11, [(2, 1), (11, 1), (31, 1), (3229, 1), (62191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_3229
    · exact prime_62191
  · decide +kernel

theorem prime_136955692829 : Nat.Prime 136955692829 := by
  apply nodeValid_prime [2, 53, 646017419] ⟨136955692829, 2, [(2, 2), (53, 1), (646017419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_646017419
  · decide +kernel

theorem prime_137294539357 : Nat.Prime 137294539357 := by
  apply nodeValid_prime [2, 3, 13, 7523, 8999] ⟨137294539357, 2, [(2, 2), (3, 1), (13, 2), (7523, 1), (8999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_7523
    · exact prime_8999
  · decide +kernel

theorem prime_137294581867 : Nat.Prime 137294581867 := by
  apply nodeValid_prime [2, 3, 13, 251, 7012697] ⟨137294581867, 2, [(2, 1), (3, 1), (13, 1), (251, 1), (7012697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_251
    · exact prime_7012697
  · decide +kernel

theorem prime_137294582003 : Nat.Prime 137294582003 := by
  apply nodeValid_prime [2, 179, 239, 1604621] ⟨137294582003, 2, [(2, 1), (179, 1), (239, 1), (1604621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_239
    · exact prime_1604621
  · decide +kernel

theorem prime_137633954323 : Nat.Prime 137633954323 := by
  apply nodeValid_prime [2, 3, 2803, 8183729] ⟨137633954323, 2, [(2, 1), (3, 1), (2803, 1), (8183729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2803
    · exact prime_8183729
  · decide +kernel

theorem prime_137633958221 : Nat.Prime 137633958221 := by
  apply nodeValid_prime [2, 5, 11, 23, 3607, 7541] ⟨137633958221, 10, [(2, 2), (5, 1), (11, 1), (23, 1), (3607, 1), (7541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_3607
    · exact prime_7541
  · decide +kernel

theorem prime_137633961077 : Nat.Prime 137633961077 := by
  apply nodeValid_prime [2, 31, 193, 5751043] ⟨137633961077, 2, [(2, 2), (31, 1), (193, 1), (5751043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_193
    · exact prime_5751043
  · decide +kernel

theorem prime_137973917867 : Nat.Prime 137973917867 := by
  apply nodeValid_prime [2, 61, 1130933753] ⟨137973917867, 2, [(2, 1), (61, 1), (1130933753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_1130933753
  · decide +kernel

theorem prime_137973918881 : Nat.Prime 137973918881 := by
  apply nodeValid_prime [2, 5, 7, 163, 353, 2141] ⟨137973918881, 3, [(2, 5), (5, 1), (7, 1), (163, 1), (353, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_163
    · exact prime_353
    · exact prime_2141
  · decide +kernel

theorem prime_137973932111 : Nat.Prime 137973932111 := by
  apply nodeValid_prime [2, 5, 7, 179, 11011487] ⟨137973932111, 13, [(2, 1), (5, 1), (7, 1), (179, 1), (11011487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_179
    · exact prime_11011487
  · decide +kernel

theorem prime_138314479469 : Nat.Prime 138314479469 := by
  apply nodeValid_prime [2, 11, 4721, 665857] ⟨138314479469, 2, [(2, 2), (11, 1), (4721, 1), (665857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4721
    · exact prime_665857
  · decide +kernel

theorem prime_138314498017 : Nat.Prime 138314498017 := by
  apply nodeValid_prime [2, 3, 1440776021] ⟨138314498017, 7, [(2, 5), (3, 1), (1440776021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1440776021
  · decide +kernel

theorem prime_138314498381 : Nat.Prime 138314498381 := by
  apply nodeValid_prime [2, 5, 6915724919] ⟨138314498381, 2, [(2, 2), (5, 1), (6915724919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6915724919
  · decide +kernel

theorem prime_138655600907 : Nat.Prime 138655600907 := by
  apply nodeValid_prime [2, 17, 4078105909] ⟨138655600907, 2, [(2, 1), (17, 1), (4078105909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4078105909
  · decide +kernel

theorem prime_138655601947 : Nat.Prime 138655601947 := by
  apply nodeValid_prime [2, 3, 7703088997] ⟨138655601947, 2, [(2, 1), (3, 2), (7703088997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7703088997
  · decide +kernel

theorem prime_138655606657 : Nat.Prime 138655606657 := by
  apply nodeValid_prime [2, 3, 7, 43, 73, 16433] ⟨138655606657, 11, [(2, 7), (3, 1), (7, 1), (43, 1), (73, 1), (16433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_73
    · exact prime_16433
  · decide +kernel

theorem prime_138997290433 : Nat.Prime 138997290433 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 723221] ⟨138997290433, 5, [(2, 6), (3, 1), (7, 1), (11, 1), (13, 1), (723221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_723221
  · decide +kernel

theorem prime_138997323463 : Nat.Prime 138997323463 := by
  apply nodeValid_prime [2, 3, 23166220577] ⟨138997323463, 3, [(2, 1), (3, 1), (23166220577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23166220577
  · decide +kernel

theorem prime_138997324211 : Nat.Prime 138997324211 := by
  apply nodeValid_prime [2, 5, 40427, 343823] ⟨138997324211, 2, [(2, 1), (5, 1), (40427, 1), (343823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40427
    · exact prime_343823
  · decide +kernel

theorem prime_139339550269 : Nat.Prime 139339550269 := by
  apply nodeValid_prime [2, 3, 23, 359, 156253] ⟨139339550269, 6, [(2, 2), (3, 3), (23, 1), (359, 1), (156253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_359
    · exact prime_156253
  · decide +kernel

theorem prime_139339558277 : Nat.Prime 139339558277 := by
  apply nodeValid_prime [2, 34834889569] ⟨139339558277, 2, [(2, 2), (34834889569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34834889569
  · decide +kernel

theorem prime_139339558811 : Nat.Prime 139339558811 := by
  apply nodeValid_prime [2, 5, 19, 733366099] ⟨139339558811, 2, [(2, 1), (5, 1), (19, 1), (733366099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_733366099
  · decide +kernel

theorem prime_139682377999 : Nat.Prime 139682377999 := by
  apply nodeValid_prime [2, 3, 53, 251, 583337] ⟨139682377999, 3, [(2, 1), (3, 2), (53, 1), (251, 1), (583337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_251
    · exact prime_583337
  · decide +kernel

theorem prime_139682384641 : Nat.Prime 139682384641 := by
  apply nodeValid_prime [2, 3, 5, 12125207] ⟨139682384641, 13, [(2, 8), (3, 2), (5, 1), (12125207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12125207
  · decide +kernel

theorem prime_139682384767 : Nat.Prime 139682384767 := by
  apply nodeValid_prime [2, 3, 862236943] ⟨139682384767, 3, [(2, 1), (3, 4), (862236943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_862236943
  · decide +kernel

theorem prime_140025749389 : Nat.Prime 140025749389 := by
  apply nodeValid_prime [2, 3, 7, 139, 733, 16361] ⟨140025749389, 2, [(2, 2), (3, 1), (7, 1), (139, 1), (733, 1), (16361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
    · exact prime_733
    · exact prime_16361
  · decide +kernel

theorem prime_140025749573 : Nat.Prime 140025749573 := by
  apply nodeValid_prime [2, 3181, 11004853] ⟨140025749573, 2, [(2, 2), (3181, 1), (11004853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3181
    · exact prime_11004853
  · decide +kernel

theorem prime_140025777659 : Nat.Prime 140025777659 := by
  apply nodeValid_prime [2, 13, 109, 211, 234167] ⟨140025777659, 2, [(2, 1), (13, 1), (109, 1), (211, 1), (234167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_109
    · exact prime_211
    · exact prime_234167
  · decide +kernel

theorem prime_140369751461 : Nat.Prime 140369751461 := by
  apply nodeValid_prime [2, 5, 419, 16750567] ⟨140369751461, 2, [(2, 2), (5, 1), (419, 1), (16750567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_419
    · exact prime_16750567
  · decide +kernel

theorem prime_140369765843 : Nat.Prime 140369765843 := by
  apply nodeValid_prime [2, 367, 953, 200671] ⟨140369765843, 2, [(2, 1), (367, 1), (953, 1), (200671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_953
    · exact prime_200671
  · decide +kernel

theorem prime_140369766403 : Nat.Prime 140369766403 := by
  apply nodeValid_prime [2, 3, 151, 2729, 56773] ⟨140369766403, 2, [(2, 1), (3, 1), (151, 1), (2729, 1), (56773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_2729
    · exact prime_56773
  · decide +kernel

end Sude.Lucas.Generated
