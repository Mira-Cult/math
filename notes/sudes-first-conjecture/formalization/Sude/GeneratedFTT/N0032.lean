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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1951 : Nat.Prime 1951 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨1951, 3, [(2, 1), (3, 1), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_3319 : Nat.Prime 3319 := by
  apply nodeValid_prime [2, 3, 7, 79] ⟨3319, 6, [(2, 1), (3, 1), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_3643 : Nat.Prime 3643 := by
  apply nodeValid_prime [2, 3, 607] ⟨3643, 2, [(2, 1), (3, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_607
  · decide +kernel

theorem prime_3733 : Nat.Prime 3733 := by
  apply nodeValid_prime [2, 3, 311] ⟨3733, 2, [(2, 2), (3, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
  · decide +kernel

theorem prime_3823 : Nat.Prime 3823 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨3823, 3, [(2, 1), (3, 1), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_7759 : Nat.Prime 7759 := by
  apply nodeValid_prime [2, 3, 431] ⟨7759, 3, [(2, 1), (3, 2), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
  · decide +kernel

theorem prime_8167 : Nat.Prime 8167 := by
  apply nodeValid_prime [2, 3, 1361] ⟨8167, 3, [(2, 1), (3, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1361
  · decide +kernel

theorem prime_8537 : Nat.Prime 8537 := by
  apply nodeValid_prime [2, 11, 97] ⟨8537, 3, [(2, 3), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_8609 : Nat.Prime 8609 := by
  apply nodeValid_prime [2, 269] ⟨8609, 3, [(2, 5), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_269
  · decide +kernel

theorem prime_8627 : Nat.Prime 8627 := by
  apply nodeValid_prime [2, 19, 227] ⟨8627, 2, [(2, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_9463 : Nat.Prime 9463 := by
  apply nodeValid_prime [2, 3, 19, 83] ⟨9463, 3, [(2, 1), (3, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_9661 : Nat.Prime 9661 := by
  apply nodeValid_prime [2, 3, 5, 7, 23] ⟨9661, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_9697 : Nat.Prime 9697 := by
  apply nodeValid_prime [2, 3, 101] ⟨9697, 10, [(2, 5), (3, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_10891 : Nat.Prime 10891 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨10891, 2, [(2, 1), (3, 2), (5, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_11689 : Nat.Prime 11689 := by
  apply nodeValid_prime [2, 3, 487] ⟨11689, 7, [(2, 3), (3, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
  · decide +kernel

theorem prime_12109 : Nat.Prime 12109 := by
  apply nodeValid_prime [2, 3, 1009] ⟨12109, 6, [(2, 2), (3, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1009
  · decide +kernel

theorem prime_12919 : Nat.Prime 12919 := by
  apply nodeValid_prime [2, 3, 2153] ⟨12919, 6, [(2, 1), (3, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2153
  · decide +kernel

theorem prime_13063 : Nat.Prime 13063 := by
  apply nodeValid_prime [2, 3, 7, 311] ⟨13063, 5, [(2, 1), (3, 1), (7, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_311
  · decide +kernel

theorem prime_13613 : Nat.Prime 13613 := by
  apply nodeValid_prime [2, 41, 83] ⟨13613, 2, [(2, 2), (41, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_83
  · decide +kernel

theorem prime_18251 : Nat.Prime 18251 := by
  apply nodeValid_prime [2, 5, 73] ⟨18251, 2, [(2, 1), (5, 3), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_20929 : Nat.Prime 20929 := by
  apply nodeValid_prime [2, 3, 109] ⟨20929, 7, [(2, 6), (3, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_21061 : Nat.Prime 21061 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨21061, 7, [(2, 2), (3, 4), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_22079 : Nat.Prime 22079 := by
  apply nodeValid_prime [2, 7, 19, 83] ⟨22079, 7, [(2, 1), (7, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_22943 : Nat.Prime 22943 := by
  apply nodeValid_prime [2, 11471] ⟨22943, 5, [(2, 1), (11471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11471
  · decide +kernel

theorem prime_23593 : Nat.Prime 23593 := by
  apply nodeValid_prime [2, 3, 983] ⟨23593, 5, [(2, 3), (3, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_983
  · decide +kernel

theorem prime_28771 : Nat.Prime 28771 := by
  apply nodeValid_prime [2, 3, 5, 7, 137] ⟨28771, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_29389 : Nat.Prime 29389 := by
  apply nodeValid_prime [2, 3, 31, 79] ⟨29389, 2, [(2, 2), (3, 1), (31, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_79
  · decide +kernel

theorem prime_34513 : Nat.Prime 34513 := by
  apply nodeValid_prime [2, 3, 719] ⟨34513, 11, [(2, 4), (3, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
  · decide +kernel

theorem prime_35509 : Nat.Prime 35509 := by
  apply nodeValid_prime [2, 3, 11, 269] ⟨35509, 2, [(2, 2), (3, 1), (11, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_269
  · decide +kernel

theorem prime_40493 : Nat.Prime 40493 := by
  apply nodeValid_prime [2, 53, 191] ⟨40493, 2, [(2, 2), (53, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_191
  · decide +kernel

theorem prime_41381 : Nat.Prime 41381 := by
  apply nodeValid_prime [2, 5, 2069] ⟨41381, 3, [(2, 2), (5, 1), (2069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2069
  · decide +kernel

theorem prime_45077 : Nat.Prime 45077 := by
  apply nodeValid_prime [2, 59, 191] ⟨45077, 2, [(2, 2), (59, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_191
  · decide +kernel

theorem prime_45427 : Nat.Prime 45427 := by
  apply nodeValid_prime [2, 3, 67, 113] ⟨45427, 3, [(2, 1), (3, 1), (67, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_113
  · decide +kernel

theorem prime_45887 : Nat.Prime 45887 := by
  apply nodeValid_prime [2, 22943] ⟨45887, 5, [(2, 1), (22943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22943
  · decide +kernel

theorem prime_46273 : Nat.Prime 46273 := by
  apply nodeValid_prime [2, 3, 241] ⟨46273, 5, [(2, 6), (3, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel

theorem prime_48647 : Nat.Prime 48647 := by
  apply nodeValid_prime [2, 13, 1871] ⟨48647, 5, [(2, 1), (13, 1), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1871
  · decide +kernel

theorem prime_49633 : Nat.Prime 49633 := by
  apply nodeValid_prime [2, 3, 11, 47] ⟨49633, 5, [(2, 5), (3, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_54629 : Nat.Prime 54629 := by
  apply nodeValid_prime [2, 7, 1951] ⟨54629, 3, [(2, 2), (7, 1), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1951
  · decide +kernel

theorem prime_56569 : Nat.Prime 56569 := by
  apply nodeValid_prime [2, 3, 2357] ⟨56569, 11, [(2, 3), (3, 1), (2357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2357
  · decide +kernel

theorem prime_68219 : Nat.Prime 68219 := by
  apply nodeValid_prime [2, 23, 1483] ⟨68219, 2, [(2, 1), (23, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1483
  · decide +kernel

theorem prime_68863 : Nat.Prime 68863 := by
  apply nodeValid_prime [2, 3, 23, 499] ⟨68863, 3, [(2, 1), (3, 1), (23, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_499
  · decide +kernel

theorem prime_78989 : Nat.Prime 78989 := by
  apply nodeValid_prime [2, 7, 13, 31] ⟨78989, 2, [(2, 2), (7, 2), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_82763 : Nat.Prime 82763 := by
  apply nodeValid_prime [2, 41381] ⟨82763, 2, [(2, 1), (41381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41381
  · decide +kernel

theorem prime_104711 : Nat.Prime 104711 := by
  apply nodeValid_prime [2, 5, 37, 283] ⟨104711, 43, [(2, 1), (5, 1), (37, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_283
  · decide +kernel

theorem prime_111973 : Nat.Prime 111973 := by
  apply nodeValid_prime [2, 3, 7, 31, 43] ⟨111973, 2, [(2, 2), (3, 1), (7, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_115933 : Nat.Prime 115933 := by
  apply nodeValid_prime [2, 3, 9661] ⟨115933, 2, [(2, 2), (3, 1), (9661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9661
  · decide +kernel

theorem prime_128519 : Nat.Prime 128519 := by
  apply nodeValid_prime [2, 13, 4943] ⟨128519, 23, [(2, 1), (13, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4943
  · decide +kernel

theorem prime_130631 : Nat.Prime 130631 := by
  apply nodeValid_prime [2, 5, 13063] ⟨130631, 7, [(2, 1), (5, 1), (13063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13063
  · decide +kernel

theorem prime_132859 : Nat.Prime 132859 := by
  apply nodeValid_prime [2, 3, 11, 61] ⟨132859, 2, [(2, 1), (3, 2), (11, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_138053 : Nat.Prime 138053 := by
  apply nodeValid_prime [2, 34513] ⟨138053, 2, [(2, 2), (34513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34513
  · decide +kernel

theorem prime_149119 : Nat.Prime 149119 := by
  apply nodeValid_prime [2, 3, 29, 857] ⟨149119, 15, [(2, 1), (3, 1), (29, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_857
  · decide +kernel

theorem prime_164513 : Nat.Prime 164513 := by
  apply nodeValid_prime [2, 53, 97] ⟨164513, 3, [(2, 5), (53, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_97
  · decide +kernel

theorem prime_172181 : Nat.Prime 172181 := by
  apply nodeValid_prime [2, 5, 8609] ⟨172181, 2, [(2, 2), (5, 1), (8609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8609
  · decide +kernel

theorem prime_275323 : Nat.Prime 275323 := by
  apply nodeValid_prime [2, 3, 45887] ⟨275323, 5, [(2, 1), (3, 1), (45887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45887
  · decide +kernel

theorem prime_316633 : Nat.Prime 316633 := by
  apply nodeValid_prime [2, 3, 79, 167] ⟨316633, 5, [(2, 3), (3, 1), (79, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_167
  · decide +kernel

theorem prime_328891 : Nat.Prime 328891 := by
  apply nodeValid_prime [2, 3, 5, 19, 577] ⟨328891, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_577
  · decide +kernel

theorem prime_344363 : Nat.Prime 344363 := by
  apply nodeValid_prime [2, 172181] ⟨344363, 2, [(2, 1), (172181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_172181
  · decide +kernel

theorem prime_354971 : Nat.Prime 354971 := by
  apply nodeValid_prime [2, 5, 7, 11, 461] ⟨354971, 2, [(2, 1), (5, 1), (7, 1), (11, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_461
  · decide +kernel

theorem prime_395719 : Nat.Prime 395719 := by
  apply nodeValid_prime [2, 3, 101, 653] ⟨395719, 6, [(2, 1), (3, 1), (101, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_653
  · decide +kernel

theorem prime_456811 : Nat.Prime 456811 := by
  apply nodeValid_prime [2, 3, 5, 15227] ⟨456811, 3, [(2, 1), (3, 1), (5, 1), (15227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15227
  · decide +kernel

theorem prime_529003 : Nat.Prime 529003 := by
  apply nodeValid_prime [2, 3, 29389] ⟨529003, 2, [(2, 1), (3, 2), (29389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29389
  · decide +kernel

theorem prime_695599 : Nat.Prime 695599 := by
  apply nodeValid_prime [2, 3, 115933] ⟨695599, 6, [(2, 1), (3, 1), (115933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115933
  · decide +kernel

theorem prime_706847 : Nat.Prime 706847 := by
  apply nodeValid_prime [2, 7, 29, 1741] ⟨706847, 5, [(2, 1), (7, 1), (29, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_1741
  · decide +kernel

theorem prime_721177 : Nat.Prime 721177 := by
  apply nodeValid_prime [2, 3, 151, 199] ⟨721177, 10, [(2, 3), (3, 1), (151, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_199
  · decide +kernel

theorem prime_722749 : Nat.Prime 722749 := by
  apply nodeValid_prime [2, 3, 13, 41, 113] ⟨722749, 22, [(2, 2), (3, 1), (13, 1), (41, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_113
  · decide +kernel

theorem prime_783787 : Nat.Prime 783787 := by
  apply nodeValid_prime [2, 3, 130631] ⟨783787, 2, [(2, 1), (3, 1), (130631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130631
  · decide +kernel

theorem prime_987079 : Nat.Prime 987079 := by
  apply nodeValid_prime [2, 3, 164513] ⟨987079, 7, [(2, 1), (3, 1), (164513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_164513
  · decide +kernel

theorem prime_1041119 : Nat.Prime 1041119 := by
  apply nodeValid_prime [2, 13, 23, 1741] ⟨1041119, 7, [(2, 1), (13, 1), (23, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_1741
  · decide +kernel

theorem prime_1079569 : Nat.Prime 1079569 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨1079569, 29, [(2, 4), (3, 4), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_1299821 : Nat.Prime 1299821 := by
  apply nodeValid_prime [2, 5, 17, 3823] ⟨1299821, 3, [(2, 2), (5, 1), (17, 1), (3823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_3823
  · decide +kernel

theorem prime_1621877 : Nat.Prime 1621877 := by
  apply nodeValid_prime [2, 47, 8627] ⟨1621877, 2, [(2, 2), (47, 1), (8627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_8627
  · decide +kernel

theorem prime_1829281 : Nat.Prime 1829281 := by
  apply nodeValid_prime [2, 3, 5, 37, 103] ⟨1829281, 14, [(2, 5), (3, 1), (5, 1), (37, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_103
  · decide +kernel

theorem prime_1860193 : Nat.Prime 1860193 := by
  apply nodeValid_prime [2, 3, 2153] ⟨1860193, 5, [(2, 5), (3, 3), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2153
  · decide +kernel

theorem prime_1983389 : Nat.Prime 1983389 := by
  apply nodeValid_prime [2, 11, 45077] ⟨1983389, 2, [(2, 2), (11, 1), (45077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_45077
  · decide +kernel

theorem prime_2082749 : Nat.Prime 2082749 := by
  apply nodeValid_prime [2, 43, 12109] ⟨2082749, 2, [(2, 2), (43, 1), (12109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_12109
  · decide +kernel

theorem prime_2418547 : Nat.Prime 2418547 := by
  apply nodeValid_prime [2, 3, 13, 101, 307] ⟨2418547, 14, [(2, 1), (3, 1), (13, 1), (101, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
    · exact prime_307
  · decide +kernel

theorem prime_2497337 : Nat.Prime 2497337 := by
  apply nodeValid_prime [2, 487, 641] ⟨2497337, 3, [(2, 3), (487, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_641
  · decide +kernel

theorem prime_2504011 : Nat.Prime 2504011 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 191] ⟨2504011, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_191
  · decide +kernel

theorem prime_2580917 : Nat.Prime 2580917 := by
  apply nodeValid_prime [2, 13, 49633] ⟨2580917, 2, [(2, 2), (13, 1), (49633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_49633
  · decide +kernel

theorem prime_2594959 : Nat.Prime 2594959 := by
  apply nodeValid_prime [2, 3, 37, 11689] ⟨2594959, 3, [(2, 1), (3, 1), (37, 1), (11689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_11689
  · decide +kernel

theorem prime_2922259 : Nat.Prime 2922259 := by
  apply nodeValid_prime [2, 3, 283, 1721] ⟨2922259, 2, [(2, 1), (3, 1), (283, 1), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1721
  · decide +kernel

theorem prime_3062203 : Nat.Prime 3062203 := by
  apply nodeValid_prime [2, 3, 11, 13, 43, 83] ⟨3062203, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (43, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_43
    · exact prime_83
  · decide +kernel

theorem prime_3347959 : Nat.Prime 3347959 := by
  apply nodeValid_prime [2, 3, 743, 751] ⟨3347959, 3, [(2, 1), (3, 1), (743, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_743
    · exact prime_751
  · decide +kernel

theorem prime_4112609 : Nat.Prime 4112609 := by
  apply nodeValid_prime [2, 128519] ⟨4112609, 3, [(2, 5), (128519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_128519
  · decide +kernel

theorem prime_5290031 : Nat.Prime 5290031 := by
  apply nodeValid_prime [2, 5, 529003] ⟨5290031, 13, [(2, 1), (5, 1), (529003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_529003
  · decide +kernel

theorem prime_5868277 : Nat.Prime 5868277 := by
  apply nodeValid_prime [2, 3, 131, 3733] ⟨5868277, 5, [(2, 2), (3, 1), (131, 1), (3733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_3733
  · decide +kernel

theorem prime_8008739 : Nat.Prime 8008739 := by
  apply nodeValid_prime [2, 23, 151, 1153] ⟨8008739, 2, [(2, 1), (23, 1), (151, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_151
    · exact prime_1153
  · decide +kernel

theorem prime_13488899 : Nat.Prime 13488899 := by
  apply nodeValid_prime [2, 19, 354971] ⟨13488899, 2, [(2, 1), (19, 1), (354971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_354971
  · decide +kernel

theorem prime_17689723 : Nat.Prime 17689723 := by
  apply nodeValid_prime [2, 3, 19, 8167] ⟨17689723, 2, [(2, 1), (3, 1), (19, 2), (8167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_8167
  · decide +kernel

theorem prime_19057403 : Nat.Prime 19057403 := by
  apply nodeValid_prime [2, 7, 13, 104711] ⟨19057403, 2, [(2, 1), (7, 1), (13, 1), (104711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_104711
  · decide +kernel

theorem prime_19264177 : Nat.Prime 19264177 := by
  apply nodeValid_prime [2, 3, 19, 2347] ⟨19264177, 10, [(2, 4), (3, 3), (19, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2347
  · decide +kernel

theorem prime_22018063 : Nat.Prime 22018063 := by
  apply nodeValid_prime [2, 3, 11, 449, 743] ⟨22018063, 3, [(2, 1), (3, 1), (11, 1), (449, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_449
    · exact prime_743
  · decide +kernel

theorem prime_25257413 : Nat.Prime 25257413 := by
  apply nodeValid_prime [2, 139, 45427] ⟨25257413, 2, [(2, 2), (139, 1), (45427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_45427
  · decide +kernel

theorem prime_41464373 : Nat.Prime 41464373 := by
  apply nodeValid_prime [2, 1069, 9697] ⟨41464373, 2, [(2, 2), (1069, 1), (9697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1069
    · exact prime_9697
  · decide +kernel

theorem prime_56137589 : Nat.Prime 56137589 := by
  apply nodeValid_prime [2, 13, 1079569] ⟨56137589, 2, [(2, 2), (13, 1), (1079569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1079569
  · decide +kernel

theorem prime_58045129 : Nat.Prime 58045129 := by
  apply nodeValid_prime [2, 3, 2418547] ⟨58045129, 17, [(2, 3), (3, 1), (2418547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2418547
  · decide +kernel

theorem prime_63920033 : Nat.Prime 63920033 := by
  apply nodeValid_prime [2, 11, 113, 1607] ⟨63920033, 3, [(2, 5), (11, 1), (113, 1), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
    · exact prime_1607
  · decide +kernel

theorem prime_66818957 : Nat.Prime 66818957 := by
  apply nodeValid_prime [2, 23, 367, 1979] ⟨66818957, 2, [(2, 2), (23, 1), (367, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_367
    · exact prime_1979
  · decide +kernel

theorem prime_69381397 : Nat.Prime 69381397 := by
  apply nodeValid_prime [2, 3, 7, 275323] ⟨69381397, 2, [(2, 2), (3, 2), (7, 1), (275323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_275323
  · decide +kernel

theorem prime_164443211 : Nat.Prime 164443211 := by
  apply nodeValid_prime [2, 5, 17, 41, 23593] ⟨164443211, 2, [(2, 1), (5, 1), (17, 1), (41, 1), (23593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_41
    · exact prime_23593
  · decide +kernel

theorem prime_202519819 : Nat.Prime 202519819 := by
  apply nodeValid_prime [2, 3, 29, 79, 1637] ⟨202519819, 2, [(2, 1), (3, 3), (29, 1), (79, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_79
    · exact prime_1637
  · decide +kernel

theorem prime_221010791 : Nat.Prime 221010791 := by
  apply nodeValid_prime [2, 5, 7, 11, 13, 22079] ⟨221010791, 21, [(2, 1), (5, 1), (7, 1), (11, 1), (13, 1), (22079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_22079
  · decide +kernel

theorem prime_262376159 : Nat.Prime 262376159 := by
  apply nodeValid_prime [2, 11, 127, 8537] ⟨262376159, 11, [(2, 1), (11, 2), (127, 1), (8537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_8537
  · decide +kernel

theorem prime_284405111 : Nat.Prime 284405111 := by
  apply nodeValid_prime [2, 5, 11, 19, 41, 3319] ⟨284405111, 7, [(2, 1), (5, 1), (11, 1), (19, 1), (41, 1), (3319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_41
    · exact prime_3319
  · decide +kernel

theorem prime_328886423 : Nat.Prime 328886423 := by
  apply nodeValid_prime [2, 164443211] ⟨328886423, 5, [(2, 1), (164443211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_164443211
  · decide +kernel

theorem prime_359157833 : Nat.Prime 359157833 := by
  apply nodeValid_prime [2, 11, 47, 86837] ⟨359157833, 5, [(2, 3), (11, 1), (47, 1), (86837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_86837
  · decide +kernel

theorem prime_361870699 : Nat.Prime 361870699 := by
  apply nodeValid_prime [2, 3, 7, 2837, 3037] ⟨361870699, 2, [(2, 1), (3, 1), (7, 1), (2837, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2837
    · exact prime_3037
  · decide +kernel

theorem prime_390700631 : Nat.Prime 390700631 := by
  apply nodeValid_prime [2, 5, 17, 53, 103, 421] ⟨390700631, 31, [(2, 1), (5, 1), (17, 1), (53, 1), (103, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_53
    · exact prime_103
    · exact prime_421
  · decide +kernel

theorem prime_432494333 : Nat.Prime 432494333 := by
  apply nodeValid_prime [2, 37, 2922259] ⟨432494333, 2, [(2, 2), (37, 1), (2922259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2922259
  · decide +kernel

theorem prime_566635217 : Nat.Prime 566635217 := by
  apply nodeValid_prime [2, 7, 722749] ⟨566635217, 3, [(2, 4), (7, 2), (722749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_722749
  · decide +kernel

theorem prime_718315667 : Nat.Prime 718315667 := by
  apply nodeValid_prime [2, 359157833] ⟨718315667, 2, [(2, 1), (359157833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_359157833
  · decide +kernel

theorem prime_851985929 : Nat.Prime 851985929 := by
  apply nodeValid_prime [2, 79, 211, 6389] ⟨851985929, 3, [(2, 3), (79, 1), (211, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_211
    · exact prime_6389
  · decide +kernel

theorem prime_895751663 : Nat.Prime 895751663 := by
  apply nodeValid_prime [2, 13, 43, 47, 17047] ⟨895751663, 5, [(2, 1), (13, 1), (43, 1), (47, 1), (17047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_47
    · exact prime_17047
  · decide +kernel

theorem prime_1168855981 : Nat.Prime 1168855981 := by
  apply nodeValid_prime [2, 3, 5, 421, 46273] ⟨1168855981, 2, [(2, 2), (3, 1), (5, 1), (421, 1), (46273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_421
    · exact prime_46273
  · decide +kernel

theorem prime_1439889931 : Nat.Prime 1439889931 := by
  apply nodeValid_prime [2, 3, 5, 23, 695599] ⟨1439889931, 2, [(2, 1), (3, 2), (5, 1), (23, 1), (695599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_695599
  · decide +kernel

theorem prime_1824432413 : Nat.Prime 1824432413 := by
  apply nodeValid_prime [2, 11, 41464373] ⟨1824432413, 3, [(2, 2), (11, 1), (41464373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41464373
  · decide +kernel

theorem prime_2077113959 : Nat.Prime 2077113959 := by
  apply nodeValid_prime [2, 17, 47, 1299821] ⟨2077113959, 7, [(2, 1), (17, 1), (47, 1), (1299821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_1299821
  · decide +kernel

theorem prime_2290202807 : Nat.Prime 2290202807 := by
  apply nodeValid_prime [2, 151, 587, 12919] ⟨2290202807, 5, [(2, 1), (151, 1), (587, 1), (12919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_587
    · exact prime_12919
  · decide +kernel

theorem prime_2513637227 : Nat.Prime 2513637227 := by
  apply nodeValid_prime [2, 18251, 68863] ⟨2513637227, 2, [(2, 1), (18251, 1), (68863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18251
    · exact prime_68863
  · decide +kernel

theorem prime_3154582999 : Nat.Prime 3154582999 := by
  apply nodeValid_prime [2, 3, 7, 367, 68219] ⟨3154582999, 3, [(2, 1), (3, 2), (7, 1), (367, 1), (68219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_367
    · exact prime_68219
  · decide +kernel

theorem prime_3579521849 : Nat.Prime 3579521849 := by
  apply nodeValid_prime [2, 7, 63920033] ⟨3579521849, 3, [(2, 3), (7, 1), (63920033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_63920033
  · decide +kernel

theorem prime_4635938831 : Nat.Prime 4635938831 := by
  apply nodeValid_prime [2, 5, 79, 5868277] ⟨4635938831, 17, [(2, 1), (5, 1), (79, 1), (5868277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_5868277
  · decide +kernel

theorem prime_4722770863 : Nat.Prime 4722770863 := by
  apply nodeValid_prime [2, 3, 262376159] ⟨4722770863, 6, [(2, 1), (3, 2), (262376159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_262376159
  · decide +kernel

theorem prime_9271877663 : Nat.Prime 9271877663 := by
  apply nodeValid_prime [2, 4635938831] ⟨9271877663, 5, [(2, 1), (4635938831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4635938831
  · decide +kernel

theorem prime_16616911673 : Nat.Prime 16616911673 := by
  apply nodeValid_prime [2, 2077113959] ⟨16616911673, 3, [(2, 3), (2077113959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2077113959
  · decide +kernel

theorem prime_20362661261 : Nat.Prime 20362661261 := by
  apply nodeValid_prime [2, 5, 20929, 48647] ⟨20362661261, 2, [(2, 2), (5, 1), (20929, 1), (48647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20929
    · exact prime_48647
  · decide +kernel

theorem prime_24969078223 : Nat.Prime 24969078223 := by
  apply nodeValid_prime [2, 3, 11, 113, 3347959] ⟨24969078223, 11, [(2, 1), (3, 1), (11, 1), (113, 1), (3347959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
    · exact prime_3347959
  · decide +kernel

theorem prime_28636174793 : Nat.Prime 28636174793 := by
  apply nodeValid_prime [2, 3579521849] ⟨28636174793, 3, [(2, 3), (3579521849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3579521849
  · decide +kernel

theorem prime_33584543021 : Nat.Prime 33584543021 := by
  apply nodeValid_prime [2, 5, 7, 3037, 78989] ⟨33584543021, 3, [(2, 2), (5, 1), (7, 1), (3037, 1), (78989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3037
    · exact prime_78989
  · decide +kernel

theorem prime_39880590349 : Nat.Prime 39880590349 := by
  apply nodeValid_prime [2, 3, 241, 1013, 13613] ⟨39880590349, 2, [(2, 2), (3, 1), (241, 1), (1013, 1), (13613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_1013
    · exact prime_13613
  · decide +kernel

theorem prime_66234936827 : Nat.Prime 66234936827 := by
  apply nodeValid_prime [2, 23, 1439889931] ⟨66234936827, 2, [(2, 1), (23, 1), (1439889931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1439889931
  · decide +kernel

theorem prime_67639489537 : Nat.Prime 67639489537 := by
  apply nodeValid_prime [2, 3, 22018063] ⟨67639489537, 5, [(2, 10), (3, 1), (22018063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22018063
  · decide +kernel

theorem prime_68468088497 : Nat.Prime 68468088497 := by
  apply nodeValid_prime [2, 31, 1039, 132859] ⟨68468088497, 3, [(2, 4), (31, 1), (1039, 1), (132859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1039
    · exact prime_132859
  · decide +kernel

theorem prime_68706084211 : Nat.Prime 68706084211 := by
  apply nodeValid_prime [2, 3, 5, 2290202807] ⟨68706084211, 2, [(2, 1), (3, 1), (5, 1), (2290202807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2290202807
  · decide +kernel

theorem prime_203272336511 : Nat.Prime 203272336511 := by
  apply nodeValid_prime [2, 5, 47, 432494333] ⟨203272336511, 17, [(2, 1), (5, 1), (47, 1), (432494333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_432494333
  · decide +kernel

theorem prime_204691953029 : Nat.Prime 204691953029 := by
  apply nodeValid_prime [2, 569, 2221, 40493] ⟨204691953029, 2, [(2, 2), (569, 1), (2221, 1), (40493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_569
    · exact prime_2221
    · exact prime_40493
  · decide +kernel

theorem prime_205761047483 : Nat.Prime 205761047483 := by
  apply nodeValid_prime [2, 229, 277, 1621877] ⟨205761047483, 2, [(2, 1), (229, 1), (277, 1), (1621877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_277
    · exact prime_1621877
  · decide +kernel

theorem prime_395321471057 : Nat.Prime 395321471057 := by
  apply nodeValid_prime [2, 29, 851985929] ⟨395321471057, 3, [(2, 4), (29, 1), (851985929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_851985929
  · decide +kernel

theorem prime_395321480447 : Nat.Prime 395321480447 := by
  apply nodeValid_prime [2, 601, 328886423] ⟨395321480447, 5, [(2, 1), (601, 1), (328886423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_328886423
  · decide +kernel

theorem prime_395321480797 : Nat.Prime 395321480797 := by
  apply nodeValid_prime [2, 3, 11, 9463, 28771] ⟨395321480797, 2, [(2, 2), (3, 1), (11, 2), (9463, 1), (28771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9463
    · exact prime_28771
  · decide +kernel

theorem prime_396016692697 : Nat.Prime 396016692697 := by
  apply nodeValid_prime [2, 3, 29, 599, 316633] ⟨396016692697, 13, [(2, 3), (3, 2), (29, 1), (599, 1), (316633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_599
    · exact prime_316633
  · decide +kernel

theorem prime_396016692991 : Nat.Prime 396016692991 := by
  apply nodeValid_prime [2, 3, 5, 5087, 2594959] ⟨396016692991, 3, [(2, 1), (3, 1), (5, 1), (5087, 1), (2594959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5087
    · exact prime_2594959
  · decide +kernel

theorem prime_396016698949 : Nat.Prime 396016698949 := by
  apply nodeValid_prime [2, 3, 13, 127, 2393, 8353] ⟨396016698949, 2, [(2, 2), (3, 1), (13, 1), (127, 1), (2393, 1), (8353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_127
    · exact prime_2393
    · exact prime_8353
  · decide +kernel

theorem prime_396712752071 : Nat.Prime 396712752071 := by
  apply nodeValid_prime [2, 5, 19, 809, 2580917] ⟨396712752071, 11, [(2, 1), (5, 1), (19, 1), (809, 1), (2580917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_809
    · exact prime_2580917
  · decide +kernel

theorem prime_396712752493 : Nat.Prime 396712752493 := by
  apply nodeValid_prime [2, 3, 7, 4722770863] ⟨396712752493, 5, [(2, 2), (3, 1), (7, 1), (4722770863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4722770863
  · decide +kernel

theorem prime_396712754047 : Nat.Prime 396712754047 := by
  apply nodeValid_prime [2, 3, 7, 19, 2141, 11057] ⟨396712754047, 3, [(2, 1), (3, 2), (7, 2), (19, 1), (2141, 1), (11057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_2141
    · exact prime_11057
  · decide +kernel

theorem prime_397409619661 : Nat.Prime 397409619661 := by
  apply nodeValid_prime [2, 3, 5, 487, 1433, 9491] ⟨397409619661, 2, [(2, 2), (3, 1), (5, 1), (487, 1), (1433, 1), (9491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_487
    · exact prime_1433
    · exact prime_9491
  · decide +kernel

theorem prime_397409620963 : Nat.Prime 397409620963 := by
  apply nodeValid_prime [2, 3, 66234936827] ⟨397409620963, 2, [(2, 1), (3, 1), (66234936827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66234936827
  · decide +kernel

theorem prime_397409632889 : Nat.Prime 397409632889 := by
  apply nodeValid_prime [2, 47, 257, 4112609] ⟨397409632889, 3, [(2, 3), (47, 1), (257, 1), (4112609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_257
    · exact prime_4112609
  · decide +kernel

theorem prime_398107343707 : Nat.Prime 398107343707 := by
  apply nodeValid_prime [2, 3, 37, 71, 25257413] ⟨398107343707, 2, [(2, 1), (3, 1), (37, 1), (71, 1), (25257413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_25257413
  · decide +kernel

theorem prime_398107344703 : Nat.Prime 398107344703 := by
  apply nodeValid_prime [2, 3, 53, 673, 1860193] ⟨398107344703, 3, [(2, 1), (3, 1), (53, 1), (673, 1), (1860193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_673
    · exact prime_1860193
  · decide +kernel

theorem prime_398107345807 : Nat.Prime 398107345807 := by
  apply nodeValid_prime [2, 3, 331, 66818957] ⟨398107345807, 3, [(2, 1), (3, 2), (331, 1), (66818957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
    · exact prime_66818957
  · decide +kernel

theorem prime_398805880153 : Nat.Prime 398805880153 := by
  apply nodeValid_prime [2, 3, 16616911673] ⟨398805880153, 10, [(2, 3), (3, 1), (16616911673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16616911673
  · decide +kernel

theorem prime_398805903491 : Nat.Prime 398805903491 := by
  apply nodeValid_prime [2, 5, 39880590349] ⟨398805903491, 2, [(2, 1), (5, 1), (39880590349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_39880590349
  · decide +kernel

theorem prime_398805903541 : Nat.Prime 398805903541 := by
  apply nodeValid_prime [2, 3, 5, 11, 1229, 54629] ⟨398805903541, 10, [(2, 2), (3, 3), (5, 1), (11, 1), (1229, 1), (54629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1229
    · exact prime_54629
  · decide +kernel

theorem prime_399505241699 : Nat.Prime 399505241699 := by
  apply nodeValid_prime [2, 223, 895751663] ⟨399505241699, 2, [(2, 1), (223, 1), (895751663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_895751663
  · decide +kernel

theorem prime_399505251569 : Nat.Prime 399505251569 := by
  apply nodeValid_prime [2, 24969078223] ⟨399505251569, 3, [(2, 4), (24969078223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24969078223
  · decide +kernel

theorem prime_399505251697 : Nat.Prime 399505251697 := by
  apply nodeValid_prime [2, 3, 23, 361870699] ⟨399505251697, 5, [(2, 4), (3, 1), (23, 1), (361870699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_361870699
  · decide +kernel

theorem prime_400205434477 : Nat.Prime 400205434477 := by
  apply nodeValid_prime [2, 3, 10891, 3062203] ⟨400205434477, 2, [(2, 2), (3, 1), (10891, 1), (3062203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10891
    · exact prime_3062203
  · decide +kernel

theorem prime_400205461849 : Nat.Prime 400205461849 := by
  apply nodeValid_prime [2, 3, 31, 761, 706847] ⟨400205461849, 11, [(2, 3), (3, 1), (31, 1), (761, 1), (706847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_761
    · exact prime_706847
  · decide +kernel

theorem prime_400205463001 : Nat.Prime 400205463001 := by
  apply nodeValid_prime [2, 3, 5, 7, 19057403] ⟨400205463001, 17, [(2, 3), (3, 1), (5, 3), (7, 1), (19057403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19057403
  · decide +kernel

theorem prime_400906447103 : Nat.Prime 400906447103 := by
  apply nodeValid_prime [2, 7, 28636174793] ⟨400906447103, 5, [(2, 1), (7, 1), (28636174793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_28636174793
  · decide +kernel

theorem prime_400906447889 : Nat.Prime 400906447889 := by
  apply nodeValid_prime [2, 29, 569, 809, 1877] ⟨400906447889, 3, [(2, 4), (29, 1), (569, 1), (809, 1), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_569
    · exact prime_809
    · exact prime_1877
  · decide +kernel

theorem prime_400906454891 : Nat.Prime 400906454891 := by
  apply nodeValid_prime [2, 5, 23, 21061, 82763] ⟨400906454891, 2, [(2, 1), (5, 1), (23, 1), (21061, 1), (82763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_21061
    · exact prime_82763
  · decide +kernel

theorem prime_401608308247 : Nat.Prime 401608308247 := by
  apply nodeValid_prime [2, 3, 26731, 2504011] ⟨401608308247, 3, [(2, 1), (3, 1), (26731, 1), (2504011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26731
    · exact prime_2504011
  · decide +kernel

theorem prime_401608311707 : Nat.Prime 401608311707 := by
  apply nodeValid_prime [2, 7, 73, 56137589] ⟨401608311707, 2, [(2, 1), (7, 2), (73, 1), (56137589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_56137589
  · decide +kernel

theorem prime_402310994927 : Nat.Prime 402310994927 := by
  apply nodeValid_prime [2, 25117, 8008739] ⟨402310994927, 5, [(2, 1), (25117, 1), (8008739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_25117
    · exact prime_8008739
  · decide +kernel

theorem prime_402311001353 : Nat.Prime 402311001353 := by
  apply nodeValid_prime [2, 13, 1549, 2497337] ⟨402311001353, 3, [(2, 3), (13, 1), (1549, 1), (2497337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1549
    · exact prime_2497337
  · decide +kernel

theorem prime_402311004071 : Nat.Prime 402311004071 := by
  apply nodeValid_prime [2, 5, 71, 566635217] ⟨402311004071, 7, [(2, 1), (5, 1), (71, 1), (566635217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_566635217
  · decide +kernel

theorem prime_403014439811 : Nat.Prime 403014439811 := by
  apply nodeValid_prime [2, 5, 199, 202519819] ⟨403014439811, 2, [(2, 1), (5, 1), (199, 1), (202519819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_202519819
  · decide +kernel

theorem prime_403014439897 : Nat.Prime 403014439897 := by
  apply nodeValid_prime [2, 3, 23, 73, 1289, 7759] ⟨403014439897, 5, [(2, 3), (3, 1), (23, 1), (73, 1), (1289, 1), (7759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_73
    · exact prime_1289
    · exact prime_7759
  · decide +kernel

theorem prime_403014516253 : Nat.Prime 403014516253 := by
  apply nodeValid_prime [2, 3, 33584543021] ⟨403014516253, 6, [(2, 2), (3, 1), (33584543021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33584543021
  · decide +kernel

theorem prime_403718875447 : Nat.Prime 403718875447 := by
  apply nodeValid_prime [2, 3, 37, 109, 149, 111973] ⟨403718875447, 3, [(2, 1), (3, 1), (37, 1), (109, 1), (149, 1), (111973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_109
    · exact prime_149
    · exact prime_111973
  · decide +kernel

theorem prime_403718879107 : Nat.Prime 403718879107 := by
  apply nodeValid_prime [2, 3, 43, 167, 1041119] ⟨403718879107, 3, [(2, 1), (3, 3), (43, 1), (167, 1), (1041119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_167
    · exact prime_1041119
  · decide +kernel

theorem prime_403718879929 : Nat.Prime 403718879929 := by
  apply nodeValid_prime [2, 3, 7, 13, 103, 138053] ⟨403718879929, 17, [(2, 3), (3, 1), (7, 1), (13, 2), (103, 1), (138053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_103
    · exact prime_138053
  · decide +kernel

theorem prime_404424067843 : Nat.Prime 404424067843 := by
  apply nodeValid_prime [2, 3, 79, 284405111] ⟨404424067843, 3, [(2, 1), (3, 2), (79, 1), (284405111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_284405111
  · decide +kernel

theorem prime_404424169427 : Nat.Prime 404424169427 := by
  apply nodeValid_prime [2, 173, 1168855981] ⟨404424169427, 2, [(2, 1), (173, 1), (1168855981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_1168855981
  · decide +kernel

theorem prime_404424169819 : Nat.Prime 404424169819 := by
  apply nodeValid_prime [2, 3, 19, 263, 13488899] ⟨404424169819, 2, [(2, 1), (3, 1), (19, 1), (263, 1), (13488899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_263
    · exact prime_13488899
  · decide +kernel

theorem prime_405130036147 : Nat.Prime 405130036147 := by
  apply nodeValid_prime [2, 3, 11, 347, 17689723] ⟨405130036147, 2, [(2, 1), (3, 1), (11, 1), (347, 1), (17689723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_347
    · exact prime_17689723
  · decide +kernel

theorem prime_405130036189 : Nat.Prime 405130036189 := by
  apply nodeValid_prime [2, 3, 47, 718315667] ⟨405130036189, 2, [(2, 2), (3, 1), (47, 1), (718315667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_718315667
  · decide +kernel

theorem prime_405130094857 : Nat.Prime 405130094857 := by
  apply nodeValid_prime [2, 3, 2393, 783787] ⟨405130094857, 5, [(2, 3), (3, 3), (2393, 1), (783787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2393
    · exact prime_783787
  · decide +kernel

theorem prime_405836936969 : Nat.Prime 405836936969 := by
  apply nodeValid_prime [2, 23, 37, 59, 149, 6781] ⟨405836936969, 3, [(2, 3), (23, 1), (37, 1), (59, 1), (149, 1), (6781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_59
    · exact prime_149
    · exact prime_6781
  · decide +kernel

theorem prime_405836937223 : Nat.Prime 405836937223 := by
  apply nodeValid_prime [2, 3, 67639489537] ⟨405836937223, 3, [(2, 1), (3, 1), (67639489537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67639489537
  · decide +kernel

theorem prime_405836965537 : Nat.Prime 405836965537 := by
  apply nodeValid_prime [2, 3, 2311, 1829281] ⟨405836965537, 5, [(2, 5), (3, 1), (2311, 1), (1829281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2311
    · exact prime_1829281
  · decide +kernel

theorem prime_406544671541 : Nat.Prime 406544671541 := by
  apply nodeValid_prime [2, 5, 7, 53, 1543, 35509] ⟨406544671541, 3, [(2, 2), (5, 1), (7, 1), (53, 1), (1543, 1), (35509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_1543
    · exact prime_35509
  · decide +kernel

theorem prime_406544672197 : Nat.Prime 406544672197 := by
  apply nodeValid_prime [2, 3, 13, 269, 283, 11411] ⟨406544672197, 5, [(2, 2), (3, 2), (13, 1), (269, 1), (283, 1), (11411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_269
    · exact prime_283
    · exact prime_11411
  · decide +kernel

theorem prime_406544673023 : Nat.Prime 406544673023 := by
  apply nodeValid_prime [2, 203272336511] ⟨406544673023, 5, [(2, 1), (203272336511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_203272336511
  · decide +kernel

theorem prime_407253225221 : Nat.Prime 407253225221 := by
  apply nodeValid_prime [2, 5, 20362661261] ⟨407253225221, 3, [(2, 2), (5, 1), (20362661261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20362661261
  · decide +kernel

theorem prime_407253227443 : Nat.Prime 407253227443 := by
  apply nodeValid_prime [2, 3, 47, 4391, 328891] ⟨407253227443, 2, [(2, 1), (3, 1), (47, 1), (4391, 1), (328891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_4391
    · exact prime_328891
  · decide +kernel

theorem prime_407253230149 : Nat.Prime 407253230149 := by
  apply nodeValid_prime [2, 3, 71, 241, 1983389] ⟨407253230149, 6, [(2, 2), (3, 1), (71, 1), (241, 1), (1983389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_241
    · exact prime_1983389
  · decide +kernel

theorem prime_407962614361 : Nat.Prime 407962614361 := by
  apply nodeValid_prime [2, 3, 5, 7, 69381397] ⟨407962614361, 23, [(2, 3), (3, 1), (5, 1), (7, 2), (69381397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_69381397
  · decide +kernel

theorem prime_407962617131 : Nat.Prime 407962617131 := by
  apply nodeValid_prime [2, 5, 56569, 721177] ⟨407962617131, 2, [(2, 1), (5, 1), (56569, 1), (721177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_56569
    · exact prime_721177
  · decide +kernel

theorem prime_407962617173 : Nat.Prime 407962617173 := by
  apply nodeValid_prime [2, 11, 9271877663] ⟨407962617173, 2, [(2, 2), (11, 1), (9271877663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9271877663
  · decide +kernel

theorem prime_408672843283 : Nat.Prime 408672843283 := by
  apply nodeValid_prime [2, 3, 11, 991, 2082749] ⟨408672843283, 2, [(2, 1), (3, 2), (11, 1), (991, 1), (2082749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_991
    · exact prime_2082749
  · decide +kernel

theorem prime_408672860027 : Nat.Prime 408672860027 := by
  apply nodeValid_prime [2, 523, 390700631] ⟨408672860027, 2, [(2, 1), (523, 1), (390700631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_523
    · exact prime_390700631
  · decide +kernel

theorem prime_408672860513 : Nat.Prime 408672860513 := by
  apply nodeValid_prime [2, 7, 1824432413] ⟨408672860513, 3, [(2, 5), (7, 1), (1824432413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1824432413
  · decide +kernel

theorem prime_409383906059 : Nat.Prime 409383906059 := by
  apply nodeValid_prime [2, 204691953029] ⟨409383906059, 2, [(2, 1), (204691953029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_204691953029
  · decide +kernel

theorem prime_409383968359 : Nat.Prime 409383968359 := by
  apply nodeValid_prime [2, 3, 41, 3643, 456811] ⟨409383968359, 3, [(2, 1), (3, 1), (41, 1), (3643, 1), (456811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_3643
    · exact prime_456811
  · decide +kernel

theorem prime_409383968509 : Nat.Prime 409383968509 := by
  apply nodeValid_prime [2, 3, 31, 103, 395719] ⟨409383968509, 2, [(2, 2), (3, 4), (31, 1), (103, 1), (395719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_103
    · exact prime_395719
  · decide +kernel

theorem prime_410095789657 : Nat.Prime 410095789657 := by
  apply nodeValid_prime [2, 3, 7, 2473, 987079] ⟨410095789657, 5, [(2, 3), (3, 1), (7, 1), (2473, 1), (987079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2473
    · exact prime_987079
  · decide +kernel

theorem prime_410095789871 : Nat.Prime 410095789871 := by
  apply nodeValid_prime [2, 5, 13, 3154582999] ⟨410095789871, 11, [(2, 1), (5, 1), (13, 1), (3154582999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_3154582999
  · decide +kernel

theorem prime_410095799977 : Nat.Prime 410095799977 := by
  apply nodeValid_prime [2, 3, 887, 19264177] ⟨410095799977, 5, [(2, 3), (3, 1), (887, 1), (19264177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_887
    · exact prime_19264177
  · decide +kernel

theorem prime_410808529577 : Nat.Prime 410808529577 := by
  apply nodeValid_prime [2, 149119, 344363] ⟨410808529577, 3, [(2, 3), (149119, 1), (344363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149119
    · exact prime_344363
  · decide +kernel

theorem prime_410808530983 : Nat.Prime 410808530983 := by
  apply nodeValid_prime [2, 3, 68468088497] ⟨410808530983, 3, [(2, 1), (3, 1), (68468088497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_68468088497
  · decide +kernel

theorem prime_411522091553 : Nat.Prime 411522091553 := by
  apply nodeValid_prime [2, 11, 13, 17, 5290031] ⟨411522091553, 3, [(2, 5), (11, 1), (13, 1), (17, 1), (5290031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_5290031
  · decide +kernel

theorem prime_411522092843 : Nat.Prime 411522092843 := by
  apply nodeValid_prime [2, 7, 19, 221010791] ⟨411522092843, 5, [(2, 1), (7, 2), (19, 1), (221010791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_221010791
  · decide +kernel

theorem prime_411522094967 : Nat.Prime 411522094967 := by
  apply nodeValid_prime [2, 205761047483] ⟨411522094967, 5, [(2, 1), (205761047483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_205761047483
  · decide +kernel

theorem prime_412236505229 : Nat.Prime 412236505229 := by
  apply nodeValid_prime [2, 41, 2513637227] ⟨412236505229, 2, [(2, 2), (41, 1), (2513637227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_2513637227
  · decide +kernel

theorem prime_412236505267 : Nat.Prime 412236505267 := by
  apply nodeValid_prime [2, 3, 68706084211] ⟨412236505267, 13, [(2, 1), (3, 1), (68706084211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_68706084211
  · decide +kernel

theorem prime_412236506159 : Nat.Prime 412236506159 := by
  apply nodeValid_prime [2, 53, 67, 58045129] ⟨412236506159, 7, [(2, 1), (53, 1), (67, 1), (58045129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_67
    · exact prime_58045129
  · decide +kernel

end Sude.Lucas.Generated
