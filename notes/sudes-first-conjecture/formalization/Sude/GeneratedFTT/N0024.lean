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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1723 : Nat.Prime 1723 := by
  apply nodeValid_prime [2, 3, 7, 41] ⟨1723, 3, [(2, 1), (3, 1), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_1801 : Nat.Prime 1801 := by
  apply nodeValid_prime [2, 3, 5] ⟨1801, 11, [(2, 3), (3, 2), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_1999 : Nat.Prime 1999 := by
  apply nodeValid_prime [2, 3, 37] ⟨1999, 3, [(2, 1), (3, 3), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_3631 : Nat.Prime 3631 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨3631, 15, [(2, 1), (3, 1), (5, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_4649 : Nat.Prime 4649 := by
  apply nodeValid_prime [2, 7, 83] ⟨4649, 3, [(2, 3), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_4951 : Nat.Prime 4951 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨4951, 6, [(2, 1), (3, 2), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_5051 : Nat.Prime 5051 := by
  apply nodeValid_prime [2, 5, 101] ⟨5051, 2, [(2, 1), (5, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_5393 : Nat.Prime 5393 := by
  apply nodeValid_prime [2, 337] ⟨5393, 3, [(2, 4), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_337
  · decide +kernel

theorem prime_6451 : Nat.Prime 6451 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨6451, 3, [(2, 1), (3, 1), (5, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_6607 : Nat.Prime 6607 := by
  apply nodeValid_prime [2, 3, 367] ⟨6607, 3, [(2, 1), (3, 2), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
  · decide +kernel

theorem prime_6871 : Nat.Prime 6871 := by
  apply nodeValid_prime [2, 3, 5, 229] ⟨6871, 3, [(2, 1), (3, 1), (5, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
  · decide +kernel

theorem prime_6911 : Nat.Prime 6911 := by
  apply nodeValid_prime [2, 5, 691] ⟨6911, 7, [(2, 1), (5, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_691
  · decide +kernel

theorem prime_6949 : Nat.Prime 6949 := by
  apply nodeValid_prime [2, 3, 193] ⟨6949, 2, [(2, 2), (3, 2), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
  · decide +kernel

theorem prime_7487 : Nat.Prime 7487 := by
  apply nodeValid_prime [2, 19, 197] ⟨7487, 5, [(2, 1), (19, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_197
  · decide +kernel

theorem prime_10937 : Nat.Prime 10937 := by
  apply nodeValid_prime [2, 1367] ⟨10937, 3, [(2, 3), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1367
  · decide +kernel

theorem prime_12097 : Nat.Prime 12097 := by
  apply nodeValid_prime [2, 3, 7] ⟨12097, 5, [(2, 6), (3, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_16193 : Nat.Prime 16193 := by
  apply nodeValid_prime [2, 11, 23] ⟨16193, 5, [(2, 6), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_16673 : Nat.Prime 16673 := by
  apply nodeValid_prime [2, 521] ⟨16673, 3, [(2, 5), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_521
  · decide +kernel

theorem prime_16843 : Nat.Prime 16843 := by
  apply nodeValid_prime [2, 3, 7, 401] ⟨16843, 2, [(2, 1), (3, 1), (7, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_401
  · decide +kernel

theorem prime_18313 : Nat.Prime 18313 := by
  apply nodeValid_prime [2, 3, 7, 109] ⟨18313, 10, [(2, 3), (3, 1), (7, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
  · decide +kernel

theorem prime_19051 : Nat.Prime 19051 := by
  apply nodeValid_prime [2, 3, 5, 127] ⟨19051, 2, [(2, 1), (3, 1), (5, 2), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_19403 : Nat.Prime 19403 := by
  apply nodeValid_prime [2, 89, 109] ⟨19403, 2, [(2, 1), (89, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_109
  · decide +kernel

theorem prime_21577 : Nat.Prime 21577 := by
  apply nodeValid_prime [2, 3, 29, 31] ⟨21577, 5, [(2, 3), (3, 1), (29, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
  · decide +kernel

theorem prime_21817 : Nat.Prime 21817 := by
  apply nodeValid_prime [2, 3, 101] ⟨21817, 7, [(2, 3), (3, 3), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_24379 : Nat.Prime 24379 := by
  apply nodeValid_prime [2, 3, 17, 239] ⟨24379, 2, [(2, 1), (3, 1), (17, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_239
  · decide +kernel

theorem prime_24967 : Nat.Prime 24967 := by
  apply nodeValid_prime [2, 3, 19, 73] ⟨24967, 3, [(2, 1), (3, 2), (19, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_73
  · decide +kernel

theorem prime_25087 : Nat.Prime 25087 := by
  apply nodeValid_prime [2, 3, 37, 113] ⟨25087, 3, [(2, 1), (3, 1), (37, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_113
  · decide +kernel

theorem prime_25561 : Nat.Prime 25561 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨25561, 11, [(2, 3), (3, 2), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_26993 : Nat.Prime 26993 := by
  apply nodeValid_prime [2, 7, 241] ⟨26993, 3, [(2, 4), (7, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_241
  · decide +kernel

theorem prime_30449 : Nat.Prime 30449 := by
  apply nodeValid_prime [2, 11, 173] ⟨30449, 3, [(2, 4), (11, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_173
  · decide +kernel

theorem prime_35107 : Nat.Prime 35107 := by
  apply nodeValid_prime [2, 3, 5851] ⟨35107, 2, [(2, 1), (3, 1), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5851
  · decide +kernel

theorem prime_36073 : Nat.Prime 36073 := by
  apply nodeValid_prime [2, 3, 167] ⟨36073, 5, [(2, 3), (3, 3), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
  · decide +kernel

theorem prime_45341 : Nat.Prime 45341 := by
  apply nodeValid_prime [2, 5, 2267] ⟨45341, 2, [(2, 2), (5, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2267
  · decide +kernel

theorem prime_53987 : Nat.Prime 53987 := by
  apply nodeValid_prime [2, 26993] ⟨53987, 2, [(2, 1), (26993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26993
  · decide +kernel

theorem prime_54869 : Nat.Prime 54869 := by
  apply nodeValid_prime [2, 11, 29, 43] ⟨54869, 2, [(2, 2), (11, 1), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_60899 : Nat.Prime 60899 := by
  apply nodeValid_prime [2, 30449] ⟨60899, 2, [(2, 1), (30449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30449
  · decide +kernel

theorem prime_64969 : Nat.Prime 64969 := by
  apply nodeValid_prime [2, 3, 2707] ⟨64969, 13, [(2, 3), (3, 1), (2707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2707
  · decide +kernel

theorem prime_71237 : Nat.Prime 71237 := by
  apply nodeValid_prime [2, 11, 1619] ⟨71237, 2, [(2, 2), (11, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1619
  · decide +kernel

theorem prime_75503 : Nat.Prime 75503 := by
  apply nodeValid_prime [2, 7, 5393] ⟨75503, 5, [(2, 1), (7, 1), (5393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5393
  · decide +kernel

theorem prime_83933 : Nat.Prime 83933 := by
  apply nodeValid_prime [2, 20983] ⟨83933, 2, [(2, 2), (20983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20983
  · decide +kernel

theorem prime_88037 : Nat.Prime 88037 := by
  apply nodeValid_prime [2, 13, 1693] ⟨88037, 2, [(2, 2), (13, 1), (1693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1693
  · decide +kernel

theorem prime_94811 : Nat.Prime 94811 := by
  apply nodeValid_prime [2, 5, 19, 499] ⟨94811, 2, [(2, 1), (5, 1), (19, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_499
  · decide +kernel

theorem prime_115343 : Nat.Prime 115343 := by
  apply nodeValid_prime [2, 101, 571] ⟨115343, 5, [(2, 1), (101, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_571
  · decide +kernel

theorem prime_133691 : Nat.Prime 133691 := by
  apply nodeValid_prime [2, 5, 29, 461] ⟨133691, 2, [(2, 1), (5, 1), (29, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_461
  · decide +kernel

theorem prime_172597 : Nat.Prime 172597 := by
  apply nodeValid_prime [2, 3, 19, 757] ⟨172597, 2, [(2, 2), (3, 1), (19, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_757
  · decide +kernel

theorem prime_181837 : Nat.Prime 181837 := by
  apply nodeValid_prime [2, 3, 5051] ⟨181837, 5, [(2, 2), (3, 2), (5051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5051
  · decide +kernel

theorem prime_184997 : Nat.Prime 184997 := by
  apply nodeValid_prime [2, 7, 6607] ⟨184997, 2, [(2, 2), (7, 1), (6607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6607
  · decide +kernel

theorem prime_185951 : Nat.Prime 185951 := by
  apply nodeValid_prime [2, 5, 3719] ⟨185951, 17, [(2, 1), (5, 2), (3719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3719
  · decide +kernel

theorem prime_195809 : Nat.Prime 195809 := by
  apply nodeValid_prime [2, 29, 211] ⟨195809, 3, [(2, 5), (29, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_211
  · decide +kernel

theorem prime_217747 : Nat.Prime 217747 := by
  apply nodeValid_prime [2, 3, 12097] ⟨217747, 2, [(2, 1), (3, 2), (12097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12097
  · decide +kernel

theorem prime_218401 : Nat.Prime 218401 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨218401, 22, [(2, 5), (3, 1), (5, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_279127 : Nat.Prime 279127 := by
  apply nodeValid_prime [2, 3, 1723] ⟨279127, 5, [(2, 1), (3, 4), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1723
  · decide +kernel

theorem prime_297061 : Nat.Prime 297061 := by
  apply nodeValid_prime [2, 3, 5, 4951] ⟨297061, 2, [(2, 2), (3, 1), (5, 1), (4951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4951
  · decide +kernel

theorem prime_344483 : Nat.Prime 344483 := by
  apply nodeValid_prime [2, 41, 4201] ⟨344483, 2, [(2, 1), (41, 1), (4201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_4201
  · decide +kernel

theorem prime_363751 : Nat.Prime 363751 := by
  apply nodeValid_prime [2, 3, 5, 97] ⟨363751, 3, [(2, 1), (3, 1), (5, 4), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_416503 : Nat.Prime 416503 := by
  apply nodeValid_prime [2, 3, 857] ⟨416503, 3, [(2, 1), (3, 5), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_857
  · decide +kernel

theorem prime_471439 : Nat.Prime 471439 := by
  apply nodeValid_prime [2, 3, 11, 2381] ⟨471439, 3, [(2, 1), (3, 2), (11, 1), (2381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2381
  · decide +kernel

theorem prime_476107 : Nat.Prime 476107 := by
  apply nodeValid_prime [2, 3, 73, 1087] ⟨476107, 2, [(2, 1), (3, 1), (73, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_1087
  · decide +kernel

theorem prime_569897 : Nat.Prime 569897 := by
  apply nodeValid_prime [2, 71237] ⟨569897, 3, [(2, 3), (71237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71237
  · decide +kernel

theorem prime_718121 : Nat.Prime 718121 := by
  apply nodeValid_prime [2, 5, 13, 1381] ⟨718121, 3, [(2, 3), (5, 1), (13, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1381
  · decide +kernel

theorem prime_853733 : Nat.Prime 853733 := by
  apply nodeValid_prime [2, 11, 19403] ⟨853733, 2, [(2, 2), (11, 1), (19403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19403
  · decide +kernel

theorem prime_857821 : Nat.Prime 857821 := by
  apply nodeValid_prime [2, 3, 5, 17, 29] ⟨857821, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_881779 : Nat.Prime 881779 := by
  apply nodeValid_prime [2, 3, 281, 523] ⟨881779, 2, [(2, 1), (3, 1), (281, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_523
  · decide +kernel

theorem prime_934543 : Nat.Prime 934543 := by
  apply nodeValid_prime [2, 3, 7, 7417] ⟨934543, 7, [(2, 1), (3, 2), (7, 1), (7417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7417
  · decide +kernel

theorem prime_1221079 : Nat.Prime 1221079 := by
  apply nodeValid_prime [2, 3, 113, 1801] ⟨1221079, 3, [(2, 1), (3, 1), (113, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_1801
  · decide +kernel

theorem prime_1404763 : Nat.Prime 1404763 := by
  apply nodeValid_prime [2, 3, 257, 911] ⟨1404763, 3, [(2, 1), (3, 1), (257, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_911
  · decide +kernel

theorem prime_1863181 : Nat.Prime 1863181 := by
  apply nodeValid_prime [2, 3, 5, 11, 941] ⟨1863181, 10, [(2, 2), (3, 2), (5, 1), (11, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_941
  · decide +kernel

theorem prime_1904429 : Nat.Prime 1904429 := by
  apply nodeValid_prime [2, 476107] ⟨1904429, 2, [(2, 2), (476107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_476107
  · decide +kernel

theorem prime_2281711 : Nat.Prime 2281711 := by
  apply nodeValid_prime [2, 3, 5, 19, 4003] ⟨2281711, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_4003
  · decide +kernel

theorem prime_2718109 : Nat.Prime 2718109 := by
  apply nodeValid_prime [2, 3, 75503] ⟨2718109, 2, [(2, 2), (3, 2), (75503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75503
  · decide +kernel

theorem prime_3123623 : Nat.Prime 3123623 := by
  apply nodeValid_prime [2, 31, 83, 607] ⟨3123623, 5, [(2, 1), (31, 1), (83, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_83
    · exact prime_607
  · decide +kernel

theorem prime_3485171 : Nat.Prime 3485171 := by
  apply nodeValid_prime [2, 5, 13, 17, 19, 83] ⟨3485171, 2, [(2, 1), (5, 1), (13, 1), (17, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_3581041 : Nat.Prime 3581041 := by
  apply nodeValid_prime [2, 3, 5, 43, 347] ⟨3581041, 11, [(2, 4), (3, 1), (5, 1), (43, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_347
  · decide +kernel

theorem prime_5948477 : Nat.Prime 5948477 := by
  apply nodeValid_prime [2, 61, 24379] ⟨5948477, 2, [(2, 2), (61, 1), (24379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_24379
  · decide +kernel

theorem prime_6889661 : Nat.Prime 6889661 := by
  apply nodeValid_prime [2, 5, 344483] ⟨6889661, 2, [(2, 2), (5, 1), (344483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_344483
  · decide +kernel

theorem prime_9996073 : Nat.Prime 9996073 := by
  apply nodeValid_prime [2, 3, 416503] ⟨9996073, 5, [(2, 3), (3, 1), (416503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_416503
  · decide +kernel

theorem prime_10009471 : Nat.Prime 10009471 := by
  apply nodeValid_prime [2, 3, 5, 109, 3061] ⟨10009471, 3, [(2, 1), (3, 1), (5, 1), (109, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_3061
  · decide +kernel

theorem prime_11749613 : Nat.Prime 11749613 := by
  apply nodeValid_prime [2, 7, 151, 397] ⟨11749613, 2, [(2, 2), (7, 2), (151, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_151
    · exact prime_397
  · decide +kernel

theorem prime_12636983 : Nat.Prime 12636983 := by
  apply nodeValid_prime [2, 23, 29, 9473] ⟨12636983, 5, [(2, 1), (23, 1), (29, 1), (9473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_9473
  · decide +kernel

theorem prime_15996037 : Nat.Prime 15996037 := by
  apply nodeValid_prime [2, 3, 7, 53, 3593] ⟨15996037, 11, [(2, 2), (3, 1), (7, 1), (53, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_3593
  · decide +kernel

theorem prime_21837443 : Nat.Prime 21837443 := by
  apply nodeValid_prime [2, 11, 23, 103, 419] ⟨21837443, 2, [(2, 1), (11, 1), (23, 1), (103, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_103
    · exact prime_419
  · decide +kernel

theorem prime_25273967 : Nat.Prime 25273967 := by
  apply nodeValid_prime [2, 12636983] ⟨25273967, 5, [(2, 1), (12636983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12636983
  · decide +kernel

theorem prime_25488299 : Nat.Prime 25488299 := by
  apply nodeValid_prime [2, 11, 571, 2029] ⟨25488299, 2, [(2, 1), (11, 1), (571, 1), (2029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_571
    · exact prime_2029
  · decide +kernel

theorem prime_31362119 : Nat.Prime 31362119 := by
  apply nodeValid_prime [2, 2269, 6911] ⟨31362119, 19, [(2, 1), (2269, 1), (6911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2269
    · exact prime_6911
  · decide +kernel

theorem prime_36504271 : Nat.Prime 36504271 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 241] ⟨36504271, 3, [(2, 1), (3, 4), (5, 1), (11, 1), (17, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_241
  · decide +kernel

theorem prime_40959689 : Nat.Prime 40959689 := by
  apply nodeValid_prime [2, 7, 11, 23, 59] ⟨40959689, 3, [(2, 3), (7, 3), (11, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_51786043 : Nat.Prime 51786043 := by
  apply nodeValid_prime [2, 3, 7, 11, 67, 239] ⟨51786043, 5, [(2, 1), (3, 1), (7, 2), (11, 1), (67, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_67
    · exact prime_239
  · decide +kernel

theorem prime_77953427 : Nat.Prime 77953427 := by
  apply nodeValid_prime [2, 179, 217747] ⟨77953427, 2, [(2, 1), (179, 1), (217747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_217747
  · decide +kernel

theorem prime_91043531 : Nat.Prime 91043531 := by
  apply nodeValid_prime [2, 5, 83, 229, 479] ⟨91043531, 2, [(2, 1), (5, 1), (83, 1), (229, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_229
    · exact prime_479
  · decide +kernel

theorem prime_146906887 : Nat.Prime 146906887 := by
  apply nodeValid_prime [2, 3, 7, 191, 18313] ⟨146906887, 5, [(2, 1), (3, 1), (7, 1), (191, 1), (18313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_191
    · exact prime_18313
  · decide +kernel

theorem prime_163246549 : Nat.Prime 163246549 := by
  apply nodeValid_prime [2, 3, 23, 79, 7487] ⟨163246549, 2, [(2, 2), (3, 1), (23, 1), (79, 1), (7487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_79
    · exact prime_7487
  · decide +kernel

theorem prime_210333353 : Nat.Prime 210333353 := by
  apply nodeValid_prime [2, 487, 53987] ⟨210333353, 3, [(2, 3), (487, 1), (53987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_53987
  · decide +kernel

theorem prime_216091901 : Nat.Prime 216091901 := by
  apply nodeValid_prime [2, 5, 23, 47, 1999] ⟨216091901, 2, [(2, 2), (5, 2), (23, 1), (47, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_47
    · exact prime_1999
  · decide +kernel

theorem prime_237136121 : Nat.Prime 237136121 := by
  apply nodeValid_prime [2, 5, 13, 73, 6247] ⟨237136121, 3, [(2, 3), (5, 1), (13, 1), (73, 1), (6247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_73
    · exact prime_6247
  · decide +kernel

theorem prime_254878339 : Nat.Prime 254878339 := by
  apply nodeValid_prime [2, 3, 11, 13, 297061] ⟨254878339, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (297061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_297061
  · decide +kernel

theorem prime_299151353 : Nat.Prime 299151353 := by
  apply nodeValid_prime [2, 19, 139, 14159] ⟨299151353, 3, [(2, 3), (19, 1), (139, 1), (14159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_139
    · exact prime_14159
  · decide +kernel

theorem prime_365138701 : Nat.Prime 365138701 := by
  apply nodeValid_prime [2, 3, 5, 73, 16673] ⟨365138701, 2, [(2, 2), (3, 1), (5, 2), (73, 1), (16673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_16673
  · decide +kernel

theorem prime_429736961 : Nat.Prime 429736961 := by
  apply nodeValid_prime [2, 5, 83933] ⟨429736961, 3, [(2, 10), (5, 1), (83933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83933
  · decide +kernel

theorem prime_532869767 : Nat.Prime 532869767 := by
  apply nodeValid_prime [2, 11, 13, 1863181] ⟨532869767, 5, [(2, 1), (11, 1), (13, 1), (1863181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_1863181
  · decide +kernel

theorem prime_623125777 : Nat.Prime 623125777 := by
  apply nodeValid_prime [2, 3, 7, 13, 142657] ⟨623125777, 5, [(2, 4), (3, 1), (7, 1), (13, 1), (142657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_142657
  · decide +kernel

theorem prime_934688669 : Nat.Prime 934688669 := by
  apply nodeValid_prime [2, 131, 887, 2011] ⟨934688669, 2, [(2, 2), (131, 1), (887, 1), (2011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_887
    · exact prime_2011
  · decide +kernel

theorem prime_2350510193 : Nat.Prime 2350510193 := by
  apply nodeValid_prime [2, 146906887] ⟨2350510193, 3, [(2, 4), (146906887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_146906887
  · decide +kernel

theorem prime_2435645183 : Nat.Prime 2435645183 := by
  apply nodeValid_prime [2, 17, 313, 13463] ⟨2435645183, 5, [(2, 1), (17, 2), (313, 1), (13463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_313
    · exact prime_13463
  · decide +kernel

theorem prime_5899333079 : Nat.Prime 5899333079 := by
  apply nodeValid_prime [2, 107, 239, 115343] ⟨5899333079, 23, [(2, 1), (107, 1), (239, 1), (115343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_239
    · exact prime_115343
  · decide +kernel

theorem prime_6650170673 : Nat.Prime 6650170673 := by
  apply nodeValid_prime [2, 19051, 21817] ⟨6650170673, 3, [(2, 4), (19051, 1), (21817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19051
    · exact prime_21817
  · decide +kernel

theorem prime_7773791741 : Nat.Prime 7773791741 := by
  apply nodeValid_prime [2, 5, 11, 13, 2718109] ⟨7773791741, 3, [(2, 2), (5, 1), (11, 1), (13, 1), (2718109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_2718109
  · decide +kernel

theorem prime_9936096563 : Nat.Prime 9936096563 := by
  apply nodeValid_prime [2, 7, 71, 9996073] ⟨9936096563, 2, [(2, 1), (7, 1), (71, 1), (9996073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_9996073
  · decide +kernel

theorem prime_20107777583 : Nat.Prime 20107777583 := by
  apply nodeValid_prime [2, 17, 421, 1404763] ⟨20107777583, 5, [(2, 1), (17, 1), (421, 1), (1404763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_421
    · exact prime_1404763
  · decide +kernel

theorem prime_28372249903 : Nat.Prime 28372249903 := by
  apply nodeValid_prime [2, 3, 25561, 184997] ⟨28372249903, 3, [(2, 1), (3, 1), (25561, 1), (184997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25561
    · exact prime_184997
  · decide +kernel

theorem prime_34435290257 : Nat.Prime 34435290257 := by
  apply nodeValid_prime [2, 601, 3581041] ⟨34435290257, 3, [(2, 4), (601, 1), (3581041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_3581041
  · decide +kernel

theorem prime_46642750447 : Nat.Prime 46642750447 := by
  apply nodeValid_prime [2, 3, 7773791741] ⟨46642750447, 3, [(2, 1), (3, 1), (7773791741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7773791741
  · decide +kernel

theorem prime_69006634813 : Nat.Prime 69006634813 := by
  apply nodeValid_prime [2, 3, 19, 6871, 14683] ⟨69006634813, 2, [(2, 2), (3, 2), (19, 1), (6871, 1), (14683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_6871
    · exact prime_14683
  · decide +kernel

theorem prime_137198031521 : Nat.Prime 137198031521 := by
  apply nodeValid_prime [2, 5, 11, 77953427] ⟨137198031521, 3, [(2, 5), (5, 1), (11, 1), (77953427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_77953427
  · decide +kernel

theorem prime_139105351883 : Nat.Prime 139105351883 := by
  apply nodeValid_prime [2, 7, 9936096563] ⟨139105351883, 2, [(2, 1), (7, 1), (9936096563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9936096563
  · decide +kernel

theorem prime_272232264001 : Nat.Prime 272232264001 := by
  apply nodeValid_prime [2, 3, 5, 61, 185951] ⟨272232264001, 14, [(2, 6), (3, 1), (5, 3), (61, 1), (185951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_185951
  · decide +kernel

theorem prime_272232266909 : Nat.Prime 272232266909 := by
  apply nodeValid_prime [2, 7, 41, 237136121] ⟨272232266909, 2, [(2, 2), (7, 1), (41, 1), (237136121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_237136121
  · decide +kernel

theorem prime_272232267833 : Nat.Prime 272232267833 := by
  apply nodeValid_prime [2, 7, 563, 653, 1889] ⟨272232267833, 3, [(2, 3), (7, 2), (563, 1), (653, 1), (1889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_563
    · exact prime_653
    · exact prime_1889
  · decide +kernel

theorem prime_272772119069 : Nat.Prime 272772119069 := by
  apply nodeValid_prime [2, 53, 6571, 195809] ⟨272772119069, 2, [(2, 2), (53, 1), (6571, 1), (195809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_6571
    · exact prime_195809
  · decide +kernel

theorem prime_272772153739 : Nat.Prime 272772153739 := by
  apply nodeValid_prime [2, 3, 7, 16193, 133691] ⟨272772153739, 2, [(2, 1), (3, 2), (7, 1), (16193, 1), (133691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_16193
    · exact prime_133691
  · decide +kernel

theorem prime_273312679139 : Nat.Prime 273312679139 := by
  apply nodeValid_prime [2, 5407, 25273967] ⟨273312679139, 2, [(2, 1), (5407, 1), (25273967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5407
    · exact prime_25273967
  · decide +kernel

theorem prime_273312680063 : Nat.Prime 273312680063 := by
  apply nodeValid_prime [2, 19, 79, 91043531] ⟨273312680063, 5, [(2, 1), (19, 1), (79, 1), (91043531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_79
    · exact prime_91043531
  · decide +kernel

theorem prime_273312707197 : Nat.Prime 273312707197 := by
  apply nodeValid_prime [2, 3, 53, 429736961] ⟨273312707197, 2, [(2, 2), (3, 1), (53, 1), (429736961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_429736961
  · decide +kernel

theorem prime_273854023109 : Nat.Prime 273854023109 := by
  apply nodeValid_prime [2, 37, 59, 31362119] ⟨273854023109, 2, [(2, 2), (37, 1), (59, 1), (31362119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_59
    · exact prime_31362119
  · decide +kernel

theorem prime_273854025607 : Nat.Prime 273854025607 := by
  apply nodeValid_prime [2, 3, 7, 31, 210333353] ⟨273854025607, 3, [(2, 1), (3, 1), (7, 1), (31, 1), (210333353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_210333353
  · decide +kernel

theorem prime_273854025751 : Nat.Prime 273854025751 := by
  apply nodeValid_prime [2, 3, 5, 365138701] ⟨273854025751, 3, [(2, 1), (3, 1), (5, 3), (365138701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_365138701
  · decide +kernel

theorem prime_274396063043 : Nat.Prime 274396063043 := by
  apply nodeValid_prime [2, 137198031521] ⟨274396063043, 2, [(2, 1), (137198031521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_137198031521
  · decide +kernel

theorem prime_274396091173 : Nat.Prime 274396091173 := by
  apply nodeValid_prime [2, 3, 7, 31, 73, 89, 331] ⟨274396091173, 2, [(2, 2), (3, 1), (7, 3), (31, 1), (73, 1), (89, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_73
    · exact prime_89
    · exact prime_331
  · decide +kernel

theorem prime_274396091377 : Nat.Prime 274396091377 := by
  apply nodeValid_prime [2, 3, 11, 3011, 172597] ⟨274396091377, 5, [(2, 4), (3, 1), (11, 1), (3011, 1), (172597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3011
    · exact prime_172597
  · decide +kernel

theorem prime_274938811867 : Nat.Prime 274938811867 := by
  apply nodeValid_prime [2, 3, 739, 6889661] ⟨274938811867, 23, [(2, 1), (3, 3), (739, 1), (6889661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_739
    · exact prime_6889661
  · decide +kernel

theorem prime_274938812429 : Nat.Prime 274938812429 := by
  apply nodeValid_prime [2, 7, 19, 79, 934543] ⟨274938812429, 3, [(2, 2), (7, 2), (19, 1), (79, 1), (934543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_79
    · exact prime_934543
  · decide +kernel

theorem prime_274938829093 : Nat.Prime 274938829093 := by
  apply nodeValid_prime [2, 3, 1489, 569897] ⟨274938829093, 2, [(2, 2), (3, 4), (1489, 1), (569897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1489
    · exact prime_569897
  · decide +kernel

theorem prime_275482322057 : Nat.Prime 275482322057 := by
  apply nodeValid_prime [2, 34435290257] ⟨275482322057, 3, [(2, 3), (34435290257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34435290257
  · decide +kernel

theorem prime_275482351007 : Nat.Prime 275482351007 := by
  apply nodeValid_prime [2, 23, 29, 3391, 60899] ⟨275482351007, 5, [(2, 1), (23, 1), (29, 1), (3391, 1), (60899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_3391
    · exact prime_60899
  · decide +kernel

theorem prime_275482351583 : Nat.Prime 275482351583 := by
  apply nodeValid_prime [2, 211, 761, 857821] ⟨275482351583, 5, [(2, 1), (211, 1), (761, 1), (857821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_761
    · exact prime_857821
  · decide +kernel

theorem prime_276026539253 : Nat.Prime 276026539253 := by
  apply nodeValid_prime [2, 69006634813] ⟨276026539253, 2, [(2, 2), (69006634813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_69006634813
  · decide +kernel

theorem prime_276026539307 : Nat.Prime 276026539307 := by
  apply nodeValid_prime [2, 7, 37, 532869767] ⟨276026539307, 2, [(2, 1), (7, 1), (37, 1), (532869767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_532869767
  · decide +kernel

theorem prime_276026540653 : Nat.Prime 276026540653 := by
  apply nodeValid_prime [2, 3, 35107, 218401] ⟨276026540653, 5, [(2, 2), (3, 2), (35107, 1), (218401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35107
    · exact prime_218401
  · decide +kernel

theorem prime_276571479731 : Nat.Prime 276571479731 := by
  apply nodeValid_prime [2, 5, 7, 13, 19, 15996037] ⟨276571479731, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (15996037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_15996037
  · decide +kernel

theorem prime_276571531153 : Nat.Prime 276571531153 := by
  apply nodeValid_prime [2, 3, 7, 10937, 25087] ⟨276571531153, 5, [(2, 4), (3, 2), (7, 1), (10937, 1), (25087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10937
    · exact prime_25087
  · decide +kernel

theorem prime_276571531283 : Nat.Prime 276571531283 := by
  apply nodeValid_prime [2, 109, 6977, 181837] ⟨276571531283, 2, [(2, 1), (109, 1), (6977, 1), (181837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_6977
    · exact prime_181837
  · decide +kernel

theorem prime_277117148933 : Nat.Prime 277117148933 := by
  apply nodeValid_prime [2, 13, 41, 181, 718121] ⟨277117148933, 3, [(2, 2), (13, 1), (41, 1), (181, 1), (718121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_181
    · exact prime_718121
  · decide +kernel

theorem prime_277117151671 : Nat.Prime 277117151671 := by
  apply nodeValid_prime [2, 3, 5, 47, 21837443] ⟨277117151671, 6, [(2, 1), (3, 3), (5, 1), (47, 1), (21837443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_21837443
  · decide +kernel

theorem prime_277117151833 : Nat.Prime 277117151833 := by
  apply nodeValid_prime [2, 3, 3527, 363751] ⟨277117151833, 13, [(2, 3), (3, 3), (3527, 1), (363751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3527
    · exact prime_363751
  · decide +kernel

theorem prime_277663550863 : Nat.Prime 277663550863 := by
  apply nodeValid_prime [2, 3, 19, 2435645183] ⟨277663550863, 5, [(2, 1), (3, 1), (19, 1), (2435645183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2435645183
  · decide +kernel

theorem prime_277663573571 : Nat.Prime 277663573571 := by
  apply nodeValid_prime [2, 5, 31, 257, 3485171] ⟨277663573571, 2, [(2, 1), (5, 1), (31, 1), (257, 1), (3485171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_257
    · exact prime_3485171
  · decide +kernel

theorem prime_277663573661 : Nat.Prime 277663573661 := by
  apply nodeValid_prime [2, 5, 11, 199, 491, 12917] ⟨277663573661, 2, [(2, 2), (5, 1), (11, 1), (199, 1), (491, 1), (12917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_199
    · exact prime_491
    · exact prime_12917
  · decide +kernel

theorem prime_278210687759 : Nat.Prime 278210687759 := by
  apply nodeValid_prime [2, 17, 601, 631, 21577] ⟨278210687759, 7, [(2, 1), (17, 1), (601, 1), (631, 1), (21577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_601
    · exact prime_631
    · exact prime_21577
  · decide +kernel

theorem prime_278210703767 : Nat.Prime 278210703767 := by
  apply nodeValid_prime [2, 139105351883] ⟨278210703767, 5, [(2, 1), (139105351883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_139105351883
  · decide +kernel

theorem prime_278210703829 : Nat.Prime 278210703829 := by
  apply nodeValid_prime [2, 3, 683, 941, 36073] ⟨278210703829, 14, [(2, 2), (3, 1), (683, 1), (941, 1), (36073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_941
    · exact prime_36073
  · decide +kernel

theorem prime_278758552291 : Nat.Prime 278758552291 := by
  apply nodeValid_prime [2, 3, 5, 43, 216091901] ⟨278758552291, 2, [(2, 1), (3, 1), (5, 1), (43, 1), (216091901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_216091901
  · decide +kernel

theorem prime_278758552361 : Nat.Prime 278758552361 := by
  apply nodeValid_prime [2, 5, 24967, 279127] ⟨278758552361, 3, [(2, 3), (5, 1), (24967, 1), (279127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_24967
    · exact prime_279127
  · decide +kernel

theorem prime_278758558829 : Nat.Prime 278758558829 := by
  apply nodeValid_prime [2, 17, 4649, 881779] ⟨278758558829, 2, [(2, 2), (17, 1), (4649, 1), (881779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4649
    · exact prime_881779
  · decide +kernel

theorem prime_279307163441 : Nat.Prime 279307163441 := by
  apply nodeValid_prime [2, 5, 41, 53, 163, 9857] ⟨279307163441, 7, [(2, 4), (5, 1), (41, 1), (53, 1), (163, 1), (9857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_53
    · exact prime_163
    · exact prime_9857
  · decide +kernel

theorem prime_279307168267 : Nat.Prime 279307168267 := by
  apply nodeValid_prime [2, 3, 7, 6650170673] ⟨279307168267, 2, [(2, 1), (3, 1), (7, 1), (6650170673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6650170673
  · decide +kernel

theorem prime_279307168303 : Nat.Prime 279307168303 := by
  apply nodeValid_prime [2, 3, 67, 569, 1221079] ⟨279307168303, 5, [(2, 1), (3, 1), (67, 1), (569, 1), (1221079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_569
    · exact prime_1221079
  · decide +kernel

theorem prime_279856416223 : Nat.Prime 279856416223 := by
  apply nodeValid_prime [2, 3, 61, 254878339] ⟨279856416223, 6, [(2, 1), (3, 2), (61, 1), (254878339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_254878339
  · decide +kernel

theorem prime_279856417573 : Nat.Prime 279856417573 := by
  apply nodeValid_prime [2, 3, 3407, 2281711] ⟨279856417573, 5, [(2, 2), (3, 2), (3407, 1), (2281711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3407
    · exact prime_2281711
  · decide +kernel

theorem prime_279856502683 : Nat.Prime 279856502683 := by
  apply nodeValid_prime [2, 3, 46642750447] ⟨279856502683, 2, [(2, 1), (3, 1), (46642750447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_46642750447
  · decide +kernel

theorem prime_280406579023 : Nat.Prime 280406579023 := by
  apply nodeValid_prime [2, 3, 47, 73, 661, 6869] ⟨280406579023, 5, [(2, 1), (3, 2), (47, 1), (73, 1), (661, 1), (6869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_73
    · exact prime_661
    · exact prime_6869
  · decide +kernel

theorem prime_280406599651 : Nat.Prime 280406599651 := by
  apply nodeValid_prime [2, 3, 5, 623125777] ⟨280406599651, 3, [(2, 1), (3, 2), (5, 2), (623125777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_623125777
  · decide +kernel

theorem prime_280406600701 : Nat.Prime 280406600701 := by
  apply nodeValid_prime [2, 3, 5, 934688669] ⟨280406600701, 6, [(2, 2), (3, 1), (5, 2), (934688669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_934688669
  · decide +kernel

theorem prime_280957385963 : Nat.Prime 280957385963 := by
  apply nodeValid_prime [2, 11, 53, 139, 241, 7193] ⟨280957385963, 2, [(2, 1), (11, 1), (53, 1), (139, 1), (241, 1), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_139
    · exact prime_241
    · exact prime_7193
  · decide +kernel

theorem prime_280957394359 : Nat.Prime 280957394359 := by
  apply nodeValid_prime [2, 3, 19, 263, 3123623] ⟨280957394359, 6, [(2, 1), (3, 2), (19, 1), (263, 1), (3123623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_263
    · exact prime_3123623
  · decide +kernel

theorem prime_280957395559 : Nat.Prime 280957395559 := by
  apply nodeValid_prime [2, 3, 7, 73, 6949, 13187] ⟨280957395559, 3, [(2, 1), (3, 1), (7, 1), (73, 1), (6949, 1), (13187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_6949
    · exact prime_13187
  · decide +kernel

theorem prime_281508885923 : Nat.Prime 281508885923 := by
  apply nodeValid_prime [2, 11, 6719, 1904429] ⟨281508885923, 2, [(2, 1), (11, 1), (6719, 1), (1904429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6719
    · exact prime_1904429
  · decide +kernel

theorem prime_281508886163 : Nat.Prime 281508886163 := by
  apply nodeValid_prime [2, 7, 20107777583] ⟨281508886163, 2, [(2, 1), (7, 1), (20107777583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_20107777583
  · decide +kernel

theorem prime_281508929749 : Nat.Prime 281508929749 := by
  apply nodeValid_prime [2, 3, 151, 51786043] ⟨281508929749, 6, [(2, 2), (3, 2), (151, 1), (51786043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_51786043
  · decide +kernel

theorem prime_282061209679 : Nat.Prime 282061209679 := by
  apply nodeValid_prime [2, 3, 4001, 11749613] ⟨282061209679, 7, [(2, 1), (3, 1), (4001, 1), (11749613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4001
    · exact prime_11749613
  · decide +kernel

theorem prime_282061223161 : Nat.Prime 282061223161 := by
  apply nodeValid_prime [2, 3, 5, 2350510193] ⟨282061223161, 29, [(2, 3), (3, 1), (5, 1), (2350510193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2350510193
  · decide +kernel

theorem prime_282061224307 : Nat.Prime 282061224307 := by
  apply nodeValid_prime [2, 3, 29, 8317, 64969] ⟨282061224307, 2, [(2, 1), (3, 2), (29, 1), (8317, 1), (64969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_8317
    · exact prime_64969
  · decide +kernel

theorem prime_282614228257 : Nat.Prime 282614228257 := by
  apply nodeValid_prime [2, 3, 17, 167, 181, 337] ⟨282614228257, 5, [(2, 5), (3, 1), (17, 2), (167, 1), (181, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_167
    · exact prime_181
    · exact prime_337
  · decide +kernel

theorem prime_282614259107 : Nat.Prime 282614259107 := by
  apply nodeValid_prime [2, 107, 149, 2441, 3631] ⟨282614259107, 2, [(2, 1), (107, 1), (149, 1), (2441, 1), (3631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_149
    · exact prime_2441
    · exact prime_3631
  · decide +kernel

theorem prime_282614259313 : Nat.Prime 282614259313 := by
  apply nodeValid_prime [2, 3, 7, 11, 25488299] ⟨282614259313, 5, [(2, 4), (3, 2), (7, 1), (11, 1), (25488299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_25488299
  · decide +kernel

theorem prime_283167934591 : Nat.Prime 283167934591 := by
  apply nodeValid_prime [2, 3, 5, 23, 41, 10009471] ⟨283167934591, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (41, 1), (10009471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_41
    · exact prime_10009471
  · decide +kernel

theorem prime_283167935201 : Nat.Prime 283167935201 := by
  apply nodeValid_prime [2, 5, 6451, 54869] ⟨283167935201, 3, [(2, 5), (5, 2), (6451, 1), (54869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6451
    · exact prime_54869
  · decide +kernel

theorem prime_283167987793 : Nat.Prime 283167987793 := by
  apply nodeValid_prime [2, 3, 5899333079] ⟨283167987793, 5, [(2, 4), (3, 1), (5899333079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5899333079
  · decide +kernel

theorem prime_283722486367 : Nat.Prime 283722486367 := by
  apply nodeValid_prime [2, 3, 11, 45341, 94811] ⟨283722486367, 3, [(2, 1), (3, 1), (11, 1), (45341, 1), (94811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_45341
    · exact prime_94811
  · decide +kernel

theorem prime_283722499031 : Nat.Prime 283722499031 := by
  apply nodeValid_prime [2, 5, 28372249903] ⟨283722499031, 11, [(2, 1), (5, 1), (28372249903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_28372249903
  · decide +kernel

theorem prime_283722502163 : Nat.Prime 283722502163 := by
  apply nodeValid_prime [2, 11, 79, 163246549] ⟨283722502163, 5, [(2, 1), (11, 1), (79, 1), (163246549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79
    · exact prime_163246549
  · decide +kernel

theorem prime_284277715831 : Nat.Prime 284277715831 := by
  apply nodeValid_prime [2, 3, 5, 59, 5948477] ⟨284277715831, 3, [(2, 1), (3, 4), (5, 1), (59, 1), (5948477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_5948477
  · decide +kernel

theorem prime_284277717001 : Nat.Prime 284277717001 := by
  apply nodeValid_prime [2, 3, 5, 67, 471439] ⟨284277717001, 7, [(2, 3), (3, 2), (5, 3), (67, 1), (471439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_471439
  · decide +kernel

theorem prime_284277721807 : Nat.Prime 284277721807 := by
  apply nodeValid_prime [2, 3, 13, 1423, 853733] ⟨284277721807, 5, [(2, 1), (3, 2), (13, 1), (1423, 1), (853733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1423
    · exact prime_853733
  · decide +kernel

theorem prime_284833677283 : Nat.Prime 284833677283 := by
  apply nodeValid_prime [2, 3, 7, 11, 47, 149, 88037] ⟨284833677283, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (47, 1), (149, 1), (88037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_47
    · exact prime_149
    · exact prime_88037
  · decide +kernel

theorem prime_284833677307 : Nat.Prime 284833677307 := by
  apply nodeValid_prime [2, 3, 19, 61, 40959689] ⟨284833677307, 11, [(2, 1), (3, 1), (19, 1), (61, 1), (40959689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
    · exact prime_40959689
  · decide +kernel

theorem prime_284833690987 : Nat.Prime 284833690987 := by
  apply nodeValid_prime [2, 3, 13, 19, 11411, 16843] ⟨284833690987, 2, [(2, 1), (3, 1), (13, 1), (19, 1), (11411, 1), (16843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_11411
    · exact prime_16843
  · decide +kernel

theorem prime_285390390091 : Nat.Prime 285390390091 := by
  apply nodeValid_prime [2, 3, 5, 13, 23, 97, 241, 1361] ⟨285390390091, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (23, 1), (97, 1), (241, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_97
    · exact prime_241
    · exact prime_1361
  · decide +kernel

theorem prime_285390390679 : Nat.Prime 285390390679 := by
  apply nodeValid_prime [2, 3, 1303, 36504271] ⟨285390390679, 19, [(2, 1), (3, 1), (1303, 1), (36504271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1303
    · exact prime_36504271
  · decide +kernel

theorem prime_285390390763 : Nat.Prime 285390390763 := by
  apply nodeValid_prime [2, 3, 53, 299151353] ⟨285390390763, 5, [(2, 1), (3, 2), (53, 1), (299151353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_299151353
  · decide +kernel

end Sude.Lucas.Generated
