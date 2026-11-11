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

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1871 : Nat.Prime 1871 := by
  apply nodeValid_prime [2, 5, 11, 17] ⟨1871, 14, [(2, 1), (5, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_2143 : Nat.Prime 2143 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨2143, 3, [(2, 1), (3, 2), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_2503 : Nat.Prime 2503 := by
  apply nodeValid_prime [2, 3, 139] ⟨2503, 3, [(2, 1), (3, 2), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_2851 : Nat.Prime 2851 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨2851, 2, [(2, 1), (3, 1), (5, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_3187 : Nat.Prime 3187 := by
  apply nodeValid_prime [2, 3, 59] ⟨3187, 2, [(2, 1), (3, 3), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_3469 : Nat.Prime 3469 := by
  apply nodeValid_prime [2, 3, 17] ⟨3469, 2, [(2, 2), (3, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_3673 : Nat.Prime 3673 := by
  apply nodeValid_prime [2, 3, 17] ⟨3673, 5, [(2, 3), (3, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_4597 : Nat.Prime 4597 := by
  apply nodeValid_prime [2, 3, 383] ⟨4597, 5, [(2, 2), (3, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_383
  · decide +kernel

theorem prime_4679 : Nat.Prime 4679 := by
  apply nodeValid_prime [2, 2339] ⟨4679, 11, [(2, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2339
  · decide +kernel

theorem prime_4943 : Nat.Prime 4943 := by
  apply nodeValid_prime [2, 7, 353] ⟨4943, 7, [(2, 1), (7, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_353
  · decide +kernel

theorem prime_5233 : Nat.Prime 5233 := by
  apply nodeValid_prime [2, 3, 109] ⟨5233, 10, [(2, 4), (3, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_5449 : Nat.Prime 5449 := by
  apply nodeValid_prime [2, 3, 227] ⟨5449, 7, [(2, 3), (3, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
  · decide +kernel

theorem prime_5689 : Nat.Prime 5689 := by
  apply nodeValid_prime [2, 3, 79] ⟨5689, 11, [(2, 3), (3, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_6047 : Nat.Prime 6047 := by
  apply nodeValid_prime [2, 3023] ⟨6047, 5, [(2, 1), (3023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3023
  · decide +kernel

theorem prime_6397 : Nat.Prime 6397 := by
  apply nodeValid_prime [2, 3, 13, 41] ⟨6397, 2, [(2, 2), (3, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_7951 : Nat.Prime 7951 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨7951, 6, [(2, 1), (3, 1), (5, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_7993 : Nat.Prime 7993 := by
  apply nodeValid_prime [2, 3, 37] ⟨7993, 5, [(2, 3), (3, 3), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_8563 : Nat.Prime 8563 := by
  apply nodeValid_prime [2, 3, 1427] ⟨8563, 2, [(2, 1), (3, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1427
  · decide +kernel

theorem prime_8573 : Nat.Prime 8573 := by
  apply nodeValid_prime [2, 2143] ⟨8573, 2, [(2, 2), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2143
  · decide +kernel

theorem prime_12241 : Nat.Prime 12241 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨12241, 7, [(2, 4), (3, 2), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_13159 : Nat.Prime 13159 := by
  apply nodeValid_prime [2, 3, 17, 43] ⟨13159, 3, [(2, 1), (3, 2), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_14419 : Nat.Prime 14419 := by
  apply nodeValid_prime [2, 3, 89] ⟨14419, 2, [(2, 1), (3, 4), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_14939 : Nat.Prime 14939 := by
  apply nodeValid_prime [2, 7, 11, 97] ⟨14939, 2, [(2, 1), (7, 1), (11, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_97
  · decide +kernel

theorem prime_14969 : Nat.Prime 14969 := by
  apply nodeValid_prime [2, 1871] ⟨14969, 3, [(2, 3), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1871
  · decide +kernel

theorem prime_15227 : Nat.Prime 15227 := by
  apply nodeValid_prime [2, 23, 331] ⟨15227, 2, [(2, 1), (23, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_331
  · decide +kernel

theorem prime_17077 : Nat.Prime 17077 := by
  apply nodeValid_prime [2, 3, 1423] ⟨17077, 2, [(2, 2), (3, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1423
  · decide +kernel

theorem prime_20857 : Nat.Prime 20857 := by
  apply nodeValid_prime [2, 3, 11, 79] ⟨20857, 10, [(2, 3), (3, 1), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_21011 : Nat.Prime 21011 := by
  apply nodeValid_prime [2, 5, 11, 191] ⟨21011, 2, [(2, 1), (5, 1), (11, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_191
  · decide +kernel

theorem prime_23017 : Nat.Prime 23017 := by
  apply nodeValid_prime [2, 3, 7, 137] ⟨23017, 5, [(2, 3), (3, 1), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_27697 : Nat.Prime 27697 := by
  apply nodeValid_prime [2, 3, 577] ⟨27697, 5, [(2, 4), (3, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
  · decide +kernel

theorem prime_27967 : Nat.Prime 27967 := by
  apply nodeValid_prime [2, 3, 59, 79] ⟨27967, 3, [(2, 1), (3, 1), (59, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_79
  · decide +kernel

theorem prime_31973 : Nat.Prime 31973 := by
  apply nodeValid_prime [2, 7993] ⟨31973, 2, [(2, 2), (7993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7993
  · decide +kernel

theorem prime_32911 : Nat.Prime 32911 := by
  apply nodeValid_prime [2, 3, 5, 1097] ⟨32911, 3, [(2, 1), (3, 1), (5, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1097
  · decide +kernel

theorem prime_35491 : Nat.Prime 35491 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨35491, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_42023 : Nat.Prime 42023 := by
  apply nodeValid_prime [2, 21011] ⟨42023, 5, [(2, 1), (21011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21011
  · decide +kernel

theorem prime_46349 : Nat.Prime 46349 := by
  apply nodeValid_prime [2, 11587] ⟨46349, 2, [(2, 2), (11587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11587
  · decide +kernel

theorem prime_52837 : Nat.Prime 52837 := by
  apply nodeValid_prime [2, 3, 7, 17, 37] ⟨52837, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_56149 : Nat.Prime 56149 := by
  apply nodeValid_prime [2, 3, 4679] ⟨56149, 6, [(2, 2), (3, 1), (4679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4679
  · decide +kernel

theorem prime_57367 : Nat.Prime 57367 := by
  apply nodeValid_prime [2, 3, 3187] ⟨57367, 3, [(2, 1), (3, 2), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3187
  · decide +kernel

theorem prime_57383 : Nat.Prime 57383 := by
  apply nodeValid_prime [2, 13, 2207] ⟨57383, 5, [(2, 1), (13, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2207
  · decide +kernel

theorem prime_59651 : Nat.Prime 59651 := by
  apply nodeValid_prime [2, 5, 1193] ⟨59651, 2, [(2, 1), (5, 2), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1193
  · decide +kernel

theorem prime_62417 : Nat.Prime 62417 := by
  apply nodeValid_prime [2, 47, 83] ⟨62417, 3, [(2, 4), (47, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_83
  · decide +kernel

theorem prime_63823 : Nat.Prime 63823 := by
  apply nodeValid_prime [2, 3, 11, 967] ⟨63823, 3, [(2, 1), (3, 1), (11, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_967
  · decide +kernel

theorem prime_63901 : Nat.Prime 63901 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨63901, 7, [(2, 2), (3, 2), (5, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_65729 : Nat.Prime 65729 := by
  apply nodeValid_prime [2, 13, 79] ⟨65729, 3, [(2, 6), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_73597 : Nat.Prime 73597 := by
  apply nodeValid_prime [2, 3, 6133] ⟨73597, 2, [(2, 2), (3, 1), (6133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6133
  · decide +kernel

theorem prime_78517 : Nat.Prime 78517 := by
  apply nodeValid_prime [2, 3, 727] ⟨78517, 2, [(2, 2), (3, 3), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_727
  · decide +kernel

theorem prime_84047 : Nat.Prime 84047 := by
  apply nodeValid_prime [2, 42023] ⟨84047, 5, [(2, 1), (42023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42023
  · decide +kernel

theorem prime_84349 : Nat.Prime 84349 := by
  apply nodeValid_prime [2, 3, 11, 71] ⟨84349, 2, [(2, 2), (3, 3), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_92699 : Nat.Prime 92699 := by
  apply nodeValid_prime [2, 46349] ⟨92699, 2, [(2, 1), (46349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46349
  · decide +kernel

theorem prime_96799 : Nat.Prime 96799 := by
  apply nodeValid_prime [2, 3, 13, 17, 73] ⟨96799, 6, [(2, 1), (3, 1), (13, 1), (17, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_73
  · decide +kernel

theorem prime_118633 : Nat.Prime 118633 := by
  apply nodeValid_prime [2, 3, 4943] ⟨118633, 5, [(2, 3), (3, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4943
  · decide +kernel

theorem prime_119429 : Nat.Prime 119429 := by
  apply nodeValid_prime [2, 73, 409] ⟨119429, 2, [(2, 2), (73, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_409
  · decide +kernel

theorem prime_127133 : Nat.Prime 127133 := by
  apply nodeValid_prime [2, 37, 859] ⟨127133, 2, [(2, 2), (37, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_859
  · decide +kernel

theorem prime_127703 : Nat.Prime 127703 := by
  apply nodeValid_prime [2, 67, 953] ⟨127703, 5, [(2, 1), (67, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_953
  · decide +kernel

theorem prime_150427 : Nat.Prime 150427 := by
  apply nodeValid_prime [2, 3, 61, 137] ⟨150427, 5, [(2, 1), (3, 2), (61, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_137
  · decide +kernel

theorem prime_171341 : Nat.Prime 171341 := by
  apply nodeValid_prime [2, 5, 13, 659] ⟨171341, 2, [(2, 2), (5, 1), (13, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_659
  · decide +kernel

theorem prime_174877 : Nat.Prime 174877 := by
  apply nodeValid_prime [2, 3, 13, 19, 59] ⟨174877, 5, [(2, 2), (3, 1), (13, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_217157 : Nat.Prime 217157 := by
  apply nodeValid_prime [2, 233] ⟨217157, 2, [(2, 2), (233, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_233
  · decide +kernel

theorem prime_231409 : Nat.Prime 231409 := by
  apply nodeValid_prime [2, 3, 1607] ⟨231409, 7, [(2, 4), (3, 2), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1607
  · decide +kernel

theorem prime_238859 : Nat.Prime 238859 := by
  apply nodeValid_prime [2, 119429] ⟨238859, 2, [(2, 1), (119429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_119429
  · decide +kernel

theorem prime_265621 : Nat.Prime 265621 := by
  apply nodeValid_prime [2, 3, 5, 19, 233] ⟨265621, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_233
  · decide +kernel

theorem prime_296731 : Nat.Prime 296731 := by
  apply nodeValid_prime [2, 3, 5, 7, 157] ⟨296731, 10, [(2, 1), (3, 3), (5, 1), (7, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_157
  · decide +kernel

theorem prime_303337 : Nat.Prime 303337 := by
  apply nodeValid_prime [2, 3, 11, 383] ⟨303337, 5, [(2, 3), (3, 2), (11, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_383
  · decide +kernel

theorem prime_325541 : Nat.Prime 325541 := by
  apply nodeValid_prime [2, 5, 41, 397] ⟨325541, 2, [(2, 2), (5, 1), (41, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_397
  · decide +kernel

theorem prime_335917 : Nat.Prime 335917 := by
  apply nodeValid_prime [2, 3, 7, 31, 43] ⟨335917, 6, [(2, 2), (3, 2), (7, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_340079 : Nat.Prime 340079 := by
  apply nodeValid_prime [2, 23, 7393] ⟨340079, 11, [(2, 1), (23, 1), (7393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_7393
  · decide +kernel

theorem prime_368273 : Nat.Prime 368273 := by
  apply nodeValid_prime [2, 23017] ⟨368273, 3, [(2, 4), (23017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23017
  · decide +kernel

theorem prime_432457 : Nat.Prime 432457 := by
  apply nodeValid_prime [2, 3, 37, 487] ⟨432457, 5, [(2, 3), (3, 1), (37, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_487
  · decide +kernel

theorem prime_449131 : Nat.Prime 449131 := by
  apply nodeValid_prime [2, 3, 5, 11, 1361] ⟨449131, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1361
  · decide +kernel

theorem prime_484181 : Nat.Prime 484181 := by
  apply nodeValid_prime [2, 5, 43, 563] ⟨484181, 2, [(2, 2), (5, 1), (43, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_563
  · decide +kernel

theorem prime_499423 : Nat.Prime 499423 := by
  apply nodeValid_prime [2, 3, 7, 11, 23, 47] ⟨499423, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_639011 : Nat.Prime 639011 := by
  apply nodeValid_prime [2, 5, 63901] ⟨639011, 2, [(2, 1), (5, 1), (63901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_63901
  · decide +kernel

theorem prime_718513 : Nat.Prime 718513 := by
  apply nodeValid_prime [2, 3, 14969] ⟨718513, 5, [(2, 4), (3, 1), (14969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14969
  · decide +kernel

theorem prime_741593 : Nat.Prime 741593 := by
  apply nodeValid_prime [2, 92699] ⟨741593, 3, [(2, 3), (92699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92699
  · decide +kernel

theorem prime_767029 : Nat.Prime 767029 := by
  apply nodeValid_prime [2, 3, 41, 1559] ⟨767029, 2, [(2, 2), (3, 1), (41, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1559
  · decide +kernel

theorem prime_925637 : Nat.Prime 925637 := by
  apply nodeValid_prime [2, 231409] ⟨925637, 2, [(2, 2), (231409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_231409
  · decide +kernel

theorem prime_951331 : Nat.Prime 951331 := by
  apply nodeValid_prime [2, 3, 5, 19, 1669] ⟨951331, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1669
  · decide +kernel

theorem prime_1083713 : Nat.Prime 1083713 := by
  apply nodeValid_prime [2, 7, 41, 59] ⟨1083713, 3, [(2, 6), (7, 1), (41, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_59
  · decide +kernel

theorem prime_1214417 : Nat.Prime 1214417 := by
  apply nodeValid_prime [2, 7, 1549] ⟨1214417, 3, [(2, 4), (7, 2), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1549
  · decide +kernel

theorem prime_1278227 : Nat.Prime 1278227 := by
  apply nodeValid_prime [2, 67, 9539] ⟨1278227, 2, [(2, 1), (67, 1), (9539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_9539
  · decide +kernel

theorem prime_1452301 : Nat.Prime 1452301 := by
  apply nodeValid_prime [2, 3, 5, 47, 103] ⟨1452301, 2, [(2, 2), (3, 1), (5, 2), (47, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_103
  · decide +kernel

theorem prime_1729829 : Nat.Prime 1729829 := by
  apply nodeValid_prime [2, 432457] ⟨1729829, 2, [(2, 2), (432457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_432457
  · decide +kernel

theorem prime_2211889 : Nat.Prime 2211889 := by
  apply nodeValid_prime [2, 3, 7, 29, 227] ⟨2211889, 37, [(2, 4), (3, 1), (7, 1), (29, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_227
  · decide +kernel

theorem prime_2275439 : Nat.Prime 2275439 := by
  apply nodeValid_prime [2, 11, 293, 353] ⟨2275439, 17, [(2, 1), (11, 1), (293, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_293
    · exact prime_353
  · decide +kernel

theorem prime_2389021 : Nat.Prime 2389021 := by
  apply nodeValid_prime [2, 3, 5, 29, 1373] ⟨2389021, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1373
  · decide +kernel

theorem prime_2920751 : Nat.Prime 2920751 := by
  apply nodeValid_prime [2, 5, 7, 1669] ⟨2920751, 7, [(2, 1), (5, 3), (7, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1669
  · decide +kernel

theorem prime_3044221 : Nat.Prime 3044221 := by
  apply nodeValid_prime [2, 3, 5, 113, 449] ⟨3044221, 13, [(2, 2), (3, 1), (5, 1), (113, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_449
  · decide +kernel

theorem prime_3453371 : Nat.Prime 3453371 := by
  apply nodeValid_prime [2, 5, 151, 2287] ⟨3453371, 2, [(2, 1), (5, 1), (151, 1), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_2287
  · decide +kernel

theorem prime_4562497 : Nat.Prime 4562497 := by
  apply nodeValid_prime [2, 3, 89] ⟨4562497, 5, [(2, 6), (3, 2), (89, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_4853393 : Nat.Prime 4853393 := by
  apply nodeValid_prime [2, 303337] ⟨4853393, 3, [(2, 4), (303337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_303337
  · decide +kernel

theorem prime_6440311 : Nat.Prime 6440311 := by
  apply nodeValid_prime [2, 3, 5, 7951] ⟨6440311, 3, [(2, 1), (3, 4), (5, 1), (7951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7951
  · decide +kernel

theorem prime_6465419 : Nat.Prime 6465419 := by
  apply nodeValid_prime [2, 283, 11423] ⟨6465419, 2, [(2, 1), (283, 1), (11423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_11423
  · decide +kernel

theorem prime_7365461 : Nat.Prime 7365461 := by
  apply nodeValid_prime [2, 5, 368273] ⟨7365461, 7, [(2, 2), (5, 1), (368273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_368273
  · decide +kernel

theorem prime_7493627 : Nat.Prime 7493627 := by
  apply nodeValid_prime [2, 7, 137, 3907] ⟨7493627, 2, [(2, 1), (7, 1), (137, 1), (3907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_3907
  · decide +kernel

theorem prime_8834519 : Nat.Prime 8834519 := by
  apply nodeValid_prime [2, 7, 11, 57367] ⟨8834519, 7, [(2, 1), (7, 1), (11, 1), (57367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_57367
  · decide +kernel

theorem prime_11415973 : Nat.Prime 11415973 := by
  apply nodeValid_prime [2, 3, 951331] ⟨11415973, 2, [(2, 2), (3, 1), (951331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_951331
  · decide +kernel

theorem prime_11791291 : Nat.Prime 11791291 := by
  apply nodeValid_prime [2, 3, 5, 7, 56149] ⟨11791291, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (56149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_56149
  · decide +kernel

theorem prime_12572003 : Nat.Prime 12572003 := by
  apply nodeValid_prime [2, 191, 32911] ⟨12572003, 2, [(2, 1), (191, 1), (32911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_32911
  · decide +kernel

theorem prime_16090579 : Nat.Prime 16090579 := by
  apply nodeValid_prime [2, 3, 7, 127703] ⟨16090579, 2, [(2, 1), (3, 2), (7, 1), (127703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127703
  · decide +kernel

theorem prime_16178119 : Nat.Prime 16178119 := by
  apply nodeValid_prime [2, 3, 11, 17, 14419] ⟨16178119, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (14419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_14419
  · decide +kernel

theorem prime_17505377 : Nat.Prime 17505377 := by
  apply nodeValid_prime [2, 7, 17, 4597] ⟨17505377, 3, [(2, 5), (7, 1), (17, 1), (4597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_4597
  · decide +kernel

theorem prime_20136241 : Nat.Prime 20136241 := by
  apply nodeValid_prime [2, 3, 5, 27967] ⟨20136241, 7, [(2, 4), (3, 2), (5, 1), (27967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27967
  · decide +kernel

theorem prime_21921281 : Nat.Prime 21921281 := by
  apply nodeValid_prime [2, 5, 8563] ⟨21921281, 11, [(2, 9), (5, 1), (8563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8563
  · decide +kernel

theorem prime_25660513 : Nat.Prime 25660513 := by
  apply nodeValid_prime [2, 3, 139, 641] ⟨25660513, 5, [(2, 5), (3, 2), (139, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_641
  · decide +kernel

theorem prime_34220071 : Nat.Prime 34220071 := by
  apply nodeValid_prime [2, 3, 5, 83, 509] ⟨34220071, 3, [(2, 1), (3, 4), (5, 1), (83, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_509
  · decide +kernel

theorem prime_36476399 : Nat.Prime 36476399 := by
  apply nodeValid_prime [2, 7, 31, 84047] ⟨36476399, 7, [(2, 1), (7, 1), (31, 1), (84047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_84047
  · decide +kernel

theorem prime_41529209 : Nat.Prime 41529209 := by
  apply nodeValid_prime [2, 7, 741593] ⟨41529209, 3, [(2, 3), (7, 1), (741593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_741593
  · decide +kernel

theorem prime_64712477 : Nat.Prime 64712477 := by
  apply nodeValid_prime [2, 16178119] ⟨64712477, 2, [(2, 2), (16178119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16178119
  · decide +kernel

theorem prime_71728751 : Nat.Prime 71728751 := by
  apply nodeValid_prime [2, 5, 57383] ⟨71728751, 17, [(2, 1), (5, 4), (57383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_57383
  · decide +kernel

theorem prime_80547371 : Nat.Prime 80547371 := by
  apply nodeValid_prime [2, 5, 41, 71, 2767] ⟨80547371, 2, [(2, 1), (5, 1), (41, 1), (71, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_71
    · exact prime_2767
  · decide +kernel

theorem prime_136991677 : Nat.Prime 136991677 := by
  apply nodeValid_prime [2, 3, 11415973] ⟨136991677, 2, [(2, 2), (3, 1), (11415973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11415973
  · decide +kernel

theorem prime_152748823 : Nat.Prime 152748823 := by
  apply nodeValid_prime [2, 3, 263, 96799] ⟨152748823, 5, [(2, 1), (3, 1), (263, 1), (96799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_96799
  · decide +kernel

theorem prime_161094743 : Nat.Prime 161094743 := by
  apply nodeValid_prime [2, 80547371] ⟨161094743, 5, [(2, 1), (80547371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_80547371
  · decide +kernel

theorem prime_188025419 : Nat.Prime 188025419 := by
  apply nodeValid_prime [2, 7, 2221, 6047] ⟨188025419, 2, [(2, 1), (7, 1), (2221, 1), (6047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2221
    · exact prime_6047
  · decide +kernel

theorem prime_190852553 : Nat.Prime 190852553 := by
  apply nodeValid_prime [2, 11, 127, 17077] ⟨190852553, 3, [(2, 3), (11, 1), (127, 1), (17077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_17077
  · decide +kernel

theorem prime_230145739 : Nat.Prime 230145739 := by
  apply nodeValid_prime [2, 3, 601, 63823] ⟨230145739, 2, [(2, 1), (3, 1), (601, 1), (63823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
    · exact prime_63823
  · decide +kernel

theorem prime_418590517 : Nat.Prime 418590517 := by
  apply nodeValid_prime [2, 3, 1091, 31973] ⟨418590517, 6, [(2, 2), (3, 1), (1091, 1), (31973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
    · exact prime_31973
  · decide +kernel

theorem prime_869962771 : Nat.Prime 869962771 := by
  apply nodeValid_prime [2, 3, 5, 349, 27697] ⟨869962771, 2, [(2, 1), (3, 2), (5, 1), (349, 1), (27697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
    · exact prime_27697
  · decide +kernel

theorem prime_916492939 : Nat.Prime 916492939 := by
  apply nodeValid_prime [2, 3, 152748823] ⟨916492939, 2, [(2, 1), (3, 1), (152748823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152748823
  · decide +kernel

theorem prime_1078371103 : Nat.Prime 1078371103 := by
  apply nodeValid_prime [2, 3, 47, 191, 20021] ⟨1078371103, 3, [(2, 1), (3, 1), (47, 1), (191, 1), (20021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_191
    · exact prime_20021
  · decide +kernel

theorem prime_1085874287 : Nat.Prime 1085874287 := by
  apply nodeValid_prime [2, 7, 17, 4562497] ⟨1085874287, 5, [(2, 1), (7, 1), (17, 1), (4562497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_4562497
  · decide +kernel

theorem prime_1659083207 : Nat.Prime 1659083207 := by
  apply nodeValid_prime [2, 11, 151, 499423] ⟨1659083207, 5, [(2, 1), (11, 1), (151, 1), (499423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_151
    · exact prime_499423
  · decide +kernel

theorem prime_1674362069 : Nat.Prime 1674362069 := by
  apply nodeValid_prime [2, 418590517] ⟨1674362069, 2, [(2, 2), (418590517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_418590517
  · decide +kernel

theorem prime_2222281331 : Nat.Prime 2222281331 := by
  apply nodeValid_prime [2, 5, 73, 3044221] ⟨2222281331, 2, [(2, 1), (5, 1), (73, 1), (3044221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_3044221
  · decide +kernel

theorem prime_2331684497 : Nat.Prime 2331684497 := by
  apply nodeValid_prime [2, 61, 2389021] ⟨2331684497, 3, [(2, 4), (61, 1), (2389021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_2389021
  · decide +kernel

theorem prime_2777265857 : Nat.Prime 2777265857 := by
  apply nodeValid_prime [2, 79, 347, 1583] ⟨2777265857, 3, [(2, 6), (79, 1), (347, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_347
    · exact prime_1583
  · decide +kernel

theorem prime_2940903337 : Nat.Prime 2940903337 := by
  apply nodeValid_prime [2, 3, 7, 17505377] ⟨2940903337, 5, [(2, 3), (3, 1), (7, 1), (17505377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17505377
  · decide +kernel

theorem prime_4051900091 : Nat.Prime 4051900091 := by
  apply nodeValid_prime [2, 5, 7, 331, 174877] ⟨4051900091, 6, [(2, 1), (5, 1), (7, 1), (331, 1), (174877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_331
    · exact prime_174877
  · decide +kernel

theorem prime_4814943047 : Nat.Prime 4814943047 := by
  apply nodeValid_prime [2, 53, 83, 149, 3673] ⟨4814943047, 5, [(2, 1), (53, 1), (83, 1), (149, 1), (3673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_83
    · exact prime_149
    · exact prime_3673
  · decide +kernel

theorem prime_5831060747 : Nat.Prime 5831060747 := by
  apply nodeValid_prime [2, 7, 19, 21921281] ⟨5831060747, 2, [(2, 1), (7, 1), (19, 1), (21921281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_21921281
  · decide +kernel

theorem prime_6485210051 : Nat.Prime 6485210051 := by
  apply nodeValid_prime [2, 5, 11, 11791291] ⟨6485210051, 2, [(2, 1), (5, 2), (11, 1), (11791291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_11791291
  · decide +kernel

theorem prime_9829896481 : Nat.Prime 9829896481 := by
  apply nodeValid_prime [2, 3, 5, 2275439] ⟨9829896481, 7, [(2, 5), (3, 3), (5, 1), (2275439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2275439
  · decide +kernel

theorem prime_14214366503 : Nat.Prime 14214366503 := by
  apply nodeValid_prime [2, 7, 17, 101, 113, 5233] ⟨14214366503, 5, [(2, 1), (7, 1), (17, 1), (101, 1), (113, 1), (5233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_101
    · exact prime_113
    · exact prime_5233
  · decide +kernel

theorem prime_17533183819 : Nat.Prime 17533183819 := by
  apply nodeValid_prime [2, 3, 17, 269, 639011] ⟨17533183819, 2, [(2, 1), (3, 1), (17, 1), (269, 1), (639011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_269
    · exact prime_639011
  · decide +kernel

theorem prime_22218126857 : Nat.Prime 22218126857 := by
  apply nodeValid_prime [2, 2777265857] ⟨22218126857, 3, [(2, 3), (2777265857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2777265857
  · decide +kernel

theorem prime_28428733007 : Nat.Prime 28428733007 := by
  apply nodeValid_prime [2, 14214366503] ⟨28428733007, 5, [(2, 1), (14214366503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14214366503
  · decide +kernel

theorem prime_28559910991 : Nat.Prime 28559910991 := by
  apply nodeValid_prime [2, 3, 5, 13, 19, 1217, 3167] ⟨28559910991, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (1217, 1), (3167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_1217
    · exact prime_3167
  · decide +kernel

theorem prime_29355626873 : Nat.Prime 29355626873 := by
  apply nodeValid_prime [2, 11, 13, 25660513] ⟨29355626873, 3, [(2, 3), (11, 1), (13, 1), (25660513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_25660513
  · decide +kernel

theorem prime_29556877307 : Nat.Prime 29556877307 := by
  apply nodeValid_prime [2, 11, 23, 193, 13159] ⟨29556877307, 2, [(2, 1), (11, 1), (23, 2), (193, 1), (13159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_193
    · exact prime_13159
  · decide +kernel

theorem prime_84112934519 : Nat.Prime 84112934519 := by
  apply nodeValid_prime [2, 1229, 34220071] ⟨84112934519, 11, [(2, 1), (1229, 1), (34220071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1229
    · exact prime_34220071
  · decide +kernel

theorem prime_88267818629 : Nat.Prime 88267818629 := by
  apply nodeValid_prime [2, 11, 31, 64712477] ⟨88267818629, 10, [(2, 2), (11, 1), (31, 1), (64712477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_64712477
  · decide +kernel

theorem prime_168225869039 : Nat.Prime 168225869039 := by
  apply nodeValid_prime [2, 84112934519] ⟨168225869039, 7, [(2, 1), (84112934519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84112934519
  · decide +kernel

theorem prime_168225870251 : Nat.Prime 168225870251 := by
  apply nodeValid_prime [2, 5, 389, 1729829] ⟨168225870251, 2, [(2, 1), (5, 3), (389, 1), (1729829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_389
    · exact prime_1729829
  · decide +kernel

theorem prime_168225892069 : Nat.Prime 168225892069 := by
  apply nodeValid_prime [2, 3, 13, 1078371103] ⟨168225892069, 6, [(2, 2), (3, 1), (13, 1), (1078371103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1078371103
  · decide +kernel

theorem prime_168615454807 : Nat.Prime 168615454807 := by
  apply nodeValid_prime [2, 3, 20857, 449131] ⟨168615454807, 3, [(2, 1), (3, 2), (20857, 1), (449131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20857
    · exact prime_449131
  · decide +kernel

theorem prime_168615461327 : Nat.Prime 168615461327 := by
  apply nodeValid_prime [2, 13, 6485210051] ⟨168615461327, 5, [(2, 1), (13, 1), (6485210051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_6485210051
  · decide +kernel

theorem prime_168615461477 : Nat.Prime 168615461477 := by
  apply nodeValid_prime [2, 7, 11, 2521, 217157] ⟨168615461477, 2, [(2, 2), (7, 1), (11, 1), (2521, 1), (217157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_2521
    · exact prime_217157
  · decide +kernel

theorem prime_169005622171 : Nat.Prime 169005622171 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 61, 171341] ⟨169005622171, 23, [(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (61, 1), (171341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_61
    · exact prime_171341
  · decide +kernel

theorem prime_169005635803 : Nat.Prime 169005635803 := by
  apply nodeValid_prime [2, 3, 12241, 767029] ⟨169005635803, 2, [(2, 1), (3, 2), (12241, 1), (767029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12241
    · exact prime_767029
  · decide +kernel

theorem prime_169005637063 : Nat.Prime 169005637063 := by
  apply nodeValid_prime [2, 3, 62417, 150427] ⟨169005637063, 3, [(2, 1), (3, 2), (62417, 1), (150427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62417
    · exact prime_150427
  · decide +kernel

theorem prime_169396388641 : Nat.Prime 169396388641 := by
  apply nodeValid_prime [2, 3, 5, 1452301] ⟨169396388641, 22, [(2, 5), (3, 6), (5, 1), (1452301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1452301
  · decide +kernel

theorem prime_169396388773 : Nat.Prime 169396388773 := by
  apply nodeValid_prime [2, 3, 13, 1085874287] ⟨169396388773, 2, [(2, 2), (3, 1), (13, 1), (1085874287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1085874287
  · decide +kernel

theorem prime_169396396957 : Nat.Prime 169396396957 := by
  apply nodeValid_prime [2, 3, 43, 36476399] ⟨169396396957, 6, [(2, 2), (3, 3), (43, 1), (36476399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_36476399
  · decide +kernel

theorem prime_169787786867 : Nat.Prime 169787786867 := by
  apply nodeValid_prime [2, 251, 2851, 118633] ⟨169787786867, 2, [(2, 1), (251, 1), (2851, 1), (118633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_2851
    · exact prime_118633
  · decide +kernel

theorem prime_169787789609 : Nat.Prime 169787789609 := by
  apply nodeValid_prime [2, 1319, 16090579] ⟨169787789609, 3, [(2, 3), (1319, 1), (16090579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1319
    · exact prime_16090579
  · decide +kernel

theorem prime_170179787243 : Nat.Prime 170179787243 := by
  apply nodeValid_prime [2, 78517, 1083713] ⟨170179787243, 2, [(2, 1), (78517, 1), (1083713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_78517
    · exact prime_1083713
  · decide +kernel

theorem prime_170179803823 : Nat.Prime 170179803823 := by
  apply nodeValid_prime [2, 3, 7, 4051900091] ⟨170179803823, 3, [(2, 1), (3, 1), (7, 1), (4051900091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4051900091
  · decide +kernel

theorem prime_170179804051 : Nat.Prime 170179804051 := by
  apply nodeValid_prime [2, 3, 5, 1579, 718513] ⟨170179804051, 2, [(2, 1), (3, 1), (5, 2), (1579, 1), (718513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1579
    · exact prime_718513
  · decide +kernel

theorem prime_170572392407 : Nat.Prime 170572392407 := by
  apply nodeValid_prime [2, 13, 109, 1009, 59651] ⟨170572392407, 5, [(2, 1), (13, 1), (109, 1), (1009, 1), (59651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_109
    · exact prime_1009
    · exact prime_59651
  · decide +kernel

theorem prime_170572393547 : Nat.Prime 170572393547 := by
  apply nodeValid_prime [2, 29, 2940903337] ⟨170572393547, 2, [(2, 1), (29, 1), (2940903337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_2940903337
  · decide +kernel

theorem prime_170572398043 : Nat.Prime 170572398043 := by
  apply nodeValid_prime [2, 3, 28428733007] ⟨170572398043, 2, [(2, 1), (3, 1), (28428733007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28428733007
  · decide +kernel

theorem prime_170965611689 : Nat.Prime 170965611689 := by
  apply nodeValid_prime [2, 41, 59, 8834519] ⟨170965611689, 3, [(2, 3), (41, 1), (59, 1), (8834519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_59
    · exact prime_8834519
  · decide +kernel

theorem prime_170965612897 : Nat.Prime 170965612897 := by
  apply nodeValid_prime [2, 3, 13, 136991677] ⟨170965612897, 5, [(2, 5), (3, 1), (13, 1), (136991677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_136991677
  · decide +kernel

theorem prime_170965621819 : Nat.Prime 170965621819 := by
  apply nodeValid_prime [2, 3, 19, 103, 4853393] ⟨170965621819, 2, [(2, 1), (3, 2), (19, 1), (103, 1), (4853393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_103
    · exact prime_4853393
  · decide +kernel

theorem prime_171359464609 : Nat.Prime 171359464609 := by
  apply nodeValid_prime [2, 3, 269, 2211889] ⟨171359464609, 23, [(2, 5), (3, 2), (269, 1), (2211889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_2211889
  · decide +kernel

theorem prime_171359465177 : Nat.Prime 171359465177 := by
  apply nodeValid_prime [2, 3313, 6465419] ⟨171359465177, 3, [(2, 3), (3313, 1), (6465419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3313
    · exact prime_6465419
  · decide +kernel

theorem prime_171359465947 : Nat.Prime 171359465947 := by
  apply nodeValid_prime [2, 3, 28559910991] ⟨171359465947, 3, [(2, 1), (3, 1), (28559910991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28559910991
  · decide +kernel

theorem prime_171753930841 : Nat.Prime 171753930841 := by
  apply nodeValid_prime [2, 3, 5, 191, 7493627] ⟨171753930841, 14, [(2, 3), (3, 1), (5, 1), (191, 1), (7493627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
    · exact prime_7493627
  · decide +kernel

theorem prime_171753952199 : Nat.Prime 171753952199 := by
  apply nodeValid_prime [2, 769, 1699, 65729] ⟨171753952199, 7, [(2, 1), (769, 1), (1699, 1), (65729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_769
    · exact prime_1699
    · exact prime_65729
  · decide +kernel

theorem prime_171753952541 : Nat.Prime 171753952541 := by
  apply nodeValid_prime [2, 5, 157, 229, 238859] ⟨171753952541, 2, [(2, 2), (5, 1), (157, 1), (229, 1), (238859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_229
    · exact prime_238859
  · decide +kernel

theorem prime_172149002401 : Nat.Prime 172149002401 := by
  apply nodeValid_prime [2, 3, 5, 71728751] ⟨172149002401, 11, [(2, 5), (3, 1), (5, 2), (71728751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71728751
  · decide +kernel

theorem prime_172149002807 : Nat.Prime 172149002807 := by
  apply nodeValid_prime [2, 11, 41, 190852553] ⟨172149002807, 5, [(2, 1), (11, 1), (41, 1), (190852553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_190852553
  · decide +kernel

theorem prime_172149012773 : Nat.Prime 172149012773 := by
  apply nodeValid_prime [2, 11, 17, 230145739] ⟨172149012773, 2, [(2, 2), (11, 1), (17, 1), (230145739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_230145739
  · decide +kernel

theorem prime_172544652779 : Nat.Prime 172544652779 := by
  apply nodeValid_prime [2, 37, 2331684497] ⟨172544652779, 2, [(2, 1), (37, 1), (2331684497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2331684497
  · decide +kernel

theorem prime_172544653529 : Nat.Prime 172544653529 := by
  apply nodeValid_prime [2, 13, 1659083207] ⟨172544653529, 3, [(2, 3), (13, 1), (1659083207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1659083207
  · decide +kernel

theorem prime_172544712017 : Nat.Prime 172544712017 := by
  apply nodeValid_prime [2, 73, 83, 701, 2539] ⟨172544712017, 3, [(2, 4), (73, 1), (83, 1), (701, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_83
    · exact prime_701
    · exact prime_2539
  · decide +kernel

theorem prime_172941024281 : Nat.Prime 172941024281 := by
  apply nodeValid_prime [2, 5, 587, 7365461] ⟨172941024281, 3, [(2, 3), (5, 1), (587, 1), (7365461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_587
    · exact prime_7365461
  · decide +kernel

theorem prime_172941051923 : Nat.Prime 172941051923 := by
  apply nodeValid_prime [2, 265621, 325541] ⟨172941051923, 2, [(2, 1), (265621, 1), (325541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_265621
    · exact prime_325541
  · decide +kernel

theorem prime_172941054029 : Nat.Prime 172941054029 := by
  apply nodeValid_prime [2, 127133, 340079] ⟨172941054029, 2, [(2, 2), (127133, 1), (340079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127133
    · exact prime_340079
  · decide +kernel

theorem prime_173337943469 : Nat.Prime 173337943469 := by
  apply nodeValid_prime [2, 269, 161094743] ⟨173337943469, 2, [(2, 2), (269, 1), (161094743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_161094743
  · decide +kernel

theorem prime_173337943819 : Nat.Prime 173337943819 := by
  apply nodeValid_prime [2, 3, 13, 2222281331] ⟨173337943819, 10, [(2, 1), (3, 1), (13, 1), (2222281331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2222281331
  · decide +kernel

theorem prime_173337949693 : Nat.Prime 173337949693 := by
  apply nodeValid_prime [2, 3, 4814943047] ⟨173337949693, 2, [(2, 2), (3, 2), (4814943047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4814943047
  · decide +kernel

theorem prime_173735487157 : Nat.Prime 173735487157 := by
  apply nodeValid_prime [2, 3, 7, 11, 188025419] ⟨173735487157, 6, [(2, 2), (3, 1), (7, 1), (11, 1), (188025419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_188025419
  · decide +kernel

theorem prime_173735487349 : Nat.Prime 173735487349 := by
  apply nodeValid_prime [2, 3, 719, 20136241] ⟨173735487349, 2, [(2, 2), (3, 1), (719, 1), (20136241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
    · exact prime_20136241
  · decide +kernel

theorem prime_173735490979 : Nat.Prime 173735490979 := by
  apply nodeValid_prime [2, 3, 7, 5449, 84349] ⟨173735490979, 7, [(2, 1), (3, 3), (7, 1), (5449, 1), (84349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5449
    · exact prime_84349
  · decide +kernel

theorem prime_174133649633 : Nat.Prime 174133649633 := by
  apply nodeValid_prime [2, 19, 29, 67, 223, 661] ⟨174133649633, 5, [(2, 5), (19, 1), (29, 1), (67, 1), (223, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_67
    · exact prime_223
    · exact prime_661
  · decide +kernel

theorem prime_174133655177 : Nat.Prime 174133655177 := by
  apply nodeValid_prime [2, 13, 1674362069] ⟨174133655177, 3, [(2, 3), (13, 1), (1674362069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1674362069
  · decide +kernel

theorem prime_174133658411 : Nat.Prime 174133658411 := by
  apply nodeValid_prime [2, 5, 19, 916492939] ⟨174133658411, 2, [(2, 1), (5, 1), (19, 1), (916492939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_916492939
  · decide +kernel

theorem prime_174532395691 : Nat.Prime 174532395691 := by
  apply nodeValid_prime [2, 3, 5, 23, 251, 335917] ⟨174532395691, 2, [(2, 1), (3, 2), (5, 1), (23, 1), (251, 1), (335917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_251
    · exact prime_335917
  · decide +kernel

theorem prime_174532396757 : Nat.Prime 174532396757 := by
  apply nodeValid_prime [2, 14939, 2920751] ⟨174532396757, 2, [(2, 2), (14939, 1), (2920751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_14939
    · exact prime_2920751
  · decide +kernel

theorem prime_174532428101 : Nat.Prime 174532428101 := by
  apply nodeValid_prime [2, 5, 271, 6440311] ⟨174532428101, 2, [(2, 2), (5, 2), (271, 1), (6440311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
    · exact prime_6440311
  · decide +kernel

theorem prime_174931822411 : Nat.Prime 174931822411 := by
  apply nodeValid_prime [2, 3, 5, 5831060747] ⟨174931822411, 3, [(2, 1), (3, 1), (5, 1), (5831060747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5831060747
  · decide +kernel

theorem prime_174931826137 : Nat.Prime 174931826137 := by
  apply nodeValid_prime [2, 3, 97, 1021, 73597] ⟨174931826137, 5, [(2, 3), (3, 1), (97, 1), (1021, 1), (73597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1021
    · exact prime_73597
  · decide +kernel

theorem prime_174931826431 : Nat.Prime 174931826431 := by
  apply nodeValid_prime [2, 3, 5, 43, 457, 296731] ⟨174931826431, 3, [(2, 1), (3, 1), (5, 1), (43, 1), (457, 1), (296731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_457
    · exact prime_296731
  · decide +kernel

theorem prime_175331838191 : Nat.Prime 175331838191 := by
  apply nodeValid_prime [2, 5, 17533183819] ⟨175331838191, 11, [(2, 1), (5, 1), (17533183819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17533183819
  · decide +kernel

theorem prime_175331839673 : Nat.Prime 175331839673 := by
  apply nodeValid_prime [2, 11, 23, 5689, 15227] ⟨175331839673, 3, [(2, 3), (11, 1), (23, 1), (5689, 1), (15227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_5689
    · exact prime_15227
  · decide +kernel

theorem prime_175331841137 : Nat.Prime 175331841137 := by
  apply nodeValid_prime [2, 8573, 1278227] ⟨175331841137, 3, [(2, 4), (8573, 1), (1278227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8573
    · exact prime_1278227
  · decide +kernel

theorem prime_175732479001 : Nat.Prime 175732479001 := by
  apply nodeValid_prime [2, 3, 5, 13, 1193, 1259] ⟨175732479001, 11, [(2, 3), (3, 2), (5, 3), (13, 1), (1193, 1), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1193
    · exact prime_1259
  · decide +kernel

theorem prime_175732479743 : Nat.Prime 175732479743 := by
  apply nodeValid_prime [2, 101, 869962771] ⟨175732479743, 5, [(2, 1), (101, 1), (869962771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_869962771
  · decide +kernel

theorem prime_175732480433 : Nat.Prime 175732480433 := by
  apply nodeValid_prime [2, 97, 2143, 52837] ⟨175732480433, 3, [(2, 4), (97, 1), (2143, 1), (52837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_2143
    · exact prime_52837
  · decide +kernel

theorem prime_176133741053 : Nat.Prime 176133741053 := by
  apply nodeValid_prime [2, 251, 4943, 35491] ⟨176133741053, 2, [(2, 2), (251, 1), (4943, 1), (35491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_4943
    · exact prime_35491
  · decide +kernel

theorem prime_176133761239 : Nat.Prime 176133761239 := by
  apply nodeValid_prime [2, 3, 29355626873] ⟨176133761239, 3, [(2, 1), (3, 1), (29355626873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29355626873
  · decide +kernel

theorem prime_176133762031 : Nat.Prime 176133762031 := by
  apply nodeValid_prime [2, 3, 5, 467, 12572003] ⟨176133762031, 3, [(2, 1), (3, 1), (5, 1), (467, 1), (12572003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
    · exact prime_12572003
  · decide +kernel

theorem prime_176535622693 : Nat.Prime 176535622693 := by
  apply nodeValid_prime [2, 3, 11, 13, 181, 2339] ⟨176535622693, 5, [(2, 2), (3, 6), (11, 1), (13, 1), (181, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_181
    · exact prime_2339
  · decide +kernel

theorem prime_176535637259 : Nat.Prime 176535637259 := by
  apply nodeValid_prime [2, 88267818629] ⟨176535637259, 2, [(2, 1), (88267818629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_88267818629
  · decide +kernel

theorem prime_176535637367 : Nat.Prime 176535637367 := by
  apply nodeValid_prime [2, 11, 8669, 925637] ⟨176535637367, 5, [(2, 1), (11, 1), (8669, 1), (925637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8669
    · exact prime_925637
  · decide +kernel

theorem prime_176938128067 : Nat.Prime 176938128067 := by
  apply nodeValid_prime [2, 3, 7, 3469, 1214417] ⟨176938128067, 2, [(2, 1), (3, 1), (7, 1), (3469, 1), (1214417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3469
    · exact prime_1214417
  · decide +kernel

theorem prime_176938136279 : Nat.Prime 176938136279 := by
  apply nodeValid_prime [2, 73, 2503, 484181] ⟨176938136279, 7, [(2, 1), (73, 1), (2503, 1), (484181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_2503
    · exact prime_484181
  · decide +kernel

theorem prime_176938136659 : Nat.Prime 176938136659 := by
  apply nodeValid_prime [2, 3, 9829896481] ⟨176938136659, 3, [(2, 1), (3, 2), (9829896481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9829896481
  · decide +kernel

theorem prime_177341254703 : Nat.Prime 177341254703 := by
  apply nodeValid_prime [2, 59, 239, 983, 6397] ⟨177341254703, 5, [(2, 1), (59, 1), (239, 1), (983, 1), (6397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_239
    · exact prime_983
    · exact prime_6397
  · decide +kernel

theorem prime_177341263843 : Nat.Prime 177341263843 := by
  apply nodeValid_prime [2, 3, 29556877307] ⟨177341263843, 2, [(2, 1), (3, 1), (29556877307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29556877307
  · decide +kernel

theorem prime_177341264281 : Nat.Prime 177341264281 := by
  apply nodeValid_prime [2, 3, 5, 179, 487, 5651] ⟨177341264281, 7, [(2, 3), (3, 2), (5, 1), (179, 1), (487, 1), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_487
    · exact prime_5651
  · decide +kernel

theorem prime_177745005371 : Nat.Prime 177745005371 := by
  apply nodeValid_prime [2, 5, 5147, 3453371] ⟨177745005371, 2, [(2, 1), (5, 1), (5147, 1), (3453371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5147
    · exact prime_3453371
  · decide +kernel

theorem prime_177745014521 : Nat.Prime 177745014521 := by
  apply nodeValid_prime [2, 5, 107, 41529209] ⟨177745014521, 3, [(2, 3), (5, 1), (107, 1), (41529209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_41529209
  · decide +kernel

theorem prime_177745014857 : Nat.Prime 177745014857 := by
  apply nodeValid_prime [2, 22218126857] ⟨177745014857, 3, [(2, 3), (22218126857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22218126857
  · decide +kernel

end Sude.Lucas.Generated
