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
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0077

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10903 : Nat.Prime 10903 := by
  apply nodeValid_prime [2, 3, 23, 79] ⟨10903, 3, [(2, 1), (3, 1), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_12251 : Nat.Prime 12251 := by
  apply nodeValid_prime [2, 5, 7] ⟨12251, 2, [(2, 1), (5, 3), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_12941 : Nat.Prime 12941 := by
  apply nodeValid_prime [2, 5, 647] ⟨12941, 2, [(2, 2), (5, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_647
  · decide +kernel

theorem prime_20887 : Nat.Prime 20887 := by
  apply nodeValid_prime [2, 3, 59] ⟨20887, 3, [(2, 1), (3, 1), (59, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_23063 : Nat.Prime 23063 := by
  apply nodeValid_prime [2, 13, 887] ⟨23063, 5, [(2, 1), (13, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_887
  · decide +kernel

theorem prime_24077 : Nat.Prime 24077 := by
  apply nodeValid_prime [2, 13, 463] ⟨24077, 2, [(2, 2), (13, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_463
  · decide +kernel

theorem prime_37997 : Nat.Prime 37997 := by
  apply nodeValid_prime [2, 7, 23, 59] ⟨37997, 2, [(2, 2), (7, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_41243 : Nat.Prime 41243 := by
  apply nodeValid_prime [2, 17, 1213] ⟨41243, 2, [(2, 1), (17, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1213
  · decide +kernel

theorem prime_51893 : Nat.Prime 51893 := by
  apply nodeValid_prime [2, 12973] ⟨51893, 2, [(2, 2), (12973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12973
  · decide +kernel

theorem prime_53527 : Nat.Prime 53527 := by
  apply nodeValid_prime [2, 3, 11, 811] ⟨53527, 3, [(2, 1), (3, 1), (11, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_811
  · decide +kernel

theorem prime_55763 : Nat.Prime 55763 := by
  apply nodeValid_prime [2, 7, 569] ⟨55763, 2, [(2, 1), (7, 2), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_569
  · decide +kernel

theorem prime_57773 : Nat.Prime 57773 := by
  apply nodeValid_prime [2, 11, 13, 101] ⟨57773, 3, [(2, 2), (11, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_60383 : Nat.Prime 60383 := by
  apply nodeValid_prime [2, 7, 19, 227] ⟨60383, 5, [(2, 1), (7, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_65419 : Nat.Prime 65419 := by
  apply nodeValid_prime [2, 3, 10903] ⟨65419, 3, [(2, 1), (3, 1), (10903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10903
  · decide +kernel

theorem prime_68477 : Nat.Prime 68477 := by
  apply nodeValid_prime [2, 17, 19, 53] ⟨68477, 2, [(2, 2), (17, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_70667 : Nat.Prime 70667 := by
  apply nodeValid_prime [2, 89, 397] ⟨70667, 2, [(2, 1), (89, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_397
  · decide +kernel

theorem prime_73243 : Nat.Prime 73243 := by
  apply nodeValid_prime [2, 3, 13, 313] ⟨73243, 3, [(2, 1), (3, 2), (13, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_313
  · decide +kernel

theorem prime_73529 : Nat.Prime 73529 := by
  apply nodeValid_prime [2, 7, 13, 101] ⟨73529, 3, [(2, 3), (7, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_79111 : Nat.Prime 79111 := by
  apply nodeValid_prime [2, 3, 5, 293] ⟨79111, 6, [(2, 1), (3, 3), (5, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
  · decide +kernel

theorem prime_82811 : Nat.Prime 82811 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨82811, 2, [(2, 1), (5, 1), (7, 2), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_84991 : Nat.Prime 84991 := by
  apply nodeValid_prime [2, 3, 5, 2833] ⟨84991, 3, [(2, 1), (3, 1), (5, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2833
  · decide +kernel

theorem prime_88861 : Nat.Prime 88861 := by
  apply nodeValid_prime [2, 3, 5, 1481] ⟨88861, 2, [(2, 2), (3, 1), (5, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1481
  · decide +kernel

theorem prime_91801 : Nat.Prime 91801 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨91801, 13, [(2, 3), (3, 3), (5, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_98009 : Nat.Prime 98009 := by
  apply nodeValid_prime [2, 12251] ⟨98009, 3, [(2, 3), (12251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12251
  · decide +kernel

theorem prime_103787 : Nat.Prime 103787 := by
  apply nodeValid_prime [2, 51893] ⟨103787, 2, [(2, 1), (51893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_51893
  · decide +kernel

theorem prime_115547 : Nat.Prime 115547 := by
  apply nodeValid_prime [2, 57773] ⟨115547, 2, [(2, 1), (57773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57773
  · decide +kernel

theorem prime_122719 : Nat.Prime 122719 := by
  apply nodeValid_prime [2, 3, 113, 181] ⟨122719, 3, [(2, 1), (3, 1), (113, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_181
  · decide +kernel

theorem prime_144161 : Nat.Prime 144161 := by
  apply nodeValid_prime [2, 5, 17, 53] ⟨144161, 3, [(2, 5), (5, 1), (17, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_53
  · decide +kernel

theorem prime_145969 : Nat.Prime 145969 := by
  apply nodeValid_prime [2, 3, 3041] ⟨145969, 13, [(2, 4), (3, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3041
  · decide +kernel

theorem prime_179807 : Nat.Prime 179807 := by
  apply nodeValid_prime [2, 11, 743] ⟨179807, 5, [(2, 1), (11, 2), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_743
  · decide +kernel

theorem prime_190181 : Nat.Prime 190181 := by
  apply nodeValid_prime [2, 5, 37, 257] ⟨190181, 2, [(2, 2), (5, 1), (37, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_257
  · decide +kernel

theorem prime_192617 : Nat.Prime 192617 := by
  apply nodeValid_prime [2, 24077] ⟨192617, 3, [(2, 3), (24077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24077
  · decide +kernel

theorem prime_192629 : Nat.Prime 192629 := by
  apply nodeValid_prime [2, 48157] ⟨192629, 2, [(2, 2), (48157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48157
  · decide +kernel

theorem prime_250837 : Nat.Prime 250837 := by
  apply nodeValid_prime [2, 3, 20903] ⟨250837, 7, [(2, 2), (3, 1), (20903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20903
  · decide +kernel

theorem prime_263047 : Nat.Prime 263047 := by
  apply nodeValid_prime [2, 3, 7, 6263] ⟨263047, 3, [(2, 1), (3, 1), (7, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6263
  · decide +kernel

theorem prime_380363 : Nat.Prime 380363 := by
  apply nodeValid_prime [2, 190181] ⟨380363, 2, [(2, 1), (190181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_190181
  · decide +kernel

theorem prime_395671 : Nat.Prime 395671 := by
  apply nodeValid_prime [2, 3, 5, 11, 109] ⟨395671, 15, [(2, 1), (3, 1), (5, 1), (11, 2), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_451859 : Nat.Prime 451859 := by
  apply nodeValid_prime [2, 11, 19, 23, 47] ⟨451859, 6, [(2, 1), (11, 1), (19, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_465721 : Nat.Prime 465721 := by
  apply nodeValid_prime [2, 3, 5, 3881] ⟨465721, 17, [(2, 3), (3, 1), (5, 1), (3881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3881
  · decide +kernel

theorem prime_494917 : Nat.Prime 494917 := by
  apply nodeValid_prime [2, 3, 41243] ⟨494917, 2, [(2, 2), (3, 1), (41243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41243
  · decide +kernel

theorem prime_533413 : Nat.Prime 533413 := by
  apply nodeValid_prime [2, 3, 11, 449] ⟨533413, 2, [(2, 2), (3, 3), (11, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_449
  · decide +kernel

theorem prime_551423 : Nat.Prime 551423 := by
  apply nodeValid_prime [2, 275711] ⟨551423, 5, [(2, 1), (275711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_275711
  · decide +kernel

theorem prime_621799 : Nat.Prime 621799 := by
  apply nodeValid_prime [2, 3, 31, 3343] ⟨621799, 3, [(2, 1), (3, 1), (31, 1), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3343
  · decide +kernel

theorem prime_654191 : Nat.Prime 654191 := by
  apply nodeValid_prime [2, 5, 65419] ⟨654191, 23, [(2, 1), (5, 1), (65419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_65419
  · decide +kernel

theorem prime_663209 : Nat.Prime 663209 := by
  apply nodeValid_prime [2, 7, 13, 911] ⟨663209, 6, [(2, 3), (7, 1), (13, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_911
  · decide +kernel

theorem prime_672473 : Nat.Prime 672473 := by
  apply nodeValid_prime [2, 84059] ⟨672473, 3, [(2, 3), (84059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84059
  · decide +kernel

theorem prime_673549 : Nat.Prime 673549 := by
  apply nodeValid_prime [2, 3, 37, 41] ⟨673549, 11, [(2, 2), (3, 1), (37, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_735571 : Nat.Prime 735571 := by
  apply nodeValid_prime [2, 3, 5, 11, 743] ⟨735571, 7, [(2, 1), (3, 2), (5, 1), (11, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_743
  · decide +kernel

theorem prime_796487 : Nat.Prime 796487 := by
  apply nodeValid_prime [2, 101, 3943] ⟨796487, 5, [(2, 1), (101, 1), (3943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_3943
  · decide +kernel

theorem prime_894643 : Nat.Prime 894643 := by
  apply nodeValid_prime [2, 3, 7, 17, 179] ⟨894643, 2, [(2, 1), (3, 1), (7, 2), (17, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_179
  · decide +kernel

theorem prime_939359 : Nat.Prime 939359 := by
  apply nodeValid_prime [2, 7, 229, 293] ⟨939359, 7, [(2, 1), (7, 1), (229, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_229
    · exact prime_293
  · decide +kernel

theorem prime_1155703 : Nat.Prime 1155703 := by
  apply nodeValid_prime [2, 3, 192617] ⟨1155703, 6, [(2, 1), (3, 1), (192617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_192617
  · decide +kernel

theorem prime_1337801 : Nat.Prime 1337801 := by
  apply nodeValid_prime [2, 5, 6689] ⟨1337801, 3, [(2, 3), (5, 2), (6689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6689
  · decide +kernel

theorem prime_1369541 : Nat.Prime 1369541 := by
  apply nodeValid_prime [2, 5, 68477] ⟨1369541, 2, [(2, 2), (5, 1), (68477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_68477
  · decide +kernel

theorem prime_1708321 : Nat.Prime 1708321 := by
  apply nodeValid_prime [2, 3, 5, 3559] ⟨1708321, 14, [(2, 5), (3, 1), (5, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3559
  · decide +kernel

theorem prime_2035531 : Nat.Prime 2035531 := by
  apply nodeValid_prime [2, 3, 5, 7, 359] ⟨2035531, 2, [(2, 1), (3, 4), (5, 1), (7, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_359
  · decide +kernel

theorem prime_2235869 : Nat.Prime 2235869 := by
  apply nodeValid_prime [2, 233, 2399] ⟨2235869, 2, [(2, 2), (233, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_2399
  · decide +kernel

theorem prime_2549731 : Nat.Prime 2549731 := by
  apply nodeValid_prime [2, 3, 5, 84991] ⟨2549731, 3, [(2, 1), (3, 1), (5, 1), (84991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_84991
  · decide +kernel

theorem prime_2563343 : Nat.Prime 2563343 := by
  apply nodeValid_prime [2, 61, 21011] ⟨2563343, 5, [(2, 1), (61, 1), (21011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_21011
  · decide +kernel

theorem prime_2940271 : Nat.Prime 2940271 := by
  apply nodeValid_prime [2, 3, 5, 98009] ⟨2940271, 3, [(2, 1), (3, 1), (5, 1), (98009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_98009
  · decide +kernel

theorem prime_3109349 : Nat.Prime 3109349 := by
  apply nodeValid_prime [2, 11, 70667] ⟨3109349, 3, [(2, 2), (11, 1), (70667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_70667
  · decide +kernel

theorem prime_3167453 : Nat.Prime 3167453 := by
  apply nodeValid_prime [2, 19, 71, 587] ⟨3167453, 2, [(2, 2), (19, 1), (71, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71
    · exact prime_587
  · decide +kernel

theorem prime_3250283 : Nat.Prime 3250283 := by
  apply nodeValid_prime [2, 7, 179, 1297] ⟨3250283, 2, [(2, 1), (7, 1), (179, 1), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_179
    · exact prime_1297
  · decide +kernel

theorem prime_4113773 : Nat.Prime 4113773 := by
  apply nodeValid_prime [2, 13, 79111] ⟨4113773, 2, [(2, 2), (13, 1), (79111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79111
  · decide +kernel

theorem prime_4115239 : Nat.Prime 4115239 := by
  apply nodeValid_prime [2, 3, 53, 12941] ⟨4115239, 3, [(2, 1), (3, 1), (53, 1), (12941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_12941
  · decide +kernel

theorem prime_4315369 : Nat.Prime 4315369 := by
  apply nodeValid_prime [2, 3, 179807] ⟨4315369, 13, [(2, 3), (3, 1), (179807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179807
  · decide +kernel

theorem prime_5655929 : Nat.Prime 5655929 := by
  apply nodeValid_prime [2, 29, 24379] ⟨5655929, 3, [(2, 3), (29, 1), (24379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_24379
  · decide +kernel

theorem prime_6400957 : Nat.Prime 6400957 := by
  apply nodeValid_prime [2, 3, 533413] ⟨6400957, 6, [(2, 2), (3, 1), (533413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_533413
  · decide +kernel

theorem prime_9208417 : Nat.Prime 9208417 := by
  apply nodeValid_prime [2, 3, 7, 71, 193] ⟨9208417, 5, [(2, 5), (3, 1), (7, 1), (71, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_193
  · decide +kernel

theorem prime_9249353 : Nat.Prime 9249353 := by
  apply nodeValid_prime [2, 7, 19, 8693] ⟨9249353, 3, [(2, 3), (7, 1), (19, 1), (8693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_8693
  · decide +kernel

theorem prime_9371701 : Nat.Prime 9371701 := by
  apply nodeValid_prime [2, 3, 5, 13, 89] ⟨9371701, 2, [(2, 2), (3, 4), (5, 2), (13, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_89
  · decide +kernel

theorem prime_10025569 : Nat.Prime 10025569 := by
  apply nodeValid_prime [2, 3, 7, 4973] ⟨10025569, 13, [(2, 5), (3, 2), (7, 1), (4973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4973
  · decide +kernel

theorem prime_11301221 : Nat.Prime 11301221 := by
  apply nodeValid_prime [2, 5, 7, 89, 907] ⟨11301221, 2, [(2, 2), (5, 1), (7, 1), (89, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_89
    · exact prime_907
  · decide +kernel

theorem prime_15419557 : Nat.Prime 15419557 := by
  apply nodeValid_prime [2, 3, 107, 4003] ⟨15419557, 2, [(2, 2), (3, 2), (107, 1), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_4003
  · decide +kernel

theorem prime_15929741 : Nat.Prime 15929741 := by
  apply nodeValid_prime [2, 5, 796487] ⟨15929741, 2, [(2, 2), (5, 1), (796487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_796487
  · decide +kernel

theorem prime_16364071 : Nat.Prime 16364071 := by
  apply nodeValid_prime [2, 3, 5, 173, 1051] ⟨16364071, 6, [(2, 1), (3, 2), (5, 1), (173, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_1051
  · decide +kernel

theorem prime_17129857 : Nat.Prime 17129857 := by
  apply nodeValid_prime [2, 3, 31, 1439] ⟨17129857, 5, [(2, 7), (3, 1), (31, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1439
  · decide +kernel

theorem prime_19526629 : Nat.Prime 19526629 := by
  apply nodeValid_prime [2, 3, 11, 29, 5101] ⟨19526629, 2, [(2, 2), (3, 1), (11, 1), (29, 1), (5101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_5101
  · decide +kernel

theorem prime_23740261 : Nat.Prime 23740261 := by
  apply nodeValid_prime [2, 3, 5, 395671] ⟨23740261, 2, [(2, 2), (3, 1), (5, 1), (395671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_395671
  · decide +kernel

theorem prime_25027399 : Nat.Prime 25027399 := by
  apply nodeValid_prime [2, 3, 11, 11491] ⟨25027399, 6, [(2, 1), (3, 2), (11, 2), (11491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_11491
  · decide +kernel

theorem prime_27979933 : Nat.Prime 27979933 := by
  apply nodeValid_prime [2, 3, 19, 122719] ⟨27979933, 5, [(2, 2), (3, 1), (19, 1), (122719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_122719
  · decide +kernel

theorem prime_29695021 : Nat.Prime 29695021 := by
  apply nodeValid_prime [2, 3, 5, 494917] ⟨29695021, 2, [(2, 2), (3, 1), (5, 1), (494917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_494917
  · decide +kernel

theorem prime_35807557 : Nat.Prime 35807557 := by
  apply nodeValid_prime [2, 3, 223, 13381] ⟨35807557, 2, [(2, 2), (3, 1), (223, 1), (13381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_13381
  · decide +kernel

theorem prime_50725387 : Nat.Prime 50725387 := by
  apply nodeValid_prime [2, 3, 939359] ⟨50725387, 2, [(2, 1), (3, 3), (939359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_939359
  · decide +kernel

theorem prime_60619411 : Nat.Prime 60619411 := by
  apply nodeValid_prime [2, 3, 5, 673549] ⟨60619411, 2, [(2, 1), (3, 2), (5, 1), (673549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_673549
  · decide +kernel

theorem prime_61678229 : Nat.Prime 61678229 := by
  apply nodeValid_prime [2, 15419557] ⟨61678229, 2, [(2, 2), (15419557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15419557
  · decide +kernel

theorem prime_90970469 : Nat.Prime 90970469 := by
  apply nodeValid_prime [2, 17, 1337801] ⟨90970469, 2, [(2, 2), (17, 1), (1337801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1337801
  · decide +kernel

theorem prime_107797133 : Nat.Prime 107797133 := by
  apply nodeValid_prime [2, 37, 47, 15497] ⟨107797133, 2, [(2, 2), (37, 1), (47, 1), (15497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_47
    · exact prime_15497
  · decide +kernel

theorem prime_147988163 : Nat.Prime 147988163 := by
  apply nodeValid_prime [2, 7, 17, 621799] ⟨147988163, 2, [(2, 1), (7, 1), (17, 1), (621799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_621799
  · decide +kernel

theorem prime_201725483 : Nat.Prime 201725483 := by
  apply nodeValid_prime [2, 7, 101, 179, 797] ⟨201725483, 2, [(2, 1), (7, 1), (101, 1), (179, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_179
    · exact prime_797
  · decide +kernel

theorem prime_309758923 : Nat.Prime 309758923 := by
  apply nodeValid_prime [2, 3, 11, 173, 9043] ⟨309758923, 2, [(2, 1), (3, 2), (11, 1), (173, 1), (9043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_173
    · exact prime_9043
  · decide +kernel

theorem prime_331037381 : Nat.Prime 331037381 := by
  apply nodeValid_prime [2, 5, 19, 191, 4561] ⟨331037381, 2, [(2, 2), (5, 1), (19, 1), (191, 1), (4561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_191
    · exact prime_4561
  · decide +kernel

theorem prime_544561067 : Nat.Prime 544561067 := by
  apply nodeValid_prime [2, 7, 31, 251, 4999] ⟨544561067, 2, [(2, 1), (7, 1), (31, 1), (251, 1), (4999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_251
    · exact prime_4999
  · decide +kernel

theorem prime_592756111 : Nat.Prime 592756111 := by
  apply nodeValid_prime [2, 3, 5, 19, 115547] ⟨592756111, 3, [(2, 1), (3, 3), (5, 1), (19, 1), (115547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_115547
  · decide +kernel

theorem prime_675295451 : Nat.Prime 675295451 := by
  apply nodeValid_prime [2, 5, 29, 465721] ⟨675295451, 2, [(2, 1), (5, 2), (29, 1), (465721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_465721
  · decide +kernel

theorem prime_1110208123 : Nat.Prime 1110208123 := by
  apply nodeValid_prime [2, 3, 61678229] ⟨1110208123, 2, [(2, 1), (3, 2), (61678229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61678229
  · decide +kernel

theorem prime_1788710953 : Nat.Prime 1788710953 := by
  apply nodeValid_prime [2, 3, 7, 29, 71, 5171] ⟨1788710953, 5, [(2, 3), (3, 1), (7, 1), (29, 1), (71, 1), (5171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_71
    · exact prime_5171
  · decide +kernel

theorem prime_2378479777 : Nat.Prime 2378479777 := by
  apply nodeValid_prime [2, 3, 29, 211, 4049] ⟨2378479777, 5, [(2, 5), (3, 1), (29, 1), (211, 1), (4049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_211
    · exact prime_4049
  · decide +kernel

theorem prime_3551041969 : Nat.Prime 3551041969 := by
  apply nodeValid_prime [2, 3, 59, 199, 6301] ⟨3551041969, 7, [(2, 4), (3, 1), (59, 1), (199, 1), (6301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_199
    · exact prime_6301
  · decide +kernel

theorem prime_4179685109 : Nat.Prime 4179685109 := by
  apply nodeValid_prime [2, 61, 17129857] ⟨4179685109, 2, [(2, 2), (61, 1), (17129857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_17129857
  · decide +kernel

theorem prime_4440832493 : Nat.Prime 4440832493 := by
  apply nodeValid_prime [2, 1110208123] ⟨4440832493, 2, [(2, 2), (1110208123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1110208123
  · decide +kernel

theorem prime_4476789281 : Nat.Prime 4476789281 := by
  apply nodeValid_prime [2, 5, 27979933] ⟨4476789281, 3, [(2, 5), (5, 1), (27979933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_27979933
  · decide +kernel

theorem prime_5038426951 : Nat.Prime 5038426951 := by
  apply nodeValid_prime [2, 3, 5, 233, 144161] ⟨5038426951, 3, [(2, 1), (3, 1), (5, 2), (233, 1), (144161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233
    · exact prime_144161
  · decide +kernel

theorem prime_8458088017 : Nat.Prime 8458088017 := by
  apply nodeValid_prime [2, 3, 7, 59, 331, 1289] ⟨8458088017, 5, [(2, 4), (3, 1), (7, 1), (59, 1), (331, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_331
    · exact prime_1289
  · decide +kernel

theorem prime_15621408967 : Nat.Prime 15621408967 := by
  apply nodeValid_prime [2, 3, 79, 359, 91801] ⟨15621408967, 3, [(2, 1), (3, 1), (79, 1), (359, 1), (91801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_359
    · exact prime_91801
  · decide +kernel

theorem prime_16784150029 : Nat.Prime 16784150029 := by
  apply nodeValid_prime [2, 3, 53, 137, 192629] ⟨16784150029, 6, [(2, 2), (3, 1), (53, 1), (137, 1), (192629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_137
    · exact prime_192629
  · decide +kernel

theorem prime_23963016331 : Nat.Prime 23963016331 := by
  apply nodeValid_prime [2, 3, 5, 11, 37, 654191] ⟨23963016331, 7, [(2, 1), (3, 2), (5, 1), (11, 1), (37, 1), (654191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_654191
  · decide +kernel

theorem prime_94166712593 : Nat.Prime 94166712593 := by
  apply nodeValid_prime [2, 19, 309758923] ⟨94166712593, 3, [(2, 4), (19, 1), (309758923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_309758923
  · decide +kernel

theorem prime_142041678761 : Nat.Prime 142041678761 := by
  apply nodeValid_prime [2, 5, 3551041969] ⟨142041678761, 3, [(2, 3), (5, 1), (3551041969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3551041969
  · decide +kernel

theorem prime_202916677013 : Nat.Prime 202916677013 := by
  apply nodeValid_prime [2, 7, 787, 9208417] ⟨202916677013, 2, [(2, 2), (7, 1), (787, 1), (9208417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_787
    · exact prime_9208417
  · decide +kernel

theorem prime_698379127837 : Nat.Prime 698379127837 := by
  apply nodeValid_prime [2, 3, 13, 4476789281] ⟨698379127837, 6, [(2, 2), (3, 1), (13, 1), (4476789281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4476789281
  · decide +kernel

theorem prime_704934301219 : Nat.Prime 704934301219 := by
  apply nodeValid_prime [2, 3, 7, 16784150029] ⟨704934301219, 2, [(2, 1), (3, 1), (7, 1), (16784150029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_16784150029
  · decide +kernel

theorem prime_1408553852879 : Nat.Prime 1408553852879 := by
  apply nodeValid_prime [2, 43, 67, 541, 451859] ⟨1408553852879, 29, [(2, 1), (43, 1), (67, 1), (541, 1), (451859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_67
    · exact prime_541
    · exact prime_451859
  · decide +kernel

theorem prime_1415136041849 : Nat.Prime 1415136041849 := by
  apply nodeValid_prime [2, 263047, 672473] ⟨1415136041849, 3, [(2, 3), (263047, 1), (672473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_263047
    · exact prime_672473
  · decide +kernel

theorem prime_1423062141899 : Nat.Prime 1423062141899 := by
  apply nodeValid_prime [2, 487, 2203, 663209] ⟨1423062141899, 2, [(2, 1), (487, 1), (2203, 1), (663209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_2203
    · exact prime_663209
  · decide +kernel

theorem prime_2793516462041 : Nat.Prime 2793516462041 := by
  apply nodeValid_prime [2, 5, 23, 37, 991, 82811] ⟨2793516462041, 3, [(2, 3), (5, 1), (23, 1), (37, 1), (991, 1), (82811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_991
    · exact prime_82811
  · decide +kernel

theorem prime_2793516511349 : Nat.Prime 2793516511349 := by
  apply nodeValid_prime [2, 698379127837] ⟨2793516511349, 2, [(2, 2), (698379127837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_698379127837
  · decide +kernel

theorem prime_2793516511871 : Nat.Prime 2793516511871 := by
  apply nodeValid_prime [2, 5, 7, 41, 23740261] ⟨2793516511871, 7, [(2, 1), (5, 1), (7, 1), (41, 2), (23740261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_23740261
  · decide +kernel

theorem prime_2796130951787 : Nat.Prime 2796130951787 := by
  apply nodeValid_prime [2, 23063, 60619411] ⟨2796130951787, 2, [(2, 1), (23063, 1), (60619411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23063
    · exact prime_60619411
  · decide +kernel

theorem prime_2796130952261 : Nat.Prime 2796130952261 := by
  apply nodeValid_prime [2, 5, 137, 883, 1155703] ⟨2796130952261, 2, [(2, 2), (5, 1), (137, 1), (883, 1), (1155703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_883
    · exact prime_1155703
  · decide +kernel

theorem prime_2796131095319 : Nat.Prime 2796131095319 := by
  apply nodeValid_prime [2, 11, 41, 131, 4639, 5101] ⟨2796131095319, 7, [(2, 1), (11, 1), (41, 1), (131, 1), (4639, 1), (5101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_131
    · exact prime_4639
    · exact prime_5101
  · decide +kernel

theorem prime_2798747380651 : Nat.Prime 2798747380651 := by
  apply nodeValid_prime [2, 3, 5, 13, 127, 11301221] ⟨2798747380651, 3, [(2, 1), (3, 1), (5, 2), (13, 1), (127, 1), (11301221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_127
    · exact prime_11301221
  · decide +kernel

theorem prime_2798747423207 : Nat.Prime 2798747423207 := by
  apply nodeValid_prime [2, 7, 145969, 1369541] ⟨2798747423207, 5, [(2, 1), (7, 1), (145969, 1), (1369541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_145969
    · exact prime_1369541
  · decide +kernel

theorem prime_2798747424223 : Nat.Prime 2798747424223 := by
  apply nodeValid_prime [2, 3, 53, 211, 1997, 20887] ⟨2798747424223, 3, [(2, 1), (3, 1), (53, 1), (211, 1), (1997, 1), (20887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_211
    · exact prime_1997
    · exact prime_20887
  · decide +kernel

theorem prime_2801365314491 : Nat.Prime 2801365314491 := by
  apply nodeValid_prime [2, 5, 17, 19, 53, 16364071] ⟨2801365314491, 2, [(2, 1), (5, 1), (17, 1), (19, 1), (53, 1), (16364071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_53
    · exact prime_16364071
  · decide +kernel

theorem prime_2801365380587 : Nat.Prime 2801365380587 := by
  apply nodeValid_prime [2, 17, 139, 592756111] ⟨2801365380587, 2, [(2, 1), (17, 1), (139, 1), (592756111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_139
    · exact prime_592756111
  · decide +kernel

theorem prime_2801365384757 : Nat.Prime 2801365384757 := by
  apply nodeValid_prime [2, 139, 5038426951] ⟨2801365384757, 2, [(2, 2), (139, 1), (5038426951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_5038426951
  · decide +kernel

theorem prime_2803984870303 : Nat.Prime 2803984870303 := by
  apply nodeValid_prime [2, 3, 7, 11, 127, 15929741] ⟨2803984870303, 3, [(2, 1), (3, 2), (7, 1), (11, 1), (127, 1), (15929741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_127
    · exact prime_15929741
  · decide +kernel

theorem prime_2803984871143 : Nat.Prime 2803984871143 := by
  apply nodeValid_prime [2, 3, 7, 13, 263, 19526629] ⟨2803984871143, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (263, 1), (19526629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_263
    · exact prime_19526629
  · decide +kernel

theorem prime_2803984902937 : Nat.Prime 2803984902937 := by
  apply nodeValid_prime [2, 3, 7, 17, 29, 79, 211, 677] ⟨2803984902937, 5, [(2, 3), (3, 2), (7, 1), (17, 1), (29, 1), (79, 1), (211, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_29
    · exact prime_79
    · exact prime_211
    · exact prime_677
  · decide +kernel

theorem prime_2806606135577 : Nat.Prime 2806606135577 := by
  apply nodeValid_prime [2, 79, 4440832493] ⟨2806606135577, 3, [(2, 3), (79, 1), (4440832493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_4440832493
  · decide +kernel

theorem prime_2806606136861 : Nat.Prime 2806606136861 := by
  apply nodeValid_prime [2, 5, 59, 2378479777] ⟨2806606136861, 10, [(2, 2), (5, 1), (59, 1), (2378479777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_2378479777
  · decide +kernel

theorem prime_2806606154789 : Nat.Prime 2806606154789 := by
  apply nodeValid_prime [2, 23, 283, 107797133] ⟨2806606154789, 3, [(2, 2), (23, 1), (283, 1), (107797133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_283
    · exact prime_107797133
  · decide +kernel

theorem prime_2809229074391 : Nat.Prime 2809229074391 := by
  apply nodeValid_prime [2, 5, 19, 47, 1877, 8821] ⟨2809229074391, 11, [(2, 1), (5, 1), (19, 2), (47, 1), (1877, 1), (8821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_47
    · exact prime_1877
    · exact prime_8821
  · decide +kernel

theorem prime_2809229076161 : Nat.Prime 2809229076161 := by
  apply nodeValid_prime [2, 5, 13, 675295451] ⟨2809229076161, 6, [(2, 6), (5, 1), (13, 1), (675295451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_675295451
  · decide +kernel

theorem prime_2809229076259 : Nat.Prime 2809229076259 := by
  apply nodeValid_prime [2, 3, 11, 211, 201725483] ⟨2809229076259, 2, [(2, 1), (3, 1), (11, 1), (211, 1), (201725483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_211
    · exact prime_201725483
  · decide +kernel

theorem prime_2811853614061 : Nat.Prime 2811853614061 := by
  apply nodeValid_prime [2, 3, 5, 15621408967] ⟨2811853614061, 10, [(2, 2), (3, 2), (5, 1), (15621408967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15621408967
  · decide +kernel

theorem prime_2811853618117 : Nat.Prime 2811853618117 := by
  apply nodeValid_prime [2, 3, 131, 1788710953] ⟨2811853618117, 5, [(2, 2), (3, 1), (131, 1), (1788710953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_1788710953
  · decide +kernel

theorem prime_2811853652857 : Nat.Prime 2811853652857 := by
  apply nodeValid_prime [2, 3, 67, 283, 347, 17807] ⟨2811853652857, 10, [(2, 3), (3, 1), (67, 1), (283, 1), (347, 1), (17807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_283
    · exact prime_347
    · exact prime_17807
  · decide +kernel

theorem prime_2814479813263 : Nat.Prime 2814479813263 := by
  apply nodeValid_prime [2, 3, 13, 109, 331037381] ⟨2814479813263, 3, [(2, 1), (3, 1), (13, 1), (109, 1), (331037381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_109
    · exact prime_331037381
  · decide +kernel

theorem prime_2814479813767 : Nat.Prime 2814479813767 := by
  apply nodeValid_prime [2, 3, 19, 89, 6763, 41017] ⟨2814479813767, 19, [(2, 1), (3, 1), (19, 1), (89, 1), (6763, 1), (41017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_89
    · exact prime_6763
    · exact prime_41017
  · decide +kernel

theorem prime_2814479877907 : Nat.Prime 2814479877907 := by
  apply nodeValid_prime [2, 3, 281, 337, 431, 1277] ⟨2814479877907, 5, [(2, 1), (3, 3), (281, 1), (337, 1), (431, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_337
    · exact prime_431
    · exact prime_1277
  · decide +kernel

theorem prime_2817107704711 : Nat.Prime 2817107704711 := by
  apply nodeValid_prime [2, 3, 5, 13, 29, 331, 250837] ⟨2817107704711, 6, [(2, 1), (3, 2), (5, 1), (13, 1), (29, 1), (331, 1), (250837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_29
    · exact prime_331
    · exact prime_250837
  · decide +kernel

theorem prime_2817107705759 : Nat.Prime 2817107705759 := by
  apply nodeValid_prime [2, 1408553852879] ⟨2817107705759, 7, [(2, 1), (1408553852879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1408553852879
  · decide +kernel

theorem prime_2817107763467 : Nat.Prime 2817107763467 := by
  apply nodeValid_prime [2, 337, 4179685109] ⟨2817107763467, 2, [(2, 1), (337, 1), (4179685109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_4179685109
  · decide +kernel

theorem prime_2819737204877 : Nat.Prime 2819737204877 := by
  apply nodeValid_prime [2, 704934301219] ⟨2819737204877, 2, [(2, 2), (704934301219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_704934301219
  · decide +kernel

theorem prime_2819737204927 : Nat.Prime 2819737204927 := by
  apply nodeValid_prime [2, 3, 863, 544561067] ⟨2819737204927, 3, [(2, 1), (3, 1), (863, 1), (544561067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863
    · exact prime_544561067
  · decide +kernel

theorem prime_2819737313977 : Nat.Prime 2819737313977 := by
  apply nodeValid_prime [2, 3, 11, 59, 71, 2549731] ⟨2819737313977, 5, [(2, 3), (3, 1), (11, 1), (59, 1), (71, 1), (2549731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_71
    · exact prime_2549731
  · decide +kernel

theorem prime_2822368524697 : Nat.Prime 2822368524697 := by
  apply nodeValid_prime [2, 3, 7, 1801, 3109349] ⟨2822368524697, 11, [(2, 3), (3, 2), (7, 1), (1801, 1), (3109349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1801
    · exact prime_3109349
  · decide +kernel

theorem prime_2822368569719 : Nat.Prime 2822368569719 := by
  apply nodeValid_prime [2, 37, 41, 21023, 44249] ⟨2822368569719, 17, [(2, 1), (37, 1), (41, 1), (21023, 1), (44249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_41
    · exact prime_21023
    · exact prime_44249
  · decide +kernel

theorem prime_2822368570391 : Nat.Prime 2822368570391 := by
  apply nodeValid_prime [2, 5, 127, 233, 1709, 5581] ⟨2822368570391, 23, [(2, 1), (5, 1), (127, 1), (233, 1), (1709, 1), (5581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_233
    · exact prime_1709
    · exact prime_5581
  · decide +kernel

theorem prime_2825001377641 : Nat.Prime 2825001377641 := by
  apply nodeValid_prime [2, 3, 5, 13, 6793, 88861] ⟨2825001377641, 19, [(2, 3), (3, 2), (5, 1), (13, 1), (6793, 1), (88861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_6793
    · exact prime_88861
  · decide +kernel

theorem prime_2825001377791 : Nat.Prime 2825001377791 := by
  apply nodeValid_prime [2, 3, 5, 94166712593] ⟨2825001377791, 3, [(2, 1), (3, 1), (5, 1), (94166712593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_94166712593
  · decide +kernel

theorem prime_2825001397679 : Nat.Prime 2825001397679 := by
  apply nodeValid_prime [2, 167, 8458088017] ⟨2825001397679, 13, [(2, 1), (167, 1), (8458088017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_8458088017
  · decide +kernel

theorem prime_2827635927059 : Nat.Prime 2827635927059 := by
  apply nodeValid_prime [2, 59, 23963016331] ⟨2827635927059, 2, [(2, 1), (59, 1), (23963016331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_23963016331
  · decide +kernel

theorem prime_2827635972349 : Nat.Prime 2827635972349 := by
  apply nodeValid_prime [2, 3, 11, 6763, 3167453] ⟨2827635972349, 2, [(2, 2), (3, 1), (11, 1), (6763, 1), (3167453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6763
    · exact prime_3167453
  · decide +kernel

theorem prime_2827635972929 : Nat.Prime 2827635972929 := by
  apply nodeValid_prime [2, 13, 67, 50725387] ⟨2827635972929, 3, [(2, 6), (13, 1), (67, 1), (50725387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_50725387
  · decide +kernel

theorem prime_2830272083207 : Nat.Prime 2830272083207 := by
  apply nodeValid_prime [2, 347, 991, 4115239] ⟨2830272083207, 5, [(2, 1), (347, 1), (991, 1), (4115239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_991
    · exact prime_4115239
  · decide +kernel

theorem prime_2830272083699 : Nat.Prime 2830272083699 := by
  apply nodeValid_prime [2, 1415136041849] ⟨2830272083699, 2, [(2, 1), (1415136041849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1415136041849
  · decide +kernel

theorem prime_2830272119033 : Nat.Prime 2830272119033 := by
  apply nodeValid_prime [2, 71, 881, 5655929] ⟨2830272119033, 3, [(2, 3), (71, 1), (881, 1), (5655929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_881
    · exact prime_5655929
  · decide +kernel

theorem prime_2832909944707 : Nat.Prime 2832909944707 := by
  apply nodeValid_prime [2, 3, 53527, 2940271] ⟨2832909944707, 2, [(2, 1), (3, 2), (53527, 1), (2940271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53527
    · exact prime_2940271
  · decide +kernel

theorem prime_2832909945233 : Nat.Prime 2832909945233 := by
  apply nodeValid_prime [2, 139, 199, 6400957] ⟨2832909945233, 3, [(2, 4), (139, 1), (199, 1), (6400957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_199
    · exact prime_6400957
  · decide +kernel

theorem prime_2832909986707 : Nat.Prime 2832909986707 := by
  apply nodeValid_prime [2, 3, 23, 263, 7703, 10133] ⟨2832909986707, 2, [(2, 1), (3, 1), (23, 1), (263, 1), (7703, 1), (10133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_263
    · exact prime_7703
    · exact prime_10133
  · decide +kernel

theorem prime_2835549517069 : Nat.Prime 2835549517069 := by
  apply nodeValid_prime [2, 3, 29347, 894643] ⟨2835549517069, 17, [(2, 2), (3, 3), (29347, 1), (894643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29347
    · exact prime_894643
  · decide +kernel

theorem prime_2835549518731 : Nat.Prime 2835549518731 := by
  apply nodeValid_prime [2, 3, 5, 1039, 90970469] ⟨2835549518731, 10, [(2, 1), (3, 1), (5, 1), (1039, 1), (90970469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1039
    · exact prime_90970469
  · decide +kernel

theorem prime_2835549519857 : Nat.Prime 2835549519857 := by
  apply nodeValid_prime [2, 47, 1471, 2563343] ⟨2835549519857, 3, [(2, 4), (47, 1), (1471, 1), (2563343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1471
    · exact prime_2563343
  · decide +kernel

theorem prime_2838190717139 : Nat.Prime 2838190717139 := by
  apply nodeValid_prime [2, 7, 6827, 29695021] ⟨2838190717139, 7, [(2, 1), (7, 1), (6827, 1), (29695021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6827
    · exact prime_29695021
  · decide +kernel

theorem prime_2838190723253 : Nat.Prime 2838190723253 := by
  apply nodeValid_prime [2, 173, 997, 4113773] ⟨2838190723253, 2, [(2, 2), (173, 1), (997, 1), (4113773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_997
    · exact prime_4113773
  · decide +kernel

theorem prime_2838190723691 : Nat.Prime 2838190723691 := by
  apply nodeValid_prime [2, 5, 7, 73529, 551423] ⟨2838190723691, 2, [(2, 1), (5, 1), (7, 1), (73529, 1), (551423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_73529
    · exact prime_551423
  · decide +kernel

theorem prime_2840833477843 : Nat.Prime 2840833477843 := by
  apply nodeValid_prime [2, 3, 29, 47, 3347, 103787] ⟨2840833477843, 3, [(2, 1), (3, 1), (29, 1), (47, 1), (3347, 1), (103787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_47
    · exact prime_3347
    · exact prime_103787
  · decide +kernel

theorem prime_2840833478183 : Nat.Prime 2840833478183 := by
  apply nodeValid_prime [2, 7, 202916677013] ⟨2840833478183, 5, [(2, 1), (7, 1), (202916677013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_202916677013
  · decide +kernel

theorem prime_2840833575221 : Nat.Prime 2840833575221 := by
  apply nodeValid_prime [2, 5, 142041678761] ⟨2840833575221, 2, [(2, 2), (5, 1), (142041678761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_142041678761
  · decide +kernel

theorem prime_2843478093457 : Nat.Prime 2843478093457 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 2609, 7561] ⟨2843478093457, 5, [(2, 4), (3, 2), (7, 1), (11, 1), (13, 1), (2609, 1), (7561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_2609
    · exact prime_7561
  · decide +kernel

theorem prime_2843478100399 : Nat.Prime 2843478100399 := by
  apply nodeValid_prime [2, 3, 13, 23, 26249, 60383] ⟨2843478100399, 23, [(2, 1), (3, 1), (13, 1), (23, 1), (26249, 1), (60383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_26249
    · exact prime_60383
  · decide +kernel

theorem prime_2843478101371 : Nat.Prime 2843478101371 := by
  apply nodeValid_prime [2, 3, 5, 2647, 35807557] ⟨2843478101371, 3, [(2, 1), (3, 1), (5, 1), (2647, 1), (35807557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2647
    · exact prime_35807557
  · decide +kernel

theorem prime_2846124225883 : Nat.Prime 2846124225883 := by
  apply nodeValid_prime [2, 3, 7, 137, 2035531] ⟨2846124225883, 2, [(2, 1), (3, 6), (7, 1), (137, 1), (2035531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_2035531
  · decide +kernel

theorem prime_2846124226003 : Nat.Prime 2846124226003 := by
  apply nodeValid_prime [2, 3, 97, 55763, 87697] ⟨2846124226003, 2, [(2, 1), (3, 1), (97, 1), (55763, 1), (87697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_55763
    · exact prime_87697
  · decide +kernel

theorem prime_2846124283799 : Nat.Prime 2846124283799 := by
  apply nodeValid_prime [2, 1423062141899] ⟨2846124283799, 11, [(2, 1), (1423062141899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1423062141899
  · decide +kernel

theorem prime_2848772137751 : Nat.Prime 2848772137751 := by
  apply nodeValid_prime [2, 5, 7, 11, 147988163] ⟨2848772137751, 7, [(2, 1), (5, 3), (7, 1), (11, 1), (147988163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_147988163
  · decide +kernel

theorem prime_2848772183107 : Nat.Prime 2848772183107 := by
  apply nodeValid_prime [2, 3, 449, 619, 1708321] ⟨2848772183107, 2, [(2, 1), (3, 1), (449, 1), (619, 1), (1708321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
    · exact prime_619
    · exact prime_1708321
  · decide +kernel

theorem prime_2848772183177 : Nat.Prime 2848772183177 := by
  apply nodeValid_prime [2, 37997, 9371701] ⟨2848772183177, 3, [(2, 3), (37997, 1), (9371701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37997
    · exact prime_9371701
  · decide +kernel

theorem prime_2851421622653 : Nat.Prime 2851421622653 := by
  apply nodeValid_prime [2, 277, 1151, 2235869] ⟨2851421622653, 2, [(2, 2), (277, 1), (1151, 1), (2235869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_1151
    · exact prime_2235869
  · decide +kernel

theorem prime_2851421622869 : Nat.Prime 2851421622869 := by
  apply nodeValid_prime [2, 7, 13, 313, 25027399] ⟨2851421622869, 2, [(2, 2), (7, 1), (13, 1), (313, 1), (25027399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_313
    · exact prime_25027399
  · decide +kernel

theorem prime_2851421658541 : Nat.Prime 2851421658541 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 1373, 380363] ⟨2851421658541, 18, [(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (1373, 1), (380363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_1373
    · exact prime_380363
  · decide +kernel

theorem prime_2854072854539 : Nat.Prime 2854072854539 := by
  apply nodeValid_prime [2, 167, 11617, 735571] ⟨2854072854539, 2, [(2, 1), (167, 1), (11617, 1), (735571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_11617
    · exact prime_735571
  · decide +kernel

theorem prime_2854072855211 : Nat.Prime 2854072855211 := by
  apply nodeValid_prime [2, 5, 59, 523, 9249353] ⟨2854072855211, 2, [(2, 1), (5, 1), (59, 1), (523, 1), (9249353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_523
    · exact prime_9249353
  · decide +kernel

theorem prime_2854072857007 : Nat.Prime 2854072857007 := by
  apply nodeValid_prime [2, 3, 7, 29, 181, 4315369] ⟨2854072857007, 7, [(2, 1), (3, 2), (7, 1), (29, 1), (181, 1), (4315369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_181
    · exact prime_4315369
  · decide +kernel

theorem prime_2856725732863 : Nat.Prime 2856725732863 := by
  apply nodeValid_prime [2, 3, 59, 491, 1301, 4211] ⟨2856725732863, 5, [(2, 1), (3, 2), (59, 1), (491, 1), (1301, 1), (4211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_491
    · exact prime_1301
    · exact prime_4211
  · decide +kernel

theorem prime_2856725733137 : Nat.Prime 2856725733137 := by
  apply nodeValid_prime [2, 11, 1619, 10025569] ⟨2856725733137, 3, [(2, 4), (11, 1), (1619, 1), (10025569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1619
    · exact prime_10025569
  · decide +kernel

theorem prime_2856725733229 : Nat.Prime 2856725733229 := by
  apply nodeValid_prime [2, 3, 73243, 3250283] ⟨2856725733229, 6, [(2, 2), (3, 1), (73243, 1), (3250283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73243
    · exact prime_3250283
  · decide +kernel

end Sude.Lucas.Generated
