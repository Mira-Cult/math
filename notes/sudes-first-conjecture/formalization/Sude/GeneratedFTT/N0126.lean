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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0123

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5039 : Nat.Prime 5039 := by
  apply nodeValid_prime [2, 11, 229] ⟨5039, 11, [(2, 1), (11, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_229
  · decide +kernel

theorem prime_6007 : Nat.Prime 6007 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨6007, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_10837 : Nat.Prime 10837 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨10837, 2, [(2, 2), (3, 2), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_12073 : Nat.Prime 12073 := by
  apply nodeValid_prime [2, 3, 503] ⟨12073, 7, [(2, 3), (3, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
  · decide +kernel

theorem prime_19463 : Nat.Prime 19463 := by
  apply nodeValid_prime [2, 37, 263] ⟨19463, 5, [(2, 1), (37, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_263
  · decide +kernel

theorem prime_20113 : Nat.Prime 20113 := by
  apply nodeValid_prime [2, 3, 419] ⟨20113, 10, [(2, 4), (3, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419
  · decide +kernel

theorem prime_24943 : Nat.Prime 24943 := by
  apply nodeValid_prime [2, 3, 4157] ⟨24943, 5, [(2, 1), (3, 1), (4157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4157
  · decide +kernel

theorem prime_26987 : Nat.Prime 26987 := by
  apply nodeValid_prime [2, 103, 131] ⟨26987, 2, [(2, 1), (103, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_131
  · decide +kernel

theorem prime_29231 : Nat.Prime 29231 := by
  apply nodeValid_prime [2, 5, 37, 79] ⟨29231, 13, [(2, 1), (5, 1), (37, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_79
  · decide +kernel

theorem prime_30389 : Nat.Prime 30389 := by
  apply nodeValid_prime [2, 71, 107] ⟨30389, 2, [(2, 2), (71, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_107
  · decide +kernel

theorem prime_32957 : Nat.Prime 32957 := by
  apply nodeValid_prime [2, 7, 11, 107] ⟨32957, 12, [(2, 2), (7, 1), (11, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_107
  · decide +kernel

theorem prime_33739 : Nat.Prime 33739 := by
  apply nodeValid_prime [2, 3, 5623] ⟨33739, 2, [(2, 1), (3, 1), (5623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5623
  · decide +kernel

theorem prime_36007 : Nat.Prime 36007 := by
  apply nodeValid_prime [2, 3, 17, 353] ⟨36007, 3, [(2, 1), (3, 1), (17, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_353
  · decide +kernel

theorem prime_39709 : Nat.Prime 39709 := by
  apply nodeValid_prime [2, 3, 1103] ⟨39709, 6, [(2, 2), (3, 2), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1103
  · decide +kernel

theorem prime_40099 : Nat.Prime 40099 := by
  apply nodeValid_prime [2, 3, 41, 163] ⟨40099, 3, [(2, 1), (3, 1), (41, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_163
  · decide +kernel

theorem prime_42187 : Nat.Prime 42187 := by
  apply nodeValid_prime [2, 3, 79, 89] ⟨42187, 13, [(2, 1), (3, 1), (79, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_89
  · decide +kernel

theorem prime_42853 : Nat.Prime 42853 := by
  apply nodeValid_prime [2, 3, 3571] ⟨42853, 2, [(2, 2), (3, 1), (3571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3571
  · decide +kernel

theorem prime_43541 : Nat.Prime 43541 := by
  apply nodeValid_prime [2, 5, 7, 311] ⟨43541, 2, [(2, 2), (5, 1), (7, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_311
  · decide +kernel

theorem prime_46817 : Nat.Prime 46817 := by
  apply nodeValid_prime [2, 7, 11, 19] ⟨46817, 3, [(2, 5), (7, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_47917 : Nat.Prime 47917 := by
  apply nodeValid_prime [2, 3, 11] ⟨47917, 5, [(2, 2), (3, 2), (11, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_72997 : Nat.Prime 72997 := by
  apply nodeValid_prime [2, 3, 7, 11, 79] ⟨72997, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_73783 : Nat.Prime 73783 := by
  apply nodeValid_prime [2, 3, 4099] ⟨73783, 3, [(2, 1), (3, 2), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4099
  · decide +kernel

theorem prime_75797 : Nat.Prime 75797 := by
  apply nodeValid_prime [2, 7, 2707] ⟨75797, 2, [(2, 2), (7, 1), (2707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2707
  · decide +kernel

theorem prime_84653 : Nat.Prime 84653 := by
  apply nodeValid_prime [2, 21163] ⟨84653, 2, [(2, 2), (21163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21163
  · decide +kernel

theorem prime_87083 : Nat.Prime 87083 := by
  apply nodeValid_prime [2, 43541] ⟨87083, 2, [(2, 1), (43541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43541
  · decide +kernel

theorem prime_87701 : Nat.Prime 87701 := by
  apply nodeValid_prime [2, 5, 877] ⟨87701, 2, [(2, 2), (5, 2), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_877
  · decide +kernel

theorem prime_97367 : Nat.Prime 97367 := by
  apply nodeValid_prime [2, 89, 547] ⟨97367, 5, [(2, 1), (89, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_547
  · decide +kernel

theorem prime_104677 : Nat.Prime 104677 := by
  apply nodeValid_prime [2, 3, 11, 13, 61] ⟨104677, 2, [(2, 2), (3, 1), (11, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_106693 : Nat.Prime 106693 := by
  apply nodeValid_prime [2, 3, 17, 523] ⟨106693, 2, [(2, 2), (3, 1), (17, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_523
  · decide +kernel

theorem prime_108287 : Nat.Prime 108287 := by
  apply nodeValid_prime [2, 29, 1867] ⟨108287, 5, [(2, 1), (29, 1), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1867
  · decide +kernel

theorem prime_114641 : Nat.Prime 114641 := by
  apply nodeValid_prime [2, 5, 1433] ⟨114641, 3, [(2, 4), (5, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1433
  · decide +kernel

theorem prime_123551 : Nat.Prime 123551 := by
  apply nodeValid_prime [2, 5, 7, 353] ⟨123551, 7, [(2, 1), (5, 2), (7, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_353
  · decide +kernel

theorem prime_127399 : Nat.Prime 127399 := by
  apply nodeValid_prime [2, 3, 17, 1249] ⟨127399, 3, [(2, 1), (3, 1), (17, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1249
  · decide +kernel

theorem prime_132707 : Nat.Prime 132707 := by
  apply nodeValid_prime [2, 7, 9479] ⟨132707, 2, [(2, 1), (7, 1), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9479
  · decide +kernel

theorem prime_147151 : Nat.Prime 147151 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨147151, 3, [(2, 1), (3, 3), (5, 2), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_147827 : Nat.Prime 147827 := by
  apply nodeValid_prime [2, 7, 10559] ⟨147827, 2, [(2, 1), (7, 1), (10559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10559
  · decide +kernel

theorem prime_151507 : Nat.Prime 151507 := by
  apply nodeValid_prime [2, 3, 19, 443] ⟨151507, 2, [(2, 1), (3, 2), (19, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_443
  · decide +kernel

theorem prime_169307 : Nat.Prime 169307 := by
  apply nodeValid_prime [2, 84653] ⟨169307, 2, [(2, 1), (84653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84653
  · decide +kernel

theorem prime_191353 : Nat.Prime 191353 := by
  apply nodeValid_prime [2, 3, 7, 17, 67] ⟨191353, 5, [(2, 3), (3, 1), (7, 1), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_205129 : Nat.Prime 205129 := by
  apply nodeValid_prime [2, 3, 7, 11, 37] ⟨205129, 13, [(2, 3), (3, 2), (7, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_224629 : Nat.Prime 224629 := by
  apply nodeValid_prime [2, 3, 18719] ⟨224629, 23, [(2, 2), (3, 1), (18719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18719
  · decide +kernel

theorem prime_265607 : Nat.Prime 265607 := by
  apply nodeValid_prime [2, 11, 12073] ⟨265607, 5, [(2, 1), (11, 1), (12073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12073
  · decide +kernel

theorem prime_299951 : Nat.Prime 299951 := by
  apply nodeValid_prime [2, 5, 7, 857] ⟨299951, 7, [(2, 1), (5, 2), (7, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_857
  · decide +kernel

theorem prime_345271 : Nat.Prime 345271 := by
  apply nodeValid_prime [2, 3, 5, 17, 677] ⟨345271, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_677
  · decide +kernel

theorem prime_350947 : Nat.Prime 350947 := by
  apply nodeValid_prime [2, 3, 67, 97] ⟨350947, 2, [(2, 1), (3, 3), (67, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_97
  · decide +kernel

theorem prime_398969 : Nat.Prime 398969 := by
  apply nodeValid_prime [2, 49871] ⟨398969, 3, [(2, 3), (49871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49871
  · decide +kernel

theorem prime_470161 : Nat.Prime 470161 := by
  apply nodeValid_prime [2, 3, 5, 653] ⟨470161, 7, [(2, 4), (3, 2), (5, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_653
  · decide +kernel

theorem prime_489449 : Nat.Prime 489449 := by
  apply nodeValid_prime [2, 193, 317] ⟨489449, 3, [(2, 3), (193, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_317
  · decide +kernel

theorem prime_606029 : Nat.Prime 606029 := by
  apply nodeValid_prime [2, 151507] ⟨606029, 2, [(2, 2), (151507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_151507
  · decide +kernel

theorem prime_643567 : Nat.Prime 643567 := by
  apply nodeValid_prime [2, 3, 7, 11, 199] ⟨643567, 3, [(2, 1), (3, 1), (7, 2), (11, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_199
  · decide +kernel

theorem prime_655439 : Nat.Prime 655439 := by
  apply nodeValid_prime [2, 7, 46817] ⟨655439, 7, [(2, 1), (7, 1), (46817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_46817
  · decide +kernel

theorem prime_792241 : Nat.Prime 792241 := by
  apply nodeValid_prime [2, 3, 5, 3301] ⟨792241, 13, [(2, 4), (3, 1), (5, 1), (3301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3301
  · decide +kernel

theorem prime_1363139 : Nat.Prime 1363139 := by
  apply nodeValid_prime [2, 7, 97367] ⟨1363139, 2, [(2, 1), (7, 1), (97367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_97367
  · decide +kernel

theorem prime_1511801 : Nat.Prime 1511801 := by
  apply nodeValid_prime [2, 5, 7559] ⟨1511801, 3, [(2, 3), (5, 2), (7559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7559
  · decide +kernel

theorem prime_1732921 : Nat.Prime 1732921 := by
  apply nodeValid_prime [2, 3, 5, 7, 2063] ⟨1732921, 29, [(2, 3), (3, 1), (5, 1), (7, 1), (2063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2063
  · decide +kernel

theorem prime_1812449 : Nat.Prime 1812449 := by
  apply nodeValid_prime [2, 11, 19, 271] ⟨1812449, 3, [(2, 5), (11, 1), (19, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_271
  · decide +kernel

theorem prime_2293883 : Nat.Prime 2293883 := by
  apply nodeValid_prime [2, 23, 47, 1061] ⟨2293883, 2, [(2, 1), (23, 1), (47, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_1061
  · decide +kernel

theorem prime_2512249 : Nat.Prime 2512249 := by
  apply nodeValid_prime [2, 3, 104677] ⟨2512249, 19, [(2, 3), (3, 1), (104677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_104677
  · decide +kernel

theorem prime_2513677 : Nat.Prime 2513677 := by
  apply nodeValid_prime [2, 3, 11, 137, 139] ⟨2513677, 2, [(2, 2), (3, 1), (11, 1), (137, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
    · exact prime_139
  · decide +kernel

theorem prime_2656189 : Nat.Prime 2656189 := by
  apply nodeValid_prime [2, 3, 73783] ⟨2656189, 2, [(2, 2), (3, 2), (73783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73783
  · decide +kernel

theorem prime_2830967 : Nat.Prime 2830967 := by
  apply nodeValid_prime [2, 293, 4831] ⟨2830967, 5, [(2, 1), (293, 1), (4831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_4831
  · decide +kernel

theorem prime_3226021 : Nat.Prime 3226021 := by
  apply nodeValid_prime [2, 3, 5, 7, 7681] ⟨3226021, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (7681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_7681
  · decide +kernel

theorem prime_4218917 : Nat.Prime 4218917 := by
  apply nodeValid_prime [2, 13, 79] ⟨4218917, 2, [(2, 2), (13, 2), (79, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_4313999 : Nat.Prime 4313999 := by
  apply nodeValid_prime [2, 13, 277, 599] ⟨4313999, 7, [(2, 1), (13, 1), (277, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_277
    · exact prime_599
  · decide +kernel

theorem prime_4974479 : Nat.Prime 4974479 := by
  apply nodeValid_prime [2, 227, 10957] ⟨4974479, 11, [(2, 1), (227, 1), (10957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_10957
  · decide +kernel

theorem prime_5615153 : Nat.Prime 5615153 := by
  apply nodeValid_prime [2, 350947] ⟨5615153, 3, [(2, 4), (350947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_350947
  · decide +kernel

theorem prime_12405269 : Nat.Prime 12405269 := by
  apply nodeValid_prime [2, 193, 16069] ⟨12405269, 2, [(2, 2), (193, 1), (16069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_16069
  · decide +kernel

theorem prime_13260193 : Nat.Prime 13260193 := by
  apply nodeValid_prime [2, 3, 11, 29, 433] ⟨13260193, 5, [(2, 5), (3, 1), (11, 1), (29, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_433
  · decide +kernel

theorem prime_13610743 : Nat.Prime 13610743 := by
  apply nodeValid_prime [2, 3, 401, 5657] ⟨13610743, 3, [(2, 1), (3, 1), (401, 1), (5657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_5657
  · decide +kernel

theorem prime_13718753 : Nat.Prime 13718753 := by
  apply nodeValid_prime [2, 577, 743] ⟨13718753, 3, [(2, 5), (577, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_743
  · decide +kernel

theorem prime_16449031 : Nat.Prime 16449031 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 827] ⟨16449031, 3, [(2, 1), (3, 2), (5, 1), (13, 1), (17, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_827
  · decide +kernel

theorem prime_17967491 : Nat.Prime 17967491 := by
  apply nodeValid_prime [2, 5, 73, 151, 163] ⟨17967491, 2, [(2, 1), (5, 1), (73, 1), (151, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_151
    · exact prime_163
  · decide +kernel

theorem prime_20974049 : Nat.Prime 20974049 := by
  apply nodeValid_prime [2, 655439] ⟨20974049, 3, [(2, 5), (655439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_655439
  · decide +kernel

theorem prime_22980487 : Nat.Prime 22980487 := by
  apply nodeValid_prime [2, 3, 31, 123551] ⟨22980487, 3, [(2, 1), (3, 1), (31, 1), (123551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_123551
  · decide +kernel

theorem prime_25184759 : Nat.Prime 25184759 := by
  apply nodeValid_prime [2, 1301, 9679] ⟨25184759, 13, [(2, 1), (1301, 1), (9679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1301
    · exact prime_9679
  · decide +kernel

theorem prime_25313503 : Nat.Prime 25313503 := by
  apply nodeValid_prime [2, 3, 4218917] ⟨25313503, 3, [(2, 1), (3, 1), (4218917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4218917
  · decide +kernel

theorem prime_27869419 : Nat.Prime 27869419 := by
  apply nodeValid_prime [2, 3, 43, 36007] ⟨27869419, 2, [(2, 1), (3, 2), (43, 1), (36007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_36007
  · decide +kernel

theorem prime_33146017 : Nat.Prime 33146017 := by
  apply nodeValid_prime [2, 3, 345271] ⟨33146017, 5, [(2, 5), (3, 1), (345271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_345271
  · decide +kernel

theorem prime_36648347 : Nat.Prime 36648347 := by
  apply nodeValid_prime [2, 7, 97, 26987] ⟨36648347, 5, [(2, 1), (7, 1), (97, 1), (26987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_97
    · exact prime_26987
  · decide +kernel

theorem prime_54542611 : Nat.Prime 54542611 := by
  apply nodeValid_prime [2, 3, 5, 606029] ⟨54542611, 3, [(2, 1), (3, 2), (5, 1), (606029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_606029
  · decide +kernel

theorem prime_84660857 : Nat.Prime 84660857 := by
  apply nodeValid_prime [2, 7, 1511801] ⟨84660857, 3, [(2, 3), (7, 1), (1511801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1511801
  · decide +kernel

theorem prime_91648633 : Nat.Prime 91648633 := by
  apply nodeValid_prime [2, 3, 17, 224629] ⟨91648633, 5, [(2, 3), (3, 1), (17, 1), (224629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_224629
  · decide +kernel

theorem prime_92078671 : Nat.Prime 92078671 := by
  apply nodeValid_prime [2, 3, 5, 101, 30389] ⟨92078671, 3, [(2, 1), (3, 1), (5, 1), (101, 1), (30389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_30389
  · decide +kernel

theorem prime_93484439 : Nat.Prime 93484439 := by
  apply nodeValid_prime [2, 59, 792241] ⟨93484439, 11, [(2, 1), (59, 1), (792241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_792241
  · decide +kernel

theorem prime_122948929 : Nat.Prime 122948929 := by
  apply nodeValid_prime [2, 3, 37, 641] ⟨122948929, 21, [(2, 6), (3, 4), (37, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_641
  · decide +kernel

theorem prime_142363171 : Nat.Prime 142363171 := by
  apply nodeValid_prime [2, 3, 5, 175757] ⟨142363171, 3, [(2, 1), (3, 4), (5, 1), (175757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_175757
  · decide +kernel

theorem prime_186968879 : Nat.Prime 186968879 := by
  apply nodeValid_prime [2, 93484439] ⟨186968879, 11, [(2, 1), (93484439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93484439
  · decide +kernel

theorem prime_206770033 : Nat.Prime 206770033 := by
  apply nodeValid_prime [2, 3, 7, 205129] ⟨206770033, 5, [(2, 4), (3, 2), (7, 1), (205129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_205129
  · decide +kernel

theorem prime_225279731 : Nat.Prime 225279731 := by
  apply nodeValid_prime [2, 5, 13, 1732921] ⟨225279731, 2, [(2, 1), (5, 1), (13, 1), (1732921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1732921
  · decide +kernel

theorem prime_290956157 : Nat.Prime 290956157 := by
  apply nodeValid_prime [2, 17, 97, 44111] ⟨290956157, 2, [(2, 2), (17, 1), (97, 1), (44111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97
    · exact prime_44111
  · decide +kernel

theorem prime_343015913 : Nat.Prime 343015913 := by
  apply nodeValid_prime [2, 2203, 19463] ⟨343015913, 3, [(2, 3), (2203, 1), (19463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2203
    · exact prime_19463
  · decide +kernel

theorem prime_549891799 : Nat.Prime 549891799 := by
  apply nodeValid_prime [2, 3, 91648633] ⟨549891799, 3, [(2, 1), (3, 1), (91648633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_91648633
  · decide +kernel

theorem prime_571651207 : Nat.Prime 571651207 := by
  apply nodeValid_prime [2, 3, 7, 13610743] ⟨571651207, 3, [(2, 1), (3, 1), (7, 1), (13610743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13610743
  · decide +kernel

theorem prime_995757029 : Nat.Prime 995757029 := by
  apply nodeValid_prime [2, 7, 349, 14557] ⟨995757029, 2, [(2, 2), (7, 2), (349, 1), (14557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_349
    · exact prime_14557
  · decide +kernel

theorem prime_1151432171 : Nat.Prime 1151432171 := by
  apply nodeValid_prime [2, 5, 7, 16449031] ⟨1151432171, 2, [(2, 1), (5, 1), (7, 1), (16449031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_16449031
  · decide +kernel

theorem prime_2217489121 : Nat.Prime 2217489121 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 2857] ⟨2217489121, 19, [(2, 5), (3, 2), (5, 1), (7, 2), (11, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_2857
  · decide +kernel

theorem prime_2286604829 : Nat.Prime 2286604829 := by
  apply nodeValid_prime [2, 571651207] ⟨2286604829, 2, [(2, 2), (571651207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_571651207
  · decide +kernel

theorem prime_3145976219 : Nat.Prime 3145976219 := by
  apply nodeValid_prime [2, 7, 11, 709, 28813] ⟨3145976219, 2, [(2, 1), (7, 1), (11, 1), (709, 1), (28813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_709
    · exact prime_28813
  · decide +kernel

theorem prime_5044121707 : Nat.Prime 5044121707 := by
  apply nodeValid_prime [2, 3, 13, 4974479] ⟨5044121707, 7, [(2, 1), (3, 1), (13, 2), (4974479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4974479
  · decide +kernel

theorem prime_6019558361 : Nat.Prime 6019558361 := by
  apply nodeValid_prime [2, 5, 3541, 42499] ⟨6019558361, 3, [(2, 3), (5, 1), (3541, 1), (42499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3541
    · exact prime_42499
  · decide +kernel

theorem prime_7300882363 : Nat.Prime 7300882363 := by
  apply nodeValid_prime [2, 3, 6359, 191353] ⟨7300882363, 2, [(2, 1), (3, 1), (6359, 1), (191353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6359
    · exact prime_191353
  · decide +kernel

theorem prime_8445455003 : Nat.Prime 8445455003 := by
  apply nodeValid_prime [2, 61, 107, 593, 1091] ⟨8445455003, 2, [(2, 1), (61, 1), (107, 1), (593, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_107
    · exact prime_593
    · exact prime_1091
  · decide +kernel

theorem prime_10312811153 : Nat.Prime 10312811153 := by
  apply nodeValid_prime [2, 7, 92078671] ⟨10312811153, 6, [(2, 4), (7, 1), (92078671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_92078671
  · decide +kernel

theorem prime_11821736791 : Nat.Prime 11821736791 := by
  apply nodeValid_prime [2, 3, 5, 10391, 12641] ⟨11821736791, 7, [(2, 1), (3, 2), (5, 1), (10391, 1), (12641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10391
    · exact prime_12641
  · decide +kernel

theorem prime_14259033143 : Nat.Prime 14259033143 := by
  apply nodeValid_prime [2, 29, 113, 863, 2521] ⟨14259033143, 5, [(2, 1), (29, 1), (113, 1), (863, 1), (2521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_113
    · exact prime_863
    · exact prime_2521
  · decide +kernel

theorem prime_26481061549 : Nat.Prime 26481061549 := by
  apply nodeValid_prime [2, 3, 131, 5615153] ⟨26481061549, 2, [(2, 2), (3, 2), (131, 1), (5615153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_5615153
  · decide +kernel

theorem prime_28446053957 : Nat.Prime 28446053957 := by
  apply nodeValid_prime [2, 73, 659, 147827] ⟨28446053957, 2, [(2, 2), (73, 1), (659, 1), (147827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_659
    · exact prime_147827
  · decide +kernel

theorem prime_29696843831 : Nat.Prime 29696843831 := by
  apply nodeValid_prime [2, 5, 1049, 2830967] ⟨29696843831, 7, [(2, 1), (5, 1), (1049, 1), (2830967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1049
    · exact prime_2830967
  · decide +kernel

theorem prime_30871432171 : Nat.Prime 30871432171 := by
  apply nodeValid_prime [2, 3, 5, 343015913] ⟨30871432171, 2, [(2, 1), (3, 2), (5, 1), (343015913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_343015913
  · decide +kernel

theorem prime_31864224929 : Nat.Prime 31864224929 := by
  apply nodeValid_prime [2, 995757029] ⟨31864224929, 3, [(2, 5), (995757029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_995757029
  · decide +kernel

theorem prime_32509775951 : Nat.Prime 32509775951 := by
  apply nodeValid_prime [2, 5, 31, 20974049] ⟨32509775951, 7, [(2, 1), (5, 2), (31, 1), (20974049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_20974049
  · decide +kernel

theorem prime_38272089839 : Nat.Prime 38272089839 := by
  apply nodeValid_prime [2, 23, 28463, 29231] ⟨38272089839, 7, [(2, 1), (23, 1), (28463, 1), (29231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_28463
    · exact prime_29231
  · decide +kernel

theorem prime_49280955953 : Nat.Prime 49280955953 := by
  apply nodeValid_prime [2, 67, 401, 114641] ⟨49280955953, 3, [(2, 4), (67, 1), (401, 1), (114641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_401
    · exact prime_114641
  · decide +kernel

theorem prime_60355378133 : Nat.Prime 60355378133 := by
  apply nodeValid_prime [2, 7, 37, 3191, 18257] ⟨60355378133, 2, [(2, 2), (7, 1), (37, 1), (3191, 1), (18257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_3191
    · exact prime_18257
  · decide +kernel

theorem prime_71081732597 : Nat.Prime 71081732597 := by
  apply nodeValid_prime [2, 7, 17, 31, 37, 2657] ⟨71081732597, 2, [(2, 2), (7, 3), (17, 1), (31, 1), (37, 1), (2657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_37
    · exact prime_2657
  · decide +kernel

theorem prime_91715058433 : Nat.Prime 91715058433 := by
  apply nodeValid_prime [2, 3, 31, 83, 191] ⟨91715058433, 5, [(2, 8), (3, 6), (31, 1), (83, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_83
    · exact prime_191
  · decide +kernel

theorem prime_213405149147 : Nat.Prime 213405149147 := by
  apply nodeValid_prime [2, 7, 71, 1459, 147151] ⟨213405149147, 2, [(2, 1), (7, 1), (71, 1), (1459, 1), (147151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_1459
    · exact prime_147151
  · decide +kernel

theorem prime_229805115583 : Nat.Prime 229805115583 := by
  apply nodeValid_prime [2, 3, 7, 1597, 489449] ⟨229805115583, 10, [(2, 1), (3, 1), (7, 2), (1597, 1), (489449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1597
    · exact prime_489449
  · decide +kernel

theorem prime_276803196743 : Nat.Prime 276803196743 := by
  apply nodeValid_prime [2, 83, 89, 3119, 6007] ⟨276803196743, 5, [(2, 1), (83, 1), (89, 1), (3119, 1), (6007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_89
    · exact prime_3119
    · exact prime_6007
  · decide +kernel

theorem prime_917150584331 : Nat.Prime 917150584331 := by
  apply nodeValid_prime [2, 5, 91715058433] ⟨917150584331, 2, [(2, 1), (5, 1), (91715058433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_91715058433
  · decide +kernel

theorem prime_926142965131 : Nat.Prime 926142965131 := by
  apply nodeValid_prime [2, 3, 5, 30871432171] ⟨926142965131, 12, [(2, 1), (3, 1), (5, 1), (30871432171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_30871432171
  · decide +kernel

theorem prime_1365410589937 : Nat.Prime 1365410589937 := by
  apply nodeValid_prime [2, 3, 28446053957] ⟨1365410589937, 5, [(2, 4), (3, 1), (28446053957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28446053957
  · decide +kernel

theorem prime_2757661415543 : Nat.Prime 2757661415543 := by
  apply nodeValid_prime [2, 11, 9137, 13718753] ⟨2757661415543, 5, [(2, 1), (11, 1), (9137, 1), (13718753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9137
    · exact prime_13718753
  · decide +kernel

theorem prime_2759733533369 : Nat.Prime 2759733533369 := by
  apply nodeValid_prime [2, 7, 49280955953] ⟨2759733533369, 6, [(2, 3), (7, 1), (49280955953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_49280955953
  · decide +kernel

theorem prime_2774266938851 : Nat.Prime 2774266938851 := by
  apply nodeValid_prime [2, 5, 11, 5044121707] ⟨2774266938851, 2, [(2, 1), (5, 2), (11, 1), (5044121707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_5044121707
  · decide +kernel

theorem prime_2778428895299 : Nat.Prime 2778428895299 := by
  apply nodeValid_prime [2, 7, 31, 72997, 87701] ⟨2778428895299, 2, [(2, 1), (7, 1), (31, 1), (72997, 1), (87701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_72997
    · exact prime_87701
  · decide +kernel

theorem prime_5461642359749 : Nat.Prime 5461642359749 := by
  apply nodeValid_prime [2, 1365410589937] ⟨5461642359749, 2, [(2, 2), (1365410589937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1365410589937
  · decide +kernel

theorem prime_5461642359769 : Nat.Prime 5461642359769 := by
  apply nodeValid_prime [2, 3, 7, 32509775951] ⟨5461642359769, 13, [(2, 3), (3, 1), (7, 1), (32509775951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_32509775951
  · decide +kernel

theorem prime_5461642397443 : Nat.Prime 5461642397443 := by
  apply nodeValid_prime [2, 3, 7, 11, 11821736791] ⟨5461642397443, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (11821736791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_11821736791
  · decide +kernel

theorem prime_5465758991369 : Nat.Prime 5465758991369 := by
  apply nodeValid_prime [2, 13, 233, 9043, 24943] ⟨5465758991369, 3, [(2, 3), (13, 1), (233, 1), (9043, 1), (24943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_233
    · exact prime_9043
    · exact prime_24943
  · decide +kernel

theorem prime_5465758991789 : Nat.Prime 5465758991789 := by
  apply nodeValid_prime [2, 227, 6019558361] ⟨5465758991789, 2, [(2, 2), (227, 1), (6019558361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_6019558361
  · decide +kernel

theorem prime_5465759052323 : Nat.Prime 5465759052323 := by
  apply nodeValid_prime [2, 13217, 206770033] ⟨5465759052323, 2, [(2, 1), (13217, 1), (206770033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13217
    · exact prime_206770033
  · decide +kernel

theorem prime_5469877756163 : Nat.Prime 5469877756163 := by
  apply nodeValid_prime [2, 19211, 142363171] ⟨5469877756163, 2, [(2, 1), (19211, 1), (142363171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19211
    · exact prime_142363171
  · decide +kernel

theorem prime_5469877757009 : Nat.Prime 5469877757009 := by
  apply nodeValid_prime [2, 7, 167, 733, 398969] ⟨5469877757009, 3, [(2, 4), (7, 1), (167, 1), (733, 1), (398969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_167
    · exact prime_733
    · exact prime_398969
  · decide +kernel

theorem prime_5469877807211 : Nat.Prime 5469877807211 := by
  apply nodeValid_prime [2, 5, 37, 587, 25184759] ⟨5469877807211, 2, [(2, 1), (5, 1), (37, 1), (587, 1), (25184759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_587
    · exact prime_25184759
  · decide +kernel

theorem prime_5473998620017 : Nat.Prime 5473998620017 := by
  apply nodeValid_prime [2, 3, 29, 317, 12405269] ⟨5473998620017, 5, [(2, 4), (3, 1), (29, 1), (317, 1), (12405269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_317
    · exact prime_12405269
  · decide +kernel

theorem prime_5473998621061 : Nat.Prime 5473998621061 := by
  apply nodeValid_prime [2, 3, 5, 29, 3145976219] ⟨5473998621061, 7, [(2, 2), (3, 1), (5, 1), (29, 1), (3145976219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_3145976219
  · decide +kernel

theorem prime_5473998661493 : Nat.Prime 5473998661493 := by
  apply nodeValid_prime [2, 23, 197, 11617, 25999] ⟨5473998661493, 3, [(2, 2), (23, 1), (197, 1), (11617, 1), (25999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_197
    · exact prime_11617
    · exact prime_25999
  · decide +kernel

theorem prime_5478121612867 : Nat.Prime 5478121612867 := by
  apply nodeValid_prime [2, 3, 7, 3559, 36648347] ⟨5478121612867, 7, [(2, 1), (3, 1), (7, 1), (3559, 1), (36648347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3559
    · exact prime_36648347
  · decide +kernel

theorem prime_5478121641703 : Nat.Prime 5478121641703 := by
  apply nodeValid_prime [2, 3, 43, 8447, 2513677] ⟨5478121641703, 3, [(2, 1), (3, 1), (43, 1), (8447, 1), (2513677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_8447
    · exact prime_2513677
  · decide +kernel

theorem prime_5482246598723 : Nat.Prime 5482246598723 := by
  apply nodeValid_prime [2, 108287, 25313503] ⟨5482246598723, 2, [(2, 1), (108287, 1), (25313503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_108287
    · exact prime_25313503
  · decide +kernel

theorem prime_5482246598929 : Nat.Prime 5482246598929 := by
  apply nodeValid_prime [2, 3, 11, 1303, 2656189] ⟨5482246598929, 17, [(2, 4), (3, 2), (11, 1), (1303, 1), (2656189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1303
    · exact prime_2656189
  · decide +kernel

theorem prime_5482246667957 : Nat.Prime 5482246667957 := by
  apply nodeValid_prime [2, 61, 132707, 169307] ⟨5482246667957, 3, [(2, 2), (61, 1), (132707, 1), (169307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_132707
    · exact prime_169307
  · decide +kernel

theorem prime_5486373745451 : Nat.Prime 5486373745451 := by
  apply nodeValid_prime [2, 5, 13, 4657, 1812449] ⟨5486373745451, 2, [(2, 1), (5, 2), (13, 1), (4657, 1), (1812449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4657
    · exact prime_1812449
  · decide +kernel

theorem prime_5486373745901 : Nat.Prime 5486373745901 := by
  apply nodeValid_prime [2, 5, 317, 577, 299951] ⟨5486373745901, 2, [(2, 2), (5, 2), (317, 1), (577, 1), (299951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_317
    · exact prime_577
    · exact prime_299951
  · decide +kernel

theorem prime_5486373824341 : Nat.Prime 5486373824341 := by
  apply nodeValid_prime [2, 3, 5, 17, 193, 27869419] ⟨5486373824341, 14, [(2, 2), (3, 1), (5, 1), (17, 1), (193, 1), (27869419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_193
    · exact prime_27869419
  · decide +kernel

theorem prime_5490503063483 : Nat.Prime 5490503063483 := by
  apply nodeValid_prime [2, 719, 2801, 1363139] ⟨5490503063483, 2, [(2, 1), (719, 1), (2801, 1), (1363139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_719
    · exact prime_2801
    · exact prime_1363139
  · decide +kernel

theorem prime_5490503063597 : Nat.Prime 5490503063597 := by
  apply nodeValid_prime [2, 619, 2217489121] ⟨5490503063597, 2, [(2, 2), (619, 1), (2217489121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_2217489121
  · decide +kernel

theorem prime_5490503080067 : Nat.Prime 5490503080067 := by
  apply nodeValid_prime [2, 137, 293, 641, 106693] ⟨5490503080067, 2, [(2, 1), (137, 1), (293, 1), (641, 1), (106693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_293
    · exact prime_641
    · exact prime_106693
  · decide +kernel

theorem prime_5494634319989 : Nat.Prime 5494634319989 := by
  apply nodeValid_prime [2, 11, 265607, 470161] ⟨5494634319989, 2, [(2, 2), (11, 1), (265607, 1), (470161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_265607
    · exact prime_470161
  · decide +kernel

theorem prime_5494634320013 : Nat.Prime 5494634320013 := by
  apply nodeValid_prime [2, 1193, 1151432171] ⟨5494634320013, 2, [(2, 2), (1193, 1), (1151432171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1193
    · exact prime_1151432171
  · decide +kernel

theorem prime_5494634441701 : Nat.Prime 5494634441701 := by
  apply nodeValid_prime [2, 3, 5, 797, 22980487] ⟨5494634441701, 7, [(2, 2), (3, 1), (5, 2), (797, 1), (22980487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_797
    · exact prime_22980487
  · decide +kernel

theorem prime_5498767870153 : Nat.Prime 5498767870153 := by
  apply nodeValid_prime [2, 3, 99881, 2293883] ⟨5498767870153, 5, [(2, 3), (3, 1), (99881, 1), (2293883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_99881
    · exact prime_2293883
  · decide +kernel

theorem prime_5498767870577 : Nat.Prime 5498767870577 := by
  apply nodeValid_prime [2, 6301, 54542611] ⟨5498767870577, 3, [(2, 4), (6301, 1), (54542611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6301
    · exact prime_54542611
  · decide +kernel

theorem prime_5498767900597 : Nat.Prime 5498767900597 := by
  apply nodeValid_prime [2, 3, 3727, 122948929] ⟨5498767900597, 5, [(2, 2), (3, 1), (3727, 1), (122948929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3727
    · exact prime_122948929
  · decide +kernel

theorem prime_5502903468571 : Nat.Prime 5502903468571 := by
  apply nodeValid_prime [2, 3, 5, 41, 83, 17967491] ⟨5502903468571, 2, [(2, 1), (3, 2), (5, 1), (41, 1), (83, 1), (17967491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_83
    · exact prime_17967491
  · decide +kernel

theorem prime_5502903505987 : Nat.Prime 5502903505987 := by
  apply nodeValid_prime [2, 3, 917150584331] ⟨5502903505987, 2, [(2, 1), (3, 1), (917150584331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_917150584331
  · decide +kernel

theorem prime_5502903506329 : Nat.Prime 5502903506329 := by
  apply nodeValid_prime [2, 3, 2341, 2903, 33739] ⟨5502903506329, 13, [(2, 3), (3, 1), (2341, 1), (2903, 1), (33739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2341
    · exact prime_2903
    · exact prime_33739
  · decide +kernel

theorem prime_5507041150969 : Nat.Prime 5507041150969 := by
  apply nodeValid_prime [2, 3, 7, 137, 10837, 22079] ⟨5507041150969, 11, [(2, 3), (3, 1), (7, 1), (137, 1), (10837, 1), (22079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_10837
    · exact prime_22079
  · decide +kernel

theorem prime_5507041155703 : Nat.Prime 5507041155703 := by
  apply nodeValid_prime [2, 3, 89, 10312811153] ⟨5507041155703, 3, [(2, 1), (3, 1), (89, 1), (10312811153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_10312811153
  · decide +kernel

theorem prime_5507041156079 : Nat.Prime 5507041156079 := by
  apply nodeValid_prime [2, 7, 11, 40099, 127399] ⟨5507041156079, 7, [(2, 1), (7, 2), (11, 1), (40099, 1), (127399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_40099
    · exact prime_127399
  · decide +kernel

theorem prime_5511180925277 : Nat.Prime 5511180925277 := by
  apply nodeValid_prime [2, 13, 42187, 2512249] ⟨5511180925277, 2, [(2, 2), (13, 1), (42187, 1), (2512249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_42187
    · exact prime_2512249
  · decide +kernel

theorem prime_5511180926077 : Nat.Prime 5511180926077 := by
  apply nodeValid_prime [2, 3, 7, 19, 223, 439, 5039] ⟨5511180926077, 5, [(2, 2), (3, 1), (7, 2), (19, 1), (223, 1), (439, 1), (5039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_223
    · exact prime_439
    · exact prime_5039
  · decide +kernel

theorem prime_5511180936817 : Nat.Prime 5511180936817 := by
  apply nodeValid_prime [2, 3, 38272089839] ⟨5511180936817, 5, [(2, 4), (3, 2), (38272089839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_38272089839
  · decide +kernel

theorem prime_5515322772019 : Nat.Prime 5515322772019 := by
  apply nodeValid_prime [2, 3, 283, 42853, 75797] ⟨5515322772019, 2, [(2, 1), (3, 1), (283, 1), (42853, 1), (75797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_42853
    · exact prime_75797
  · decide +kernel

theorem prime_5515322773993 : Nat.Prime 5515322773993 := by
  apply nodeValid_prime [2, 3, 229805115583] ⟨5515322773993, 5, [(2, 3), (3, 1), (229805115583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229805115583
  · decide +kernel

theorem prime_5515322831087 : Nat.Prime 5515322831087 := by
  apply nodeValid_prime [2, 2757661415543] ⟨5515322831087, 5, [(2, 1), (2757661415543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2757661415543
  · decide +kernel

theorem prime_5519466839441 : Nat.Prime 5519466839441 := by
  apply nodeValid_prime [2, 5, 137, 5783, 87083] ⟨5519466839441, 3, [(2, 4), (5, 1), (137, 1), (5783, 1), (87083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_5783
    · exact prime_87083
  · decide +kernel

theorem prime_5519467066429 : Nat.Prime 5519467066429 := by
  apply nodeValid_prime [2, 3, 7, 7300882363] ⟨5519467066429, 6, [(2, 2), (3, 3), (7, 1), (7300882363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7300882363
  · decide +kernel

theorem prime_5519467066739 : Nat.Prime 5519467066739 := by
  apply nodeValid_prime [2, 2759733533369] ⟨5519467066739, 2, [(2, 1), (2759733533369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2759733533369
  · decide +kernel

theorem prime_5523612952567 : Nat.Prime 5523612952567 := by
  apply nodeValid_prime [2, 3, 31, 29696843831] ⟨5523612952567, 3, [(2, 1), (3, 1), (31, 1), (29696843831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_29696843831
  · decide +kernel

theorem prime_5523612954109 : Nat.Prime 5523612954109 := by
  apply nodeValid_prime [2, 3, 5437, 84660857] ⟨5523612954109, 6, [(2, 2), (3, 1), (5437, 1), (84660857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5437
    · exact prime_84660857
  · decide +kernel

theorem prime_5523612955309 : Nat.Prime 5523612955309 := by
  apply nodeValid_prime [2, 3, 7, 19, 29, 13260193] ⟨5523612955309, 6, [(2, 2), (3, 3), (7, 1), (19, 1), (29, 1), (13260193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_29
    · exact prime_13260193
  · decide +kernel

theorem prime_5527761175333 : Nat.Prime 5527761175333 := by
  apply nodeValid_prime [2, 3, 11, 4327, 3226021] ⟨5527761175333, 2, [(2, 2), (3, 2), (11, 1), (4327, 1), (3226021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4327
    · exact prime_3226021
  · decide +kernel

theorem prime_5527761254879 : Nat.Prime 5527761254879 := by
  apply nodeValid_prime [2, 281, 919, 2099, 5099] ⟨5527761254879, 13, [(2, 1), (281, 1), (919, 1), (2099, 1), (5099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_919
    · exact prime_2099
    · exact prime_5099
  · decide +kernel

theorem prime_5527761255091 : Nat.Prime 5527761255091 := by
  apply nodeValid_prime [2, 3, 5, 17, 109, 33146017] ⟨5527761255091, 10, [(2, 1), (3, 2), (5, 1), (17, 1), (109, 1), (33146017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_109
    · exact prime_33146017
  · decide +kernel

theorem prime_5531911321471 : Nat.Prime 5531911321471 := by
  apply nodeValid_prime [2, 3, 5, 1091, 3851, 43889] ⟨5531911321471, 3, [(2, 1), (3, 1), (5, 1), (1091, 1), (3851, 1), (43889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1091
    · exact prime_3851
    · exact prime_43889
  · decide +kernel

theorem prime_5531911323223 : Nat.Prime 5531911323223 := by
  apply nodeValid_prime [2, 3, 19, 31, 409, 719, 5323] ⟨5531911323223, 3, [(2, 1), (3, 1), (19, 1), (31, 1), (409, 1), (719, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_409
    · exact prime_719
    · exact prime_5323
  · decide +kernel

theorem prime_5531911497941 : Nat.Prime 5531911497941 := by
  apply nodeValid_prime [2, 5, 503, 549891799] ⟨5531911497941, 2, [(2, 2), (5, 1), (503, 1), (549891799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_503
    · exact prime_549891799
  · decide +kernel

theorem prime_5536063908187 : Nat.Prime 5536063908187 := by
  apply nodeValid_prime [2, 3, 7, 1627, 2531, 32009] ⟨5536063908187, 13, [(2, 1), (3, 1), (7, 1), (1627, 1), (2531, 1), (32009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1627
    · exact prime_2531
    · exact prime_32009
  · decide +kernel

theorem prime_5536063908233 : Nat.Prime 5536063908233 := by
  apply nodeValid_prime [2, 11, 13, 39709, 121867] ⟨5536063908233, 3, [(2, 3), (11, 1), (13, 1), (39709, 1), (121867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_39709
    · exact prime_121867
  · decide +kernel

theorem prime_5536063934861 : Nat.Prime 5536063934861 := by
  apply nodeValid_prime [2, 5, 276803196743] ⟨5536063934861, 2, [(2, 2), (5, 1), (276803196743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_276803196743
  · decide +kernel

theorem prime_5540218481969 : Nat.Prime 5540218481969 := by
  apply nodeValid_prime [2, 41, 8445455003] ⟨5540218481969, 3, [(2, 4), (41, 1), (8445455003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_8445455003
  · decide +kernel

theorem prime_5540218490333 : Nat.Prime 5540218490333 := by
  apply nodeValid_prime [2, 29, 41, 47, 587, 42223] ⟨5540218490333, 2, [(2, 2), (29, 1), (41, 1), (47, 1), (587, 1), (42223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_41
    · exact prime_47
    · exact prime_587
    · exact prime_42223
  · decide +kernel

theorem prime_5540218490479 : Nat.Prime 5540218490479 := by
  apply nodeValid_prime [2, 3, 7, 199, 20113, 32957] ⟨5540218490479, 3, [(2, 1), (3, 1), (7, 1), (199, 1), (20113, 1), (32957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199
    · exact prime_20113
    · exact prime_32957
  · decide +kernel

theorem prime_5544375137647 : Nat.Prime 5544375137647 := by
  apply nodeValid_prime [2, 3, 29, 31864224929] ⟨5544375137647, 3, [(2, 1), (3, 1), (29, 1), (31864224929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31864224929
  · decide +kernel

theorem prime_5544375137867 : Nat.Prime 5544375137867 := by
  apply nodeValid_prime [2, 14827, 186968879] ⟨5544375137867, 2, [(2, 1), (14827, 1), (186968879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_14827
    · exact prime_186968879
  · decide +kernel

theorem prime_5544375142567 : Nat.Prime 5544375142567 := by
  apply nodeValid_prime [2, 3, 13, 71081732597] ⟨5544375142567, 3, [(2, 1), (3, 1), (13, 1), (71081732597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71081732597
  · decide +kernel

theorem prime_5548533877703 : Nat.Prime 5548533877703 := by
  apply nodeValid_prime [2, 2774266938851] ⟨5548533877703, 5, [(2, 1), (2774266938851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2774266938851
  · decide +kernel

theorem prime_5548533877823 : Nat.Prime 5548533877823 := by
  apply nodeValid_prime [2, 13, 213405149147] ⟨5548533877823, 5, [(2, 1), (13, 1), (213405149147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_213405149147
  · decide +kernel

theorem prime_5548533913991 : Nat.Prime 5548533913991 := by
  apply nodeValid_prime [2, 5, 1907, 290956157] ⟨5548533913991, 17, [(2, 1), (5, 1), (1907, 1), (290956157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1907
    · exact prime_290956157
  · decide +kernel

theorem prime_5552694788237 : Nat.Prime 5552694788237 := by
  apply nodeValid_prime [2, 23, 60355378133] ⟨5552694788237, 2, [(2, 2), (23, 1), (60355378133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_60355378133
  · decide +kernel

theorem prime_5552694788867 : Nat.Prime 5552694788867 := by
  apply nodeValid_prime [2, 643567, 4313999] ⟨5552694788867, 2, [(2, 1), (643567, 1), (4313999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_643567
    · exact prime_4313999
  · decide +kernel

theorem prime_5552694809689 : Nat.Prime 5552694809689 := by
  apply nodeValid_prime [2, 3, 13, 79, 225279731] ⟨5552694809689, 7, [(2, 3), (3, 1), (13, 1), (79, 1), (225279731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_79
    · exact prime_225279731
  · decide +kernel

theorem prime_5556857790599 : Nat.Prime 5556857790599 := by
  apply nodeValid_prime [2, 2778428895299] ⟨5556857790599, 11, [(2, 1), (2778428895299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2778428895299
  · decide +kernel

theorem prime_5556857790787 : Nat.Prime 5556857790787 := by
  apply nodeValid_prime [2, 3, 926142965131] ⟨5556857790787, 2, [(2, 1), (3, 1), (926142965131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_926142965131
  · decide +kernel

theorem prime_5556857822801 : Nat.Prime 5556857822801 := by
  apply nodeValid_prime [2, 5, 19, 15259, 47917] ⟨5556857822801, 3, [(2, 4), (5, 2), (19, 1), (15259, 1), (47917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_15259
    · exact prime_47917
  · decide +kernel

theorem prime_5561022925291 : Nat.Prime 5561022925291 := by
  apply nodeValid_prime [2, 3, 5, 7, 26481061549] ⟨5561022925291, 28, [(2, 1), (3, 1), (5, 1), (7, 1), (26481061549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_26481061549
  · decide +kernel

theorem prime_5561022925771 : Nat.Prime 5561022925771 := by
  apply nodeValid_prime [2, 3, 5, 13, 14259033143] ⟨5561022925771, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (14259033143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_14259033143
  · decide +kernel

theorem prime_5561022944129 : Nat.Prime 5561022944129 := by
  apply nodeValid_prime [2, 19, 2286604829] ⟨5561022944129, 3, [(2, 7), (19, 1), (2286604829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2286604829
  · decide +kernel

end Sude.Lucas.Generated
