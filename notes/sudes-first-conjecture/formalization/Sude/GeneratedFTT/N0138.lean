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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0127
import Sude.GeneratedFTT.N0129
import Sude.GeneratedFTT.N0132

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11777 : Nat.Prime 11777 := by
  apply nodeValid_prime [2, 23] ⟨11777, 3, [(2, 9), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23
  · decide +kernel

theorem prime_16183 : Nat.Prime 16183 := by
  apply nodeValid_prime [2, 3, 29, 31] ⟨16183, 3, [(2, 1), (3, 2), (29, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
  · decide +kernel

theorem prime_18457 : Nat.Prime 18457 := by
  apply nodeValid_prime [2, 3, 769] ⟨18457, 5, [(2, 3), (3, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_769
  · decide +kernel

theorem prime_23099 : Nat.Prime 23099 := by
  apply nodeValid_prime [2, 11549] ⟨23099, 2, [(2, 1), (11549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11549
  · decide +kernel

theorem prime_27361 : Nat.Prime 27361 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨27361, 7, [(2, 5), (3, 2), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_27749 : Nat.Prime 27749 := by
  apply nodeValid_prime [2, 7, 991] ⟨27749, 3, [(2, 2), (7, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_991
  · decide +kernel

theorem prime_40697 : Nat.Prime 40697 := by
  apply nodeValid_prime [2, 5087] ⟨40697, 3, [(2, 3), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5087
  · decide +kernel

theorem prime_42737 : Nat.Prime 42737 := by
  apply nodeValid_prime [2, 2671] ⟨42737, 3, [(2, 4), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2671
  · decide +kernel

theorem prime_46477 : Nat.Prime 46477 := by
  apply nodeValid_prime [2, 3, 1291] ⟨46477, 2, [(2, 2), (3, 2), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1291
  · decide +kernel

theorem prime_47417 : Nat.Prime 47417 := by
  apply nodeValid_prime [2, 5927] ⟨47417, 3, [(2, 3), (5927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5927
  · decide +kernel

theorem prime_52609 : Nat.Prime 52609 := by
  apply nodeValid_prime [2, 3, 137] ⟨52609, 11, [(2, 7), (3, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_55673 : Nat.Prime 55673 := by
  apply nodeValid_prime [2, 6959] ⟨55673, 3, [(2, 3), (6959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6959
  · decide +kernel

theorem prime_60821 : Nat.Prime 60821 := by
  apply nodeValid_prime [2, 5, 3041] ⟨60821, 2, [(2, 2), (5, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3041
  · decide +kernel

theorem prime_74861 : Nat.Prime 74861 := by
  apply nodeValid_prime [2, 5, 19, 197] ⟨74861, 2, [(2, 2), (5, 1), (19, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_197
  · decide +kernel

theorem prime_96787 : Nat.Prime 96787 := by
  apply nodeValid_prime [2, 3, 19, 283] ⟨96787, 2, [(2, 1), (3, 2), (19, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_283
  · decide +kernel

theorem prime_120413 : Nat.Prime 120413 := by
  apply nodeValid_prime [2, 30103] ⟨120413, 2, [(2, 2), (30103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30103
  · decide +kernel

theorem prime_123401 : Nat.Prime 123401 := by
  apply nodeValid_prime [2, 5, 617] ⟨123401, 3, [(2, 3), (5, 2), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_617
  · decide +kernel

theorem prime_123817 : Nat.Prime 123817 := by
  apply nodeValid_prime [2, 3, 7, 11, 67] ⟨123817, 13, [(2, 3), (3, 1), (7, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_125669 : Nat.Prime 125669 := by
  apply nodeValid_prime [2, 89, 353] ⟨125669, 2, [(2, 2), (89, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_353
  · decide +kernel

theorem prime_132169 : Nat.Prime 132169 := by
  apply nodeValid_prime [2, 3, 5507] ⟨132169, 37, [(2, 3), (3, 1), (5507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5507
  · decide +kernel

theorem prime_136309 : Nat.Prime 136309 := by
  apply nodeValid_prime [2, 3, 37, 307] ⟨136309, 2, [(2, 2), (3, 1), (37, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_307
  · decide +kernel

theorem prime_140317 : Nat.Prime 140317 := by
  apply nodeValid_prime [2, 3, 11, 1063] ⟨140317, 2, [(2, 2), (3, 1), (11, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1063
  · decide +kernel

theorem prime_140681 : Nat.Prime 140681 := by
  apply nodeValid_prime [2, 5, 3517] ⟨140681, 3, [(2, 3), (5, 1), (3517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3517
  · decide +kernel

theorem prime_141257 : Nat.Prime 141257 := by
  apply nodeValid_prime [2, 17657] ⟨141257, 3, [(2, 3), (17657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17657
  · decide +kernel

theorem prime_161831 : Nat.Prime 161831 := by
  apply nodeValid_prime [2, 5, 16183] ⟨161831, 53, [(2, 1), (5, 1), (16183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16183
  · decide +kernel

theorem prime_246803 : Nat.Prime 246803 := by
  apply nodeValid_prime [2, 123401] ⟨246803, 2, [(2, 1), (123401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_123401
  · decide +kernel

theorem prime_281363 : Nat.Prime 281363 := by
  apply nodeValid_prime [2, 140681] ⟨281363, 2, [(2, 1), (140681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_140681
  · decide +kernel

theorem prime_310127 : Nat.Prime 310127 := by
  apply nodeValid_prime [2, 29, 5347] ⟨310127, 5, [(2, 1), (29, 1), (5347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_5347
  · decide +kernel

theorem prime_333757 : Nat.Prime 333757 := by
  apply nodeValid_prime [2, 3, 73, 127] ⟨333757, 11, [(2, 2), (3, 2), (73, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_127
  · decide +kernel

theorem prime_345139 : Nat.Prime 345139 := by
  apply nodeValid_prime [2, 3, 23, 41, 61] ⟨345139, 2, [(2, 1), (3, 1), (23, 1), (41, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_61
  · decide +kernel

theorem prime_349603 : Nat.Prime 349603 := by
  apply nodeValid_prime [2, 3, 11, 5297] ⟨349603, 2, [(2, 1), (3, 1), (11, 1), (5297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5297
  · decide +kernel

theorem prime_366001 : Nat.Prime 366001 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨366001, 29, [(2, 4), (3, 1), (5, 3), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_370679 : Nat.Prime 370679 := by
  apply nodeValid_prime [2, 7, 11, 29, 83] ⟨370679, 7, [(2, 1), (7, 1), (11, 1), (29, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_83
  · decide +kernel

theorem prime_446533 : Nat.Prime 446533 := by
  apply nodeValid_prime [2, 3, 127, 293] ⟨446533, 2, [(2, 2), (3, 1), (127, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_293
  · decide +kernel

theorem prime_447527 : Nat.Prime 447527 := by
  apply nodeValid_prime [2, 19, 11777] ⟨447527, 5, [(2, 1), (19, 1), (11777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_11777
  · decide +kernel

theorem prime_463993 : Nat.Prime 463993 := by
  apply nodeValid_prime [2, 3, 19333] ⟨463993, 5, [(2, 3), (3, 1), (19333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19333
  · decide +kernel

theorem prime_493607 : Nat.Prime 493607 := by
  apply nodeValid_prime [2, 246803] ⟨493607, 5, [(2, 1), (246803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_246803
  · decide +kernel

theorem prime_847543 : Nat.Prime 847543 := by
  apply nodeValid_prime [2, 3, 141257] ⟨847543, 3, [(2, 1), (3, 1), (141257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_141257
  · decide +kernel

theorem prime_988483 : Nat.Prime 988483 := by
  apply nodeValid_prime [2, 3, 11, 17, 881] ⟨988483, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_881
  · decide +kernel

theorem prime_988963 : Nat.Prime 988963 := by
  apply nodeValid_prime [2, 3, 13, 31, 409] ⟨988963, 2, [(2, 1), (3, 1), (13, 1), (31, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_409
  · decide +kernel

theorem prime_1038409 : Nat.Prime 1038409 := by
  apply nodeValid_prime [2, 3, 7, 883] ⟨1038409, 13, [(2, 3), (3, 1), (7, 2), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_883
  · decide +kernel

theorem prime_1089259 : Nat.Prime 1089259 := by
  apply nodeValid_prime [2, 3, 17, 59, 181] ⟨1089259, 3, [(2, 1), (3, 1), (17, 1), (59, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_59
    · exact prime_181
  · decide +kernel

theorem prime_1191563 : Nat.Prime 1191563 := by
  apply nodeValid_prime [2, 233, 2557] ⟨1191563, 2, [(2, 1), (233, 1), (2557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_2557
  · decide +kernel

theorem prime_1305701 : Nat.Prime 1305701 := by
  apply nodeValid_prime [2, 5, 11, 1187] ⟨1305701, 3, [(2, 2), (5, 2), (11, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1187
  · decide +kernel

theorem prime_1380557 : Nat.Prime 1380557 := by
  apply nodeValid_prime [2, 345139] ⟨1380557, 2, [(2, 2), (345139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_345139
  · decide +kernel

theorem prime_1612361 : Nat.Prime 1612361 := by
  apply nodeValid_prime [2, 5, 173, 233] ⟨1612361, 6, [(2, 3), (5, 1), (173, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_233
  · decide +kernel

theorem prime_1688179 : Nat.Prime 1688179 := by
  apply nodeValid_prime [2, 3, 281363] ⟨1688179, 2, [(2, 1), (3, 1), (281363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281363
  · decide +kernel

theorem prime_1860763 : Nat.Prime 1860763 := by
  apply nodeValid_prime [2, 3, 310127] ⟨1860763, 2, [(2, 1), (3, 1), (310127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_310127
  · decide +kernel

theorem prime_2180873 : Nat.Prime 2180873 := by
  apply nodeValid_prime [2, 41, 61, 109] ⟨2180873, 3, [(2, 3), (41, 1), (61, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_61
    · exact prime_109
  · decide +kernel

theorem prime_2317123 : Nat.Prime 2317123 := by
  apply nodeValid_prime [2, 3, 109, 1181] ⟨2317123, 2, [(2, 1), (3, 2), (109, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1181
  · decide +kernel

theorem prime_2579803 : Nat.Prime 2579803 := by
  apply nodeValid_prime [2, 3, 41, 10487] ⟨2579803, 2, [(2, 1), (3, 1), (41, 1), (10487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_10487
  · decide +kernel

theorem prime_3230321 : Nat.Prime 3230321 := by
  apply nodeValid_prime [2, 5, 149, 271] ⟨3230321, 3, [(2, 4), (5, 1), (149, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_271
  · decide +kernel

theorem prime_3445907 : Nat.Prime 3445907 := by
  apply nodeValid_prime [2, 23, 3257] ⟨3445907, 2, [(2, 1), (23, 2), (3257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3257
  · decide +kernel

theorem prime_3469691 : Nat.Prime 3469691 := by
  apply nodeValid_prime [2, 5, 7, 73, 97] ⟨3469691, 2, [(2, 1), (5, 1), (7, 2), (73, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_73
    · exact prime_97
  · decide +kernel

theorem prime_3624143 : Nat.Prime 3624143 := by
  apply nodeValid_prime [2, 163, 11117] ⟨3624143, 5, [(2, 1), (163, 1), (11117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_11117
  · decide +kernel

theorem prime_4302743 : Nat.Prime 4302743 := by
  apply nodeValid_prime [2, 71, 157, 193] ⟨4302743, 5, [(2, 1), (71, 1), (157, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_157
    · exact prime_193
  · decide +kernel

theorem prime_4357037 : Nat.Prime 4357037 := by
  apply nodeValid_prime [2, 1089259] ⟨4357037, 2, [(2, 2), (1089259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1089259
  · decide +kernel

theorem prime_4643911 : Nat.Prime 4643911 := by
  apply nodeValid_prime [2, 3, 5, 51599] ⟨4643911, 3, [(2, 1), (3, 2), (5, 1), (51599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_51599
  · decide +kernel

theorem prime_5531797 : Nat.Prime 5531797 := by
  apply nodeValid_prime [2, 3, 37, 4153] ⟨5531797, 6, [(2, 2), (3, 2), (37, 1), (4153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4153
  · decide +kernel

theorem prime_5593649 : Nat.Prime 5593649 := by
  apply nodeValid_prime [2, 349603] ⟨5593649, 3, [(2, 4), (349603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_349603
  · decide +kernel

theorem prime_6684833 : Nat.Prime 6684833 := by
  apply nodeValid_prime [2, 7, 11, 2713] ⟨6684833, 3, [(2, 5), (7, 1), (11, 1), (2713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_2713
  · decide +kernel

theorem prime_7143467 : Nat.Prime 7143467 := by
  apply nodeValid_prime [2, 11, 61, 5323] ⟨7143467, 2, [(2, 1), (11, 1), (61, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_5323
  · decide +kernel

theorem prime_7385299 : Nat.Prime 7385299 := by
  apply nodeValid_prime [2, 3, 47, 26189] ⟨7385299, 3, [(2, 1), (3, 1), (47, 1), (26189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_26189
  · decide +kernel

theorem prime_7834207 : Nat.Prime 7834207 := by
  apply nodeValid_prime [2, 3, 1305701] ⟨7834207, 3, [(2, 1), (3, 1), (1305701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1305701
  · decide +kernel

theorem prime_9449801 : Nat.Prime 9449801 := by
  apply nodeValid_prime [2, 5, 37, 1277] ⟨9449801, 3, [(2, 3), (5, 2), (37, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1277
  · decide +kernel

theorem prime_14103211 : Nat.Prime 14103211 := by
  apply nodeValid_prime [2, 3, 5, 11, 42737] ⟨14103211, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (42737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_42737
  · decide +kernel

theorem prime_14118277 : Nat.Prime 14118277 := by
  apply nodeValid_prime [2, 3, 43, 27361] ⟨14118277, 6, [(2, 2), (3, 1), (43, 1), (27361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_27361
  · decide +kernel

theorem prime_15172039 : Nat.Prime 15172039 := by
  apply nodeValid_prime [2, 3, 7, 120413] ⟨15172039, 7, [(2, 1), (3, 2), (7, 1), (120413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_120413
  · decide +kernel

theorem prime_15767987 : Nat.Prime 15767987 := by
  apply nodeValid_prime [2, 13, 19, 59, 541] ⟨15767987, 2, [(2, 1), (13, 1), (19, 1), (59, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_59
    · exact prime_541
  · decide +kernel

theorem prime_18066317 : Nat.Prime 18066317 := by
  apply nodeValid_prime [2, 23, 359, 547] ⟨18066317, 2, [(2, 2), (23, 1), (359, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_359
    · exact prime_547
  · decide +kernel

theorem prime_20935963 : Nat.Prime 20935963 := by
  apply nodeValid_prime [2, 3, 47, 73, 113] ⟨20935963, 2, [(2, 1), (3, 3), (47, 1), (73, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_73
    · exact prime_113
  · decide +kernel

theorem prime_23607179 : Nat.Prime 23607179 := by
  apply nodeValid_prime [2, 7, 73, 23099] ⟨23607179, 2, [(2, 1), (7, 1), (73, 1), (23099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_23099
  · decide +kernel

theorem prime_26108897 : Nat.Prime 26108897 := by
  apply nodeValid_prime [2, 11, 613] ⟨26108897, 3, [(2, 5), (11, 3), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_613
  · decide +kernel

theorem prime_32195213 : Nat.Prime 32195213 := by
  apply nodeValid_prime [2, 7, 17, 239, 283] ⟨32195213, 2, [(2, 2), (7, 1), (17, 1), (239, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_239
    · exact prime_283
  · decide +kernel

theorem prime_42775613 : Nat.Prime 42775613 := by
  apply nodeValid_prime [2, 11, 19, 2693] ⟨42775613, 3, [(2, 2), (11, 1), (19, 2), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_2693
  · decide +kernel

theorem prime_55058351 : Nat.Prime 55058351 := by
  apply nodeValid_prime [2, 5, 761, 1447] ⟨55058351, 23, [(2, 1), (5, 2), (761, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_761
    · exact prime_1447
  · decide +kernel

theorem prime_55822891 : Nat.Prime 55822891 := by
  apply nodeValid_prime [2, 3, 5, 1860763] ⟨55822891, 2, [(2, 1), (3, 1), (5, 1), (1860763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1860763
  · decide +kernel

theorem prime_68766083 : Nat.Prime 68766083 := by
  apply nodeValid_prime [2, 7, 11, 446533] ⟨68766083, 2, [(2, 1), (7, 1), (11, 1), (446533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_446533
  · decide +kernel

theorem prime_73852991 : Nat.Prime 73852991 := by
  apply nodeValid_prime [2, 5, 7385299] ⟨73852991, 7, [(2, 1), (5, 1), (7385299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7385299
  · decide +kernel

theorem prime_74765923 : Nat.Prime 74765923 := by
  apply nodeValid_prime [2, 3, 7, 11, 161831] ⟨74765923, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (161831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_161831
  · decide +kernel

theorem prime_96010879 : Nat.Prime 96010879 := by
  apply nodeValid_prime [2, 3, 23, 53, 13127] ⟨96010879, 6, [(2, 1), (3, 1), (23, 1), (53, 1), (13127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53
    · exact prime_13127
  · decide +kernel

theorem prime_147705983 : Nat.Prime 147705983 := by
  apply nodeValid_prime [2, 73852991] ⟨147705983, 5, [(2, 1), (73852991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73852991
  · decide +kernel

theorem prime_180172177 : Nat.Prime 180172177 := by
  apply nodeValid_prime [2, 3, 73, 51419] ⟨180172177, 5, [(2, 4), (3, 1), (73, 1), (51419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_51419
  · decide +kernel

theorem prime_229624817 : Nat.Prime 229624817 := by
  apply nodeValid_prime [2, 43, 333757] ⟨229624817, 3, [(2, 4), (43, 1), (333757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_333757
  · decide +kernel

theorem prime_256235701 : Nat.Prime 256235701 := by
  apply nodeValid_prime [2, 3, 5, 7, 17431] ⟨256235701, 2, [(2, 2), (3, 1), (5, 2), (7, 2), (17431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17431
  · decide +kernel

theorem prime_422138081 : Nat.Prime 422138081 := by
  apply nodeValid_prime [2, 5, 7, 13, 79, 367] ⟨422138081, 3, [(2, 5), (5, 1), (7, 1), (13, 1), (79, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_79
    · exact prime_367
  · decide +kernel

theorem prime_521120207 : Nat.Prime 521120207 := by
  apply nodeValid_prime [2, 101, 2579803] ⟨521120207, 5, [(2, 1), (101, 1), (2579803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_2579803
  · decide +kernel

theorem prime_726886301 : Nat.Prime 726886301 := by
  apply nodeValid_prime [2, 5, 7, 1038409] ⟨726886301, 10, [(2, 2), (5, 2), (7, 1), (1038409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1038409
  · decide +kernel

theorem prime_771668813 : Nat.Prime 771668813 := by
  apply nodeValid_prime [2, 19, 193, 52609] ⟨771668813, 2, [(2, 2), (19, 1), (193, 1), (52609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_193
    · exact prime_52609
  · decide +kernel

theorem prime_779380229 : Nat.Prime 779380229 := by
  apply nodeValid_prime [2, 11, 19, 139, 353] ⟨779380229, 2, [(2, 2), (11, 1), (19, 2), (139, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_139
    · exact prime_353
  · decide +kernel

theorem prime_844276163 : Nat.Prime 844276163 := by
  apply nodeValid_prime [2, 422138081] ⟨844276163, 2, [(2, 1), (422138081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_422138081
  · decide +kernel

theorem prime_1179255223 : Nat.Prime 1179255223 := by
  apply nodeValid_prime [2, 3, 179, 366001] ⟨1179255223, 3, [(2, 1), (3, 2), (179, 1), (366001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_366001
  · decide +kernel

theorem prime_1229374753 : Nat.Prime 1229374753 := by
  apply nodeValid_prime [2, 3, 83, 277, 557] ⟨1229374753, 5, [(2, 5), (3, 1), (83, 1), (277, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_277
    · exact prime_557
  · decide +kernel

theorem prime_2141021653 : Nat.Prime 2141021653 := by
  apply nodeValid_prime [2, 3, 7, 11, 2317123] ⟨2141021653, 5, [(2, 2), (3, 1), (7, 1), (11, 1), (2317123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_2317123
  · decide +kernel

theorem prime_2870833919 : Nat.Prime 2870833919 := by
  apply nodeValid_prime [2, 19, 23, 59, 55673] ⟨2870833919, 7, [(2, 1), (19, 1), (23, 1), (59, 1), (55673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_59
    · exact prime_55673
  · decide +kernel

theorem prime_3175251479 : Nat.Prime 3175251479 := by
  apply nodeValid_prime [2, 7, 41, 5531797] ⟨3175251479, 7, [(2, 1), (7, 1), (41, 1), (5531797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_5531797
  · decide +kernel

theorem prime_4230188749 : Nat.Prime 4230188749 := by
  apply nodeValid_prime [2, 3, 317, 370679] ⟨4230188749, 2, [(2, 2), (3, 2), (317, 1), (370679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
    · exact prime_370679
  · decide +kernel

theorem prime_4529218229 : Nat.Prime 4529218229 := by
  apply nodeValid_prime [2, 18617, 60821] ⟨4529218229, 2, [(2, 2), (18617, 1), (60821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18617
    · exact prime_60821
  · decide +kernel

theorem prime_5065656979 : Nat.Prime 5065656979 := by
  apply nodeValid_prime [2, 3, 844276163] ⟨5065656979, 2, [(2, 1), (3, 1), (844276163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_844276163
  · decide +kernel

theorem prime_10455290449 : Nat.Prime 10455290449 := by
  apply nodeValid_prime [2, 3, 257, 847543] ⟨10455290449, 13, [(2, 4), (3, 1), (257, 1), (847543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_847543
  · decide +kernel

theorem prime_10581526171 : Nat.Prime 10581526171 := by
  apply nodeValid_prime [2, 3, 5, 19, 223, 27749] ⟨10581526171, 10, [(2, 1), (3, 2), (5, 1), (19, 1), (223, 1), (27749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_223
    · exact prime_27749
  · decide +kernel

theorem prime_16920754997 : Nat.Prime 16920754997 := by
  apply nodeValid_prime [2, 4230188749] ⟨16920754997, 2, [(2, 2), (4230188749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4230188749
  · decide +kernel

theorem prime_17043054857 : Nat.Prime 17043054857 := by
  apply nodeValid_prime [2, 103, 1601, 12919] ⟨17043054857, 3, [(2, 3), (103, 1), (1601, 1), (12919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_1601
    · exact prime_12919
  · decide +kernel

theorem prime_21865401211 : Nat.Prime 21865401211 := by
  apply nodeValid_prime [2, 3, 5, 19, 809, 47417] ⟨21865401211, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (809, 1), (47417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_809
    · exact prime_47417
  · decide +kernel

theorem prime_24481092319 : Nat.Prime 24481092319 := by
  apply nodeValid_prime [2, 3, 17, 14118277] ⟨24481092319, 3, [(2, 1), (3, 1), (17, 2), (14118277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_14118277
  · decide +kernel

theorem prime_67683019973 : Nat.Prime 67683019973 := by
  apply nodeValid_prime [2, 17, 479, 821, 2531] ⟨67683019973, 2, [(2, 2), (17, 1), (479, 1), (821, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_479
    · exact prime_821
    · exact prime_2531
  · decide +kernel

theorem prime_76226142367 : Nat.Prime 76226142367 := by
  apply nodeValid_prime [2, 3, 11, 42775613] ⟨76226142367, 6, [(2, 1), (3, 4), (11, 1), (42775613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_42775613
  · decide +kernel

theorem prime_98211010363 : Nat.Prime 98211010363 := by
  apply nodeValid_prime [2, 3, 33161, 493607] ⟨98211010363, 2, [(2, 1), (3, 1), (33161, 1), (493607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33161
    · exact prime_493607
  · decide +kernel

theorem prime_148200476953 : Nat.Prime 148200476953 := by
  apply nodeValid_prime [2, 3, 11, 37, 15172039] ⟨148200476953, 5, [(2, 3), (3, 1), (11, 1), (37, 1), (15172039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_15172039
  · decide +kernel

theorem prime_191233168151 : Nat.Prime 191233168151 := by
  apply nodeValid_prime [2, 5, 40697, 93979] ⟨191233168151, 7, [(2, 1), (5, 2), (40697, 1), (93979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40697
    · exact prime_93979
  · decide +kernel

theorem prime_215137311281 : Nat.Prime 215137311281 := by
  apply nodeValid_prime [2, 5, 103, 26108897] ⟨215137311281, 6, [(2, 4), (5, 1), (103, 1), (26108897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_26108897
  · decide +kernel

theorem prime_311397827869 : Nat.Prime 311397827869 := by
  apply nodeValid_prime [2, 3, 277, 3469691] ⟨311397827869, 2, [(2, 2), (3, 4), (277, 1), (3469691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_3469691
  · decide +kernel

theorem prime_379266147427 : Nat.Prime 379266147427 := by
  apply nodeValid_prime [2, 3, 17, 317, 467, 25117] ⟨379266147427, 5, [(2, 1), (3, 1), (17, 1), (317, 1), (467, 1), (25117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_317
    · exact prime_467
    · exact prime_25117
  · decide +kernel

theorem prime_486261591917 : Nat.Prime 486261591917 := by
  apply nodeValid_prime [2, 19, 1487, 4302743] ⟨486261591917, 2, [(2, 2), (19, 1), (1487, 1), (4302743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1487
    · exact prime_4302743
  · decide +kernel

theorem prime_689402655373 : Nat.Prime 689402655373 := by
  apply nodeValid_prime [2, 3, 123817, 463993] ⟨689402655373, 2, [(2, 2), (3, 1), (123817, 1), (463993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_123817
    · exact prime_463993
  · decide +kernel

theorem prime_690849213367 : Nat.Prime 690849213367 := by
  apply nodeValid_prime [2, 3, 13, 19, 3527, 132169] ⟨690849213367, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (3527, 1), (132169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_3527
    · exact prime_132169
  · decide +kernel

theorem prime_852152742851 : Nat.Prime 852152742851 := by
  apply nodeValid_prime [2, 5, 17043054857] ⟨852152742851, 7, [(2, 1), (5, 2), (17043054857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17043054857
  · decide +kernel

theorem prime_1139394740621 : Nat.Prime 1139394740621 := by
  apply nodeValid_prime [2, 5, 3613, 15767987] ⟨1139394740621, 3, [(2, 2), (5, 1), (3613, 1), (15767987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3613
    · exact prime_15767987
  · decide +kernel

theorem prime_1716289145239 : Nat.Prime 1716289145239 := by
  apply nodeValid_prime [2, 3, 17, 277, 5897, 10301] ⟨1716289145239, 3, [(2, 1), (3, 1), (17, 1), (277, 1), (5897, 1), (10301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_277
    · exact prime_5897
    · exact prime_10301
  · decide +kernel

theorem prime_6793339784447 : Nat.Prime 6793339784447 := by
  apply nodeValid_prime [2, 37, 73, 1279, 13469] ⟨6793339784447, 5, [(2, 1), (37, 1), (73, 2), (1279, 1), (13469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_73
    · exact prime_1279
    · exact prime_13469
  · decide +kernel

theorem prime_6793339801783 : Nat.Prime 6793339801783 := by
  apply nodeValid_prime [2, 3, 107, 10581526171] ⟨6793339801783, 3, [(2, 1), (3, 1), (107, 1), (10581526171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_10581526171
  · decide +kernel

theorem prime_6793339803049 : Nat.Prime 6793339803049 := by
  apply nodeValid_prime [2, 3, 773, 1877, 65029] ⟨6793339803049, 13, [(2, 3), (3, 2), (773, 1), (1877, 1), (65029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_773
    · exact prime_1877
    · exact prime_65029
  · decide +kernel

theorem prime_6798111665819 : Nat.Prime 6798111665819 := by
  apply nodeValid_prime [2, 11, 61, 5065656979] ⟨6798111665819, 2, [(2, 1), (11, 1), (61, 1), (5065656979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_5065656979
  · decide +kernel

theorem prime_6798111665981 : Nat.Prime 6798111665981 := by
  apply nodeValid_prime [2, 5, 6089, 55822891] ⟨6798111665981, 2, [(2, 2), (5, 1), (6089, 1), (55822891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6089
    · exact prime_55822891
  · decide +kernel

theorem prime_6798111689191 : Nat.Prime 6798111689191 := by
  apply nodeValid_prime [2, 3, 5, 67, 45179, 74861] ⟨6798111689191, 11, [(2, 1), (3, 1), (5, 1), (67, 1), (45179, 1), (74861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_45179
    · exact prime_74861
  · decide +kernel

theorem prime_6802885778357 : Nat.Prime 6802885778357 := by
  apply nodeValid_prime [2, 17, 113, 743, 1191563] ⟨6802885778357, 2, [(2, 2), (17, 1), (113, 1), (743, 1), (1191563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_113
    · exact prime_743
    · exact prime_1191563
  · decide +kernel

theorem prime_6802885779959 : Nat.Prime 6802885779959 := by
  apply nodeValid_prime [2, 751, 4529218229] ⟨6802885779959, 11, [(2, 1), (751, 1), (4529218229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_751
    · exact prime_4529218229
  · decide +kernel

theorem prime_6802885862173 : Nat.Prime 6802885862173 := by
  apply nodeValid_prime [2, 3, 61, 79, 4357037] ⟨6802885862173, 6, [(2, 2), (3, 4), (61, 1), (79, 1), (4357037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_79
    · exact prime_4357037
  · decide +kernel

theorem prime_6807662268287 : Nat.Prime 6807662268287 := by
  apply nodeValid_prime [2, 11, 401, 771668813] ⟨6807662268287, 5, [(2, 1), (11, 1), (401, 1), (771668813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_401
    · exact prime_771668813
  · decide +kernel

theorem prime_6807662269841 : Nat.Prime 6807662269841 := by
  apply nodeValid_prime [2, 5, 23, 127, 659, 44207] ⟨6807662269841, 6, [(2, 4), (5, 1), (23, 1), (127, 1), (659, 1), (44207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_127
    · exact prime_659
    · exact prime_44207
  · decide +kernel

theorem prime_6807662286839 : Nat.Prime 6807662286839 := by
  apply nodeValid_prime [2, 7, 486261591917] ⟨6807662286839, 13, [(2, 1), (7, 1), (486261591917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_486261591917
  · decide +kernel

theorem prime_6812440968383 : Nat.Prime 6812440968383 := by
  apply nodeValid_prime [2, 7, 14969, 4643911] ⟨6812440968383, 5, [(2, 1), (7, 2), (14969, 1), (4643911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_14969
    · exact prime_4643911
  · decide +kernel

theorem prime_6812440969307 : Nat.Prime 6812440969307 := by
  apply nodeValid_prime [2, 7, 23, 89, 109, 2180873] ⟨6812440969307, 5, [(2, 1), (7, 1), (23, 1), (89, 1), (109, 1), (2180873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_89
    · exact prime_109
    · exact prime_2180873
  · decide +kernel

theorem prime_6812440978163 : Nat.Prime 6812440978163 := by
  apply nodeValid_prime [2, 988483, 3445907] ⟨6812440978163, 2, [(2, 1), (988483, 1), (3445907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_988483
    · exact prime_3445907
  · decide +kernel

theorem prime_6817221939383 : Nat.Prime 6817221939383 := by
  apply nodeValid_prime [2, 47, 491, 147705983] ⟨6817221939383, 7, [(2, 1), (47, 1), (491, 1), (147705983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_491
    · exact prime_147705983
  · decide +kernel

theorem prime_6817221939839 : Nat.Prime 6817221939839 := by
  apply nodeValid_prime [2, 23, 148200476953] ⟨6817221939839, 11, [(2, 1), (23, 1), (148200476953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_148200476953
  · decide +kernel

theorem prime_6817221942809 : Nat.Prime 6817221942809 := by
  apply nodeValid_prime [2, 852152742851] ⟨6817221942809, 3, [(2, 3), (852152742851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_852152742851
  · decide +kernel

theorem prime_6822005177833 : Nat.Prime 6822005177833 := by
  apply nodeValid_prime [2, 3, 13, 21865401211] ⟨6822005177833, 10, [(2, 3), (3, 1), (13, 1), (21865401211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_21865401211
  · decide +kernel

theorem prime_6822005224921 : Nat.Prime 6822005224921 := by
  apply nodeValid_prime [2, 3, 5, 29, 139, 14103211] ⟨6822005224921, 7, [(2, 3), (3, 1), (5, 1), (29, 1), (139, 1), (14103211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_139
    · exact prime_14103211
  · decide +kernel

theorem prime_6822005228821 : Nat.Prime 6822005228821 := by
  apply nodeValid_prime [2, 3, 5, 19, 2017, 988963] ⟨6822005228821, 2, [(2, 2), (3, 2), (5, 1), (19, 1), (2017, 1), (988963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_2017
    · exact prime_988963
  · decide +kernel

theorem prime_6826790653457 : Nat.Prime 6826790653457 := by
  apply nodeValid_prime [2, 107, 509, 7834207] ⟨6826790653457, 3, [(2, 4), (107, 1), (509, 1), (7834207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_509
    · exact prime_7834207
  · decide +kernel

theorem prime_6826790653687 : Nat.Prime 6826790653687 := by
  apply nodeValid_prime [2, 3, 379266147427] ⟨6826790653687, 3, [(2, 1), (3, 2), (379266147427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379266147427
  · decide +kernel

theorem prime_6826790679851 : Nat.Prime 6826790679851 := by
  apply nodeValid_prime [2, 5, 43, 3175251479] ⟨6826790679851, 7, [(2, 1), (5, 2), (43, 1), (3175251479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_3175251479
  · decide +kernel

theorem prime_6831578419117 : Nat.Prime 6831578419117 := by
  apply nodeValid_prime [2, 3, 11, 233, 1583, 140317] ⟨6831578419117, 15, [(2, 2), (3, 1), (11, 1), (233, 1), (1583, 1), (140317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_233
    · exact prime_1583
    · exact prime_140317
  · decide +kernel

theorem prime_6831578419753 : Nat.Prime 6831578419753 := by
  apply nodeValid_prime [2, 3, 73, 8713, 447527] ⟨6831578419753, 5, [(2, 3), (3, 1), (73, 1), (8713, 1), (447527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_8713
    · exact prime_447527
  · decide +kernel

theorem prime_6831578454017 : Nat.Prime 6831578454017 := by
  apply nodeValid_prime [2, 499, 6684833] ⟨6831578454017, 3, [(2, 11), (499, 1), (6684833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_499
    · exact prime_6684833
  · decide +kernel

theorem prime_6836368443727 : Nat.Prime 6836368443727 := by
  apply nodeValid_prime [2, 3, 1139394740621] ⟨6836368443727, 3, [(2, 1), (3, 1), (1139394740621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1139394740621
  · decide +kernel

theorem prime_6836368444123 : Nat.Prime 6836368444123 := by
  apply nodeValid_prime [2, 3, 7, 23, 37, 43, 241, 18457] ⟨6836368444123, 7, [(2, 1), (3, 1), (7, 1), (23, 1), (37, 1), (43, 1), (241, 1), (18457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_37
    · exact prime_43
    · exact prime_241
    · exact prime_18457
  · decide +kernel

theorem prime_6836368502681 : Nat.Prime 6836368502681 := by
  apply nodeValid_prime [2, 5, 23, 29, 256235701] ⟨6836368502681, 3, [(2, 3), (5, 1), (23, 1), (29, 1), (256235701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_29
    · exact prime_256235701
  · decide +kernel

theorem prime_6841160810371 : Nat.Prime 6841160810371 := by
  apply nodeValid_prime [2, 3, 5, 787, 32195213] ⟨6841160810371, 12, [(2, 1), (3, 3), (5, 1), (787, 1), (32195213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_787
    · exact prime_32195213
  · decide +kernel

theorem prime_6841160885659 : Nat.Prime 6841160885659 := by
  apply nodeValid_prime [2, 3, 11, 4951, 20935963] ⟨6841160885659, 2, [(2, 1), (3, 1), (11, 1), (4951, 1), (20935963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4951
    · exact prime_20935963
  · decide +kernel

theorem prime_6841160886191 : Nat.Prime 6841160886191 := by
  apply nodeValid_prime [2, 5, 41, 103, 109, 1153, 1289] ⟨6841160886191, 7, [(2, 1), (5, 1), (41, 1), (103, 1), (109, 1), (1153, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_103
    · exact prime_109
    · exact prime_1153
    · exact prime_1289
  · decide +kernel

theorem prime_6845955363341 : Nat.Prime 6845955363341 := by
  apply nodeValid_prime [2, 5, 6217, 55058351] ⟨6845955363341, 2, [(2, 2), (5, 1), (6217, 1), (55058351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6217
    · exact prime_55058351
  · decide +kernel

theorem prime_6845955365021 : Nat.Prime 6845955365021 := by
  apply nodeValid_prime [2, 5, 29, 59, 83, 40853] ⟨6845955365021, 2, [(2, 2), (5, 1), (29, 1), (59, 2), (83, 1), (40853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_59
    · exact prime_83
    · exact prime_40853
  · decide +kernel

theorem prime_6845955388999 : Nat.Prime 6845955388999 := by
  apply nodeValid_prime [2, 3, 11, 28621, 3624143] ⟨6845955388999, 3, [(2, 1), (3, 1), (11, 1), (28621, 1), (3624143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_28621
    · exact prime_3624143
  · decide +kernel

theorem prime_6850752212911 : Nat.Prime 6850752212911 := by
  apply nodeValid_prime [2, 3, 5, 293, 779380229] ⟨6850752212911, 15, [(2, 1), (3, 1), (5, 1), (293, 1), (779380229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_779380229
  · decide +kernel

theorem prime_6850752213119 : Nat.Prime 6850752213119 := by
  apply nodeValid_prime [2, 11, 311397827869] ⟨6850752213119, 11, [(2, 1), (11, 1), (311397827869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_311397827869
  · decide +kernel

theorem prime_6850752252793 : Nat.Prime 6850752252793 := by
  apply nodeValid_prime [2, 3, 7, 593, 68766083] ⟨6850752252793, 10, [(2, 3), (3, 1), (7, 1), (593, 1), (68766083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_593
    · exact prime_68766083
  · decide +kernel

theorem prime_6855551332907 : Nat.Prime 6855551332907 := by
  apply nodeValid_prime [2, 1601, 2141021653] ⟨6855551332907, 2, [(2, 1), (1601, 1), (2141021653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1601
    · exact prime_2141021653
  · decide +kernel

theorem prime_6855551334851 : Nat.Prime 6855551334851 := by
  apply nodeValid_prime [2, 5, 761, 180172177] ⟨6855551334851, 6, [(2, 1), (5, 2), (761, 1), (180172177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_761
    · exact prime_180172177
  · decide +kernel

theorem prime_6855551398573 : Nat.Prime 6855551398573 := by
  apply nodeValid_prime [2, 3, 199, 2870833919] ⟨6855551398573, 2, [(2, 2), (3, 1), (199, 1), (2870833919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_2870833919
  · decide +kernel

theorem prime_6860352813031 : Nat.Prime 6860352813031 := by
  apply nodeValid_prime [2, 3, 5, 76226142367] ⟨6860352813031, 6, [(2, 1), (3, 2), (5, 1), (76226142367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_76226142367
  · decide +kernel

theorem prime_6860352908839 : Nat.Prime 6860352908839 := by
  apply nodeValid_prime [2, 3, 11, 13, 726886301] ⟨6860352908839, 11, [(2, 1), (3, 1), (11, 2), (13, 1), (726886301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_726886301
  · decide +kernel

theorem prime_6860352910781 : Nat.Prime 6860352910781 := by
  apply nodeValid_prime [2, 5, 97, 25943, 136309] ⟨6860352910781, 3, [(2, 2), (5, 1), (97, 1), (25943, 1), (136309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_25943
    · exact prime_136309
  · decide +kernel

theorem prime_6865156510633 : Nat.Prime 6865156510633 := by
  apply nodeValid_prime [2, 3, 7, 577, 23607179] ⟨6865156510633, 5, [(2, 3), (3, 2), (7, 1), (577, 1), (23607179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_577
    · exact prime_23607179
  · decide +kernel

theorem prime_6865156580957 : Nat.Prime 6865156580957 := by
  apply nodeValid_prime [2, 1716289145239] ⟨6865156580957, 2, [(2, 2), (1716289145239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1716289145239
  · decide +kernel

theorem prime_6865156581707 : Nat.Prime 6865156581707 := by
  apply nodeValid_prime [2, 31, 1481, 74765923] ⟨6865156581707, 2, [(2, 1), (31, 1), (1481, 1), (74765923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1481
    · exact prime_74765923
  · decide +kernel

theorem prime_6869962434553 : Nat.Prime 6869962434553 := by
  apply nodeValid_prime [2, 3, 7, 12659, 3230321] ⟨6869962434553, 5, [(2, 3), (3, 1), (7, 1), (12659, 1), (3230321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12659
    · exact prime_3230321
  · decide +kernel

theorem prime_6869962435967 : Nat.Prime 6869962435967 := by
  apply nodeValid_prime [2, 7, 19, 269, 96010879] ⟨6869962435967, 5, [(2, 1), (7, 1), (19, 1), (269, 1), (96010879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_269
    · exact prime_96010879
  · decide +kernel

theorem prime_6869962480517 : Nat.Prime 6869962480517 := by
  apply nodeValid_prime [2, 23, 2663, 2917, 9613] ⟨6869962480517, 2, [(2, 2), (23, 1), (2663, 1), (2917, 1), (9613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2663
    · exact prime_2917
    · exact prime_9613
  · decide +kernel

theorem prime_6874770725411 : Nat.Prime 6874770725411 := by
  apply nodeValid_prime [2, 5, 7, 98211010363] ⟨6874770725411, 2, [(2, 1), (5, 1), (7, 1), (98211010363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_98211010363
  · decide +kernel

theorem prime_6874770737357 : Nat.Prime 6874770737357 := by
  apply nodeValid_prime [2, 17, 67, 1093, 1380557] ⟨6874770737357, 2, [(2, 2), (17, 1), (67, 1), (1093, 1), (1380557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_67
    · exact prime_1093
    · exact prime_1380557
  · decide +kernel

theorem prime_6879581115443 : Nat.Prime 6879581115443 := by
  apply nodeValid_prime [2, 7, 47, 10455290449] ⟨6879581115443, 2, [(2, 1), (7, 1), (47, 1), (10455290449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_10455290449
  · decide +kernel

theorem prime_6879581117789 : Nat.Prime 6879581117789 := by
  apply nodeValid_prime [2, 1399, 1229374753] ⟨6879581117789, 2, [(2, 2), (1399, 1), (1229374753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1399
    · exact prime_1229374753
  · decide +kernel

theorem prime_6879581248333 : Nat.Prime 6879581248333 := by
  apply nodeValid_prime [2, 3, 13, 2441, 18066317] ⟨6879581248333, 5, [(2, 2), (3, 1), (13, 1), (2441, 1), (18066317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2441
    · exact prime_18066317
  · decide +kernel

theorem prime_6884393960993 : Nat.Prime 6884393960993 := by
  apply nodeValid_prime [2, 215137311281] ⟨6884393960993, 3, [(2, 5), (215137311281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_215137311281
  · decide +kernel

theorem prime_6884393962001 : Nat.Prime 6884393962001 := by
  apply nodeValid_prime [2, 5, 2039, 1688179] ⟨6884393962001, 6, [(2, 4), (5, 3), (2039, 1), (1688179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2039
    · exact prime_1688179
  · decide +kernel

theorem prime_6884394053437 : Nat.Prime 6884394053437 := by
  apply nodeValid_prime [2, 3, 191233168151] ⟨6884394053437, 5, [(2, 2), (3, 2), (191233168151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191233168151
  · decide +kernel

theorem prime_6889209012767 : Nat.Prime 6889209012767 := by
  apply nodeValid_prime [2, 23, 127, 1179255223] ⟨6889209012767, 5, [(2, 1), (23, 1), (127, 1), (1179255223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_127
    · exact prime_1179255223
  · decide +kernel

theorem prime_6889209013307 : Nat.Prime 6889209013307 := by
  apply nodeValid_prime [2, 17, 125669, 1612361] ⟨6889209013307, 2, [(2, 1), (17, 1), (125669, 1), (1612361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_125669
    · exact prime_1612361
  · decide +kernel

theorem prime_6889209136541 : Nat.Prime 6889209136541 := by
  apply nodeValid_prime [2, 5, 661, 521120207] ⟨6889209136541, 2, [(2, 2), (5, 1), (661, 1), (521120207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_661
    · exact prime_521120207
  · decide +kernel

theorem prime_6894026491007 : Nat.Prime 6894026491007 := by
  apply nodeValid_prime [2, 29, 79, 157, 277, 1193] ⟨6894026491007, 5, [(2, 1), (29, 2), (79, 1), (157, 1), (277, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_79
    · exact prime_157
    · exact prime_277
    · exact prime_1193
  · decide +kernel

theorem prime_6894026549909 : Nat.Prime 6894026549909 := by
  apply nodeValid_prime [2, 17, 239, 9127, 46477] ⟨6894026549909, 2, [(2, 2), (17, 1), (239, 1), (9127, 1), (46477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_239
    · exact prime_9127
    · exact prime_46477
  · decide +kernel

theorem prime_6894026553731 : Nat.Prime 6894026553731 := by
  apply nodeValid_prime [2, 5, 689402655373] ⟨6894026553731, 10, [(2, 1), (5, 1), (689402655373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_689402655373
  · decide +kernel

theorem prime_6898846116053 : Nat.Prime 6898846116053 := by
  apply nodeValid_prime [2, 11, 47, 467, 7143467] ⟨6898846116053, 2, [(2, 2), (11, 1), (47, 1), (467, 1), (7143467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_467
    · exact prime_7143467
  · decide +kernel

theorem prime_6898846116829 : Nat.Prime 6898846116829 := by
  apply nodeValid_prime [2, 3, 139, 151, 283, 96787] ⟨6898846116829, 2, [(2, 2), (3, 1), (139, 1), (151, 1), (283, 1), (96787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_151
    · exact prime_283
    · exact prime_96787
  · decide +kernel

theorem prime_6898846119653 : Nat.Prime 6898846119653 := by
  apply nodeValid_prime [2, 229, 797, 9449801] ⟨6898846119653, 2, [(2, 2), (229, 1), (797, 1), (9449801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_797
    · exact prime_9449801
  · decide +kernel

theorem prime_6903668033959 : Nat.Prime 6903668033959 := by
  apply nodeValid_prime [2, 3, 47, 24481092319] ⟨6903668033959, 3, [(2, 1), (3, 1), (47, 1), (24481092319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_24481092319
  · decide +kernel

theorem prime_6903668037247 : Nat.Prime 6903668037247 := by
  apply nodeValid_prime [2, 3, 17, 67683019973] ⟨6903668037247, 3, [(2, 1), (3, 1), (17, 1), (67683019973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67683019973
  · decide +kernel

theorem prime_6903668038777 : Nat.Prime 6903668038777 := by
  apply nodeValid_prime [2, 3, 17, 16920754997] ⟨6903668038777, 5, [(2, 3), (3, 1), (17, 1), (16920754997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_16920754997
  · decide +kernel

theorem prime_6908492133671 : Nat.Prime 6908492133671 := by
  apply nodeValid_prime [2, 5, 690849213367] ⟨6908492133671, 7, [(2, 1), (5, 1), (690849213367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_690849213367
  · decide +kernel

theorem prime_6908492133941 : Nat.Prime 6908492133941 := by
  apply nodeValid_prime [2, 5, 37, 1669, 5593649] ⟨6908492133941, 2, [(2, 2), (5, 1), (37, 1), (1669, 1), (5593649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1669
    · exact prime_5593649
  · decide +kernel

theorem prime_6908492244263 : Nat.Prime 6908492244263 := by
  apply nodeValid_prime [2, 7, 307, 229624817] ⟨6908492244263, 10, [(2, 1), (7, 2), (307, 1), (229624817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_307
    · exact prime_229624817
  · decide +kernel

end Sude.Lucas.Generated
