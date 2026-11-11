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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0118
import Sude.GeneratedFTT.N0136

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_12503 : Nat.Prime 12503 := by
  apply nodeValid_prime [2, 7, 19, 47] ⟨12503, 5, [(2, 1), (7, 1), (19, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_13799 : Nat.Prime 13799 := by
  apply nodeValid_prime [2, 6899] ⟨13799, 7, [(2, 1), (6899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6899
  · decide +kernel

theorem prime_15427 : Nat.Prime 15427 := by
  apply nodeValid_prime [2, 3, 857] ⟨15427, 2, [(2, 1), (3, 2), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_857
  · decide +kernel

theorem prime_15887 : Nat.Prime 15887 := by
  apply nodeValid_prime [2, 13, 47] ⟨15887, 5, [(2, 1), (13, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_21019 : Nat.Prime 21019 := by
  apply nodeValid_prime [2, 3, 31, 113] ⟨21019, 2, [(2, 1), (3, 1), (31, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_113
  · decide +kernel

theorem prime_22073 : Nat.Prime 22073 := by
  apply nodeValid_prime [2, 31, 89] ⟨22073, 3, [(2, 3), (31, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_89
  · decide +kernel

theorem prime_22511 : Nat.Prime 22511 := by
  apply nodeValid_prime [2, 5, 2251] ⟨22511, 11, [(2, 1), (5, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2251
  · decide +kernel

theorem prime_27487 : Nat.Prime 27487 := by
  apply nodeValid_prime [2, 3, 509] ⟨27487, 3, [(2, 1), (3, 3), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_509
  · decide +kernel

theorem prime_28807 : Nat.Prime 28807 := by
  apply nodeValid_prime [2, 3, 4801] ⟨28807, 11, [(2, 1), (3, 1), (4801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4801
  · decide +kernel

theorem prime_29221 : Nat.Prime 29221 := by
  apply nodeValid_prime [2, 3, 5, 487] ⟨29221, 2, [(2, 2), (3, 1), (5, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_487
  · decide +kernel

theorem prime_34703 : Nat.Prime 34703 := by
  apply nodeValid_prime [2, 17351] ⟨34703, 5, [(2, 1), (17351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17351
  · decide +kernel

theorem prime_52379 : Nat.Prime 52379 := by
  apply nodeValid_prime [2, 26189] ⟨52379, 2, [(2, 1), (26189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26189
  · decide +kernel

theorem prime_64627 : Nat.Prime 64627 := by
  apply nodeValid_prime [2, 3, 10771] ⟨64627, 5, [(2, 1), (3, 1), (10771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10771
  · decide +kernel

theorem prime_67867 : Nat.Prime 67867 := by
  apply nodeValid_prime [2, 3, 11311] ⟨67867, 2, [(2, 1), (3, 1), (11311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11311
  · decide +kernel

theorem prime_69019 : Nat.Prime 69019 := by
  apply nodeValid_prime [2, 3, 11503] ⟨69019, 2, [(2, 1), (3, 1), (11503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11503
  · decide +kernel

theorem prime_69491 : Nat.Prime 69491 := by
  apply nodeValid_prime [2, 5, 6949] ⟨69491, 2, [(2, 1), (5, 1), (6949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6949
  · decide +kernel

theorem prime_71399 : Nat.Prime 71399 := by
  apply nodeValid_prime [2, 29, 1231] ⟨71399, 11, [(2, 1), (29, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1231
  · decide +kernel

theorem prime_75511 : Nat.Prime 75511 := by
  apply nodeValid_prime [2, 3, 5, 839] ⟨75511, 3, [(2, 1), (3, 2), (5, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_839
  · decide +kernel

theorem prime_104759 : Nat.Prime 104759 := by
  apply nodeValid_prime [2, 52379] ⟨104759, 7, [(2, 1), (52379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_52379
  · decide +kernel

theorem prime_114067 : Nat.Prime 114067 := by
  apply nodeValid_prime [2, 3, 6337] ⟨114067, 2, [(2, 1), (3, 2), (6337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6337
  · decide +kernel

theorem prime_114761 : Nat.Prime 114761 := by
  apply nodeValid_prime [2, 5, 19, 151] ⟨114761, 3, [(2, 3), (5, 1), (19, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_151
  · decide +kernel

theorem prime_121853 : Nat.Prime 121853 := by
  apply nodeValid_prime [2, 41, 743] ⟨121853, 2, [(2, 2), (41, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_743
  · decide +kernel

theorem prime_141931 : Nat.Prime 141931 := by
  apply nodeValid_prime [2, 3, 5, 19, 83] ⟨141931, 2, [(2, 1), (3, 2), (5, 1), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_146437 : Nat.Prime 146437 := by
  apply nodeValid_prime [2, 3, 12203] ⟨146437, 2, [(2, 2), (3, 1), (12203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12203
  · decide +kernel

theorem prime_161053 : Nat.Prime 161053 := by
  apply nodeValid_prime [2, 3, 13421] ⟨161053, 6, [(2, 2), (3, 1), (13421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13421
  · decide +kernel

theorem prime_162847 : Nat.Prime 162847 := by
  apply nodeValid_prime [2, 3, 83, 109] ⟨162847, 3, [(2, 1), (3, 2), (83, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_109
  · decide +kernel

theorem prime_163901 : Nat.Prime 163901 := by
  apply nodeValid_prime [2, 5, 11, 149] ⟨163901, 3, [(2, 2), (5, 2), (11, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_149
  · decide +kernel

theorem prime_211097 : Nat.Prime 211097 := by
  apply nodeValid_prime [2, 26387] ⟨211097, 3, [(2, 3), (26387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26387
  · decide +kernel

theorem prime_238729 : Nat.Prime 238729 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨238729, 11, [(2, 3), (3, 1), (7, 3), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_243707 : Nat.Prime 243707 := by
  apply nodeValid_prime [2, 121853] ⟨243707, 2, [(2, 1), (121853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_121853
  · decide +kernel

theorem prime_265093 : Nat.Prime 265093 := by
  apply nodeValid_prime [2, 3, 22091] ⟨265093, 2, [(2, 2), (3, 1), (22091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22091
  · decide +kernel

theorem prime_274811 : Nat.Prime 274811 := by
  apply nodeValid_prime [2, 5, 27481] ⟨274811, 2, [(2, 1), (5, 1), (27481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_27481
  · decide +kernel

theorem prime_277897 : Nat.Prime 277897 := by
  apply nodeValid_prime [2, 3, 11579] ⟨277897, 15, [(2, 3), (3, 1), (11579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11579
  · decide +kernel

theorem prime_300497 : Nat.Prime 300497 := by
  apply nodeValid_prime [2, 7, 2683] ⟨300497, 3, [(2, 4), (7, 1), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2683
  · decide +kernel

theorem prime_332441 : Nat.Prime 332441 := by
  apply nodeValid_prime [2, 5, 8311] ⟨332441, 3, [(2, 3), (5, 1), (8311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8311
  · decide +kernel

theorem prime_334231 : Nat.Prime 334231 := by
  apply nodeValid_prime [2, 3, 5, 13, 857] ⟨334231, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_857
  · decide +kernel

theorem prime_399389 : Nat.Prime 399389 := by
  apply nodeValid_prime [2, 11, 29, 313] ⟨399389, 2, [(2, 2), (11, 1), (29, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_313
  · decide +kernel

theorem prime_402091 : Nat.Prime 402091 := by
  apply nodeValid_prime [2, 3, 5, 13, 1031] ⟨402091, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1031
  · decide +kernel

theorem prime_581663 : Nat.Prime 581663 := by
  apply nodeValid_prime [2, 337, 863] ⟨581663, 5, [(2, 1), (337, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_863
  · decide +kernel

theorem prime_591499 : Nat.Prime 591499 := by
  apply nodeValid_prime [2, 3, 17, 1933] ⟨591499, 3, [(2, 1), (3, 2), (17, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1933
  · decide +kernel

theorem prime_592873 : Nat.Prime 592873 := by
  apply nodeValid_prime [2, 3, 7, 3529] ⟨592873, 10, [(2, 3), (3, 1), (7, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3529
  · decide +kernel

theorem prime_600631 : Nat.Prime 600631 := by
  apply nodeValid_prime [2, 3, 5, 20021] ⟨600631, 6, [(2, 1), (3, 1), (5, 1), (20021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20021
  · decide +kernel

theorem prime_652609 : Nat.Prime 652609 := by
  apply nodeValid_prime [2, 3, 11, 103] ⟨652609, 7, [(2, 6), (3, 2), (11, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_103
  · decide +kernel

theorem prime_732041 : Nat.Prime 732041 := by
  apply nodeValid_prime [2, 5, 18301] ⟨732041, 11, [(2, 3), (5, 1), (18301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18301
  · decide +kernel

theorem prime_906749 : Nat.Prime 906749 := by
  apply nodeValid_prime [2, 397, 571] ⟨906749, 2, [(2, 2), (397, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_571
  · decide +kernel

theorem prime_966319 : Nat.Prime 966319 := by
  apply nodeValid_prime [2, 3, 161053] ⟨966319, 6, [(2, 1), (3, 1), (161053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_161053
  · decide +kernel

theorem prime_1041091 : Nat.Prime 1041091 := by
  apply nodeValid_prime [2, 3, 5, 34703] ⟨1041091, 3, [(2, 1), (3, 1), (5, 1), (34703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_34703
  · decide +kernel

theorem prime_1352419 : Nat.Prime 1352419 := by
  apply nodeValid_prime [2, 3, 17, 13259] ⟨1352419, 2, [(2, 1), (3, 1), (17, 1), (13259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_13259
  · decide +kernel

theorem prime_1580987 : Nat.Prime 1580987 := by
  apply nodeValid_prime [2, 11, 47, 139] ⟨1580987, 2, [(2, 1), (11, 2), (47, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_139
  · decide +kernel

theorem prime_1600631 : Nat.Prime 1600631 := by
  apply nodeValid_prime [2, 5, 67, 2389] ⟨1600631, 7, [(2, 1), (5, 1), (67, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_2389
  · decide +kernel

theorem prime_1661243 : Nat.Prime 1661243 := by
  apply nodeValid_prime [2, 11, 75511] ⟨1661243, 2, [(2, 1), (11, 1), (75511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_75511
  · decide +kernel

theorem prime_1667417 : Nat.Prime 1667417 := by
  apply nodeValid_prime [2, 257, 811] ⟨1667417, 3, [(2, 3), (257, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_811
  · decide +kernel

theorem prime_1883113 : Nat.Prime 1883113 := by
  apply nodeValid_prime [2, 3, 7, 11, 1019] ⟨1883113, 5, [(2, 3), (3, 1), (7, 1), (11, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1019
  · decide +kernel

theorem prime_1997111 : Nat.Prime 1997111 := by
  apply nodeValid_prime [2, 5, 41, 4871] ⟨1997111, 7, [(2, 1), (5, 1), (41, 1), (4871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_4871
  · decide +kernel

theorem prime_2005387 : Nat.Prime 2005387 := by
  apply nodeValid_prime [2, 3, 334231] ⟨2005387, 3, [(2, 1), (3, 1), (334231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_334231
  · decide +kernel

theorem prime_2100313 : Nat.Prime 2100313 := by
  apply nodeValid_prime [2, 3, 31, 941] ⟨2100313, 5, [(2, 3), (3, 2), (31, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_941
  · decide +kernel

theorem prime_2307479 : Nat.Prime 2307479 := by
  apply nodeValid_prime [2, 17, 67867] ⟨2307479, 11, [(2, 1), (17, 1), (67867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_67867
  · decide +kernel

theorem prime_2711573 : Nat.Prime 2711573 := by
  apply nodeValid_prime [2, 61, 11113] ⟨2711573, 2, [(2, 2), (61, 1), (11113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_11113
  · decide +kernel

theorem prime_3024481 : Nat.Prime 3024481 := by
  apply nodeValid_prime [2, 3, 5, 6301] ⟨3024481, 7, [(2, 5), (3, 1), (5, 1), (6301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6301
  · decide +kernel

theorem prime_3278021 : Nat.Prime 3278021 := by
  apply nodeValid_prime [2, 5, 163901] ⟨3278021, 2, [(2, 2), (5, 1), (163901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163901
  · decide +kernel

theorem prime_3908329 : Nat.Prime 3908329 := by
  apply nodeValid_prime [2, 3, 162847] ⟨3908329, 11, [(2, 3), (3, 1), (162847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_162847
  · decide +kernel

theorem prime_4614959 : Nat.Prime 4614959 := by
  apply nodeValid_prime [2, 2307479] ⟨4614959, 13, [(2, 1), (2307479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2307479
  · decide +kernel

theorem prime_4855133 : Nat.Prime 4855133 := by
  apply nodeValid_prime [2, 17, 71399] ⟨4855133, 2, [(2, 2), (17, 1), (71399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71399
  · decide +kernel

theorem prime_4888739 : Nat.Prime 4888739 := by
  apply nodeValid_prime [2, 19, 127, 1013] ⟨4888739, 2, [(2, 1), (19, 1), (127, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_127
    · exact prime_1013
  · decide +kernel

theorem prime_4956733 : Nat.Prime 4956733 := by
  apply nodeValid_prime [2, 3, 11, 12517] ⟨4956733, 2, [(2, 2), (3, 2), (11, 1), (12517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_12517
  · decide +kernel

theorem prime_5021257 : Nat.Prime 5021257 := by
  apply nodeValid_prime [2, 3, 17, 31, 397] ⟨5021257, 7, [(2, 3), (3, 1), (17, 1), (31, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_397
  · decide +kernel

theorem prime_5193187 : Nat.Prime 5193187 := by
  apply nodeValid_prime [2, 3, 97, 8923] ⟨5193187, 2, [(2, 1), (3, 1), (97, 1), (8923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_8923
  · decide +kernel

theorem prime_6648977 : Nat.Prime 6648977 := by
  apply nodeValid_prime [2, 149, 2789] ⟨6648977, 3, [(2, 4), (149, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_2789
  · decide +kernel

theorem prime_6674009 : Nat.Prime 6674009 := by
  apply nodeValid_prime [2, 11, 149, 509] ⟨6674009, 3, [(2, 3), (11, 1), (149, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_149
    · exact prime_509
  · decide +kernel

theorem prime_7386373 : Nat.Prime 7386373 := by
  apply nodeValid_prime [2, 3, 7, 29311] ⟨7386373, 2, [(2, 2), (3, 2), (7, 1), (29311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29311
  · decide +kernel

theorem prime_8045173 : Nat.Prime 8045173 := by
  apply nodeValid_prime [2, 3, 199, 1123] ⟨8045173, 2, [(2, 2), (3, 2), (199, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_1123
  · decide +kernel

theorem prime_11633261 : Nat.Prime 11633261 := by
  apply nodeValid_prime [2, 5, 581663] ⟨11633261, 2, [(2, 2), (5, 1), (581663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_581663
  · decide +kernel

theorem prime_13073549 : Nat.Prime 13073549 := by
  apply nodeValid_prime [2, 29, 43, 2621] ⟨13073549, 2, [(2, 2), (29, 1), (43, 1), (2621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_43
    · exact prime_2621
  · decide +kernel

theorem prime_13776733 : Nat.Prime 13776733 := by
  apply nodeValid_prime [2, 3, 17, 22511] ⟨13776733, 5, [(2, 2), (3, 2), (17, 1), (22511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_22511
  · decide +kernel

theorem prime_15439637 : Nat.Prime 15439637 := by
  apply nodeValid_prime [2, 1613, 2393] ⟨15439637, 2, [(2, 2), (1613, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1613
    · exact prime_2393
  · decide +kernel

theorem prime_15522323 : Nat.Prime 15522323 := by
  apply nodeValid_prime [2, 53, 146437] ⟨15522323, 2, [(2, 1), (53, 1), (146437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_146437
  · decide +kernel

theorem prime_16958803 : Nat.Prime 16958803 := by
  apply nodeValid_prime [2, 3, 7, 37, 1559] ⟨16958803, 2, [(2, 1), (3, 1), (7, 2), (37, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_1559
  · decide +kernel

theorem prime_19170673 : Nat.Prime 19170673 := by
  apply nodeValid_prime [2, 3, 399389] ⟨19170673, 5, [(2, 4), (3, 1), (399389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_399389
  · decide +kernel

theorem prime_19695547 : Nat.Prime 19695547 := by
  apply nodeValid_prime [2, 3, 13, 73, 1153] ⟨19695547, 5, [(2, 1), (3, 2), (13, 1), (73, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_1153
  · decide +kernel

theorem prime_24806263 : Nat.Prime 24806263 := by
  apply nodeValid_prime [2, 3, 13, 31, 10259] ⟨24806263, 3, [(2, 1), (3, 1), (13, 1), (31, 1), (10259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_10259
  · decide +kernel

theorem prime_28811359 : Nat.Prime 28811359 := by
  apply nodeValid_prime [2, 3, 1600631] ⟨28811359, 3, [(2, 1), (3, 2), (1600631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1600631
  · decide +kernel

theorem prime_32228513 : Nat.Prime 32228513 := by
  apply nodeValid_prime [2, 29, 34729] ⟨32228513, 3, [(2, 5), (29, 1), (34729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_34729
  · decide +kernel

theorem prime_32500297 : Nat.Prime 32500297 := by
  apply nodeValid_prime [2, 3, 241, 1873] ⟨32500297, 5, [(2, 3), (3, 2), (241, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_1873
  · decide +kernel

theorem prime_33991967 : Nat.Prime 33991967 := by
  apply nodeValid_prime [2, 149, 114067] ⟨33991967, 5, [(2, 1), (149, 1), (114067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_114067
  · decide +kernel

theorem prime_36311183 : Nat.Prime 36311183 := by
  apply nodeValid_prime [2, 977, 18583] ⟨36311183, 5, [(2, 1), (977, 1), (18583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_977
    · exact prime_18583
  · decide +kernel

theorem prime_42196393 : Nat.Prime 42196393 := by
  apply nodeValid_prime [2, 3, 7, 29, 2887] ⟨42196393, 22, [(2, 3), (3, 2), (7, 1), (29, 1), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_2887
  · decide +kernel

theorem prime_46281007 : Nat.Prime 46281007 := by
  apply nodeValid_prime [2, 3, 37, 69491] ⟨46281007, 3, [(2, 1), (3, 2), (37, 1), (69491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_69491
  · decide +kernel

theorem prime_59480797 : Nat.Prime 59480797 := by
  apply nodeValid_prime [2, 3, 4956733] ⟨59480797, 2, [(2, 2), (3, 1), (4956733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4956733
  · decide +kernel

theorem prime_59913331 : Nat.Prime 59913331 := by
  apply nodeValid_prime [2, 3, 5, 1997111] ⟨59913331, 2, [(2, 1), (3, 1), (5, 1), (1997111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1997111
  · decide +kernel

theorem prime_63208273 : Nat.Prime 63208273 := by
  apply nodeValid_prime [2, 3, 193, 6823] ⟨63208273, 5, [(2, 4), (3, 1), (193, 1), (6823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_6823
  · decide +kernel

theorem prime_64457027 : Nat.Prime 64457027 := by
  apply nodeValid_prime [2, 32228513] ⟨64457027, 2, [(2, 1), (32228513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32228513
  · decide +kernel

theorem prime_71677387 : Nat.Prime 71677387 := by
  apply nodeValid_prime [2, 3, 11, 19, 29, 73] ⟨71677387, 2, [(2, 1), (3, 4), (11, 1), (19, 1), (29, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_29
    · exact prime_73
  · decide +kernel

theorem prime_87495937 : Nat.Prime 87495937 := by
  apply nodeValid_prime [2, 3, 11, 10357] ⟨87495937, 15, [(2, 8), (3, 1), (11, 1), (10357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_10357
  · decide +kernel

theorem prime_97463347 : Nat.Prime 97463347 := by
  apply nodeValid_prime [2, 3, 17, 947, 1009] ⟨97463347, 3, [(2, 1), (3, 1), (17, 1), (947, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_947
    · exact prime_1009
  · decide +kernel

theorem prime_99225053 : Nat.Prime 99225053 := by
  apply nodeValid_prime [2, 24806263] ⟨99225053, 2, [(2, 2), (24806263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24806263
  · decide +kernel

theorem prime_117619109 : Nat.Prime 117619109 := by
  apply nodeValid_prime [2, 107, 274811] ⟨117619109, 2, [(2, 2), (107, 1), (274811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_274811
  · decide +kernel

theorem prime_123085583 : Nat.Prime 123085583 := by
  apply nodeValid_prime [2, 4139, 14869] ⟨123085583, 5, [(2, 1), (4139, 1), (14869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4139
    · exact prime_14869
  · decide +kernel

theorem prime_156969893 : Nat.Prime 156969893 := by
  apply nodeValid_prime [2, 1867, 21019] ⟨156969893, 2, [(2, 2), (1867, 1), (21019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1867
    · exact prime_21019
  · decide +kernel

theorem prime_173900707 : Nat.Prime 173900707 := by
  apply nodeValid_prime [2, 3, 7, 591499] ⟨173900707, 2, [(2, 1), (3, 1), (7, 2), (591499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_591499
  · decide +kernel

theorem prime_215854181 : Nat.Prime 215854181 := by
  apply nodeValid_prime [2, 5, 167, 64627] ⟨215854181, 3, [(2, 2), (5, 1), (167, 1), (64627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_64627
  · decide +kernel

theorem prime_386457593 : Nat.Prime 386457593 := by
  apply nodeValid_prime [2, 23, 2100313] ⟨386457593, 3, [(2, 3), (23, 1), (2100313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2100313
  · decide +kernel

theorem prime_430124719 : Nat.Prime 430124719 := by
  apply nodeValid_prime [2, 3, 17, 89, 47381] ⟨430124719, 6, [(2, 1), (3, 1), (17, 1), (89, 1), (47381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_89
    · exact prime_47381
  · decide +kernel

theorem prime_612646247 : Nat.Prime 612646247 := by
  apply nodeValid_prime [2, 317, 966319] ⟨612646247, 5, [(2, 1), (317, 1), (966319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_966319
  · decide +kernel

theorem prime_1146838193 : Nat.Prime 1146838193 := by
  apply nodeValid_prime [2, 71677387] ⟨1146838193, 3, [(2, 4), (71677387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71677387
  · decide +kernel

theorem prime_1295125087 : Nat.Prime 1295125087 := by
  apply nodeValid_prime [2, 3, 215854181] ⟨1295125087, 3, [(2, 1), (3, 1), (215854181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_215854181
  · decide +kernel

theorem prime_1365369647 : Nat.Prime 1365369647 := by
  apply nodeValid_prime [2, 47, 199, 1553] ⟨1365369647, 5, [(2, 1), (47, 2), (199, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_199
    · exact prime_1553
  · decide +kernel

theorem prime_1667480797 : Nat.Prime 1667480797 := by
  apply nodeValid_prime [2, 3, 15439637] ⟨1667480797, 2, [(2, 2), (3, 3), (15439637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15439637
  · decide +kernel

theorem prime_1721895629 : Nat.Prime 1721895629 := by
  apply nodeValid_prime [2, 15661, 27487] ⟨1721895629, 2, [(2, 2), (15661, 1), (27487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15661
    · exact prime_27487
  · decide +kernel

theorem prime_1757941853 : Nat.Prime 1757941853 := by
  apply nodeValid_prime [2, 1093, 402091] ⟨1757941853, 2, [(2, 2), (1093, 1), (402091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1093
    · exact prime_402091
  · decide +kernel

theorem prime_2560511753 : Nat.Prime 2560511753 := by
  apply nodeValid_prime [2, 15427, 20747] ⟨2560511753, 3, [(2, 3), (15427, 1), (20747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15427
    · exact prime_20747
  · decide +kernel

theorem prime_2654747467 : Nat.Prime 2654747467 := by
  apply nodeValid_prime [2, 3, 7, 63208273] ⟨2654747467, 7, [(2, 1), (3, 1), (7, 1), (63208273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_63208273
  · decide +kernel

theorem prime_2885656019 : Nat.Prime 2885656019 := by
  apply nodeValid_prime [2, 7, 31, 6648977] ⟨2885656019, 2, [(2, 1), (7, 1), (31, 1), (6648977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_6648977
  · decide +kernel

theorem prime_3119471021 : Nat.Prime 3119471021 := by
  apply nodeValid_prime [2, 5, 239, 652609] ⟨3119471021, 3, [(2, 2), (5, 1), (239, 1), (652609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_652609
  · decide +kernel

theorem prime_3443791259 : Nat.Prime 3443791259 := by
  apply nodeValid_prime [2, 1721895629] ⟨3443791259, 2, [(2, 1), (1721895629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1721895629
  · decide +kernel

theorem prime_3517356533 : Nat.Prime 3517356533 := by
  apply nodeValid_prime [2, 19, 46281007] ⟨3517356533, 2, [(2, 2), (19, 1), (46281007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_46281007
  · decide +kernel

theorem prime_3697586413 : Nat.Prime 3697586413 := by
  apply nodeValid_prime [2, 3, 13, 167, 141931] ⟨3697586413, 20, [(2, 2), (3, 1), (13, 1), (167, 1), (141931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_167
    · exact prime_141931
  · decide +kernel

theorem prime_3752594009 : Nat.Prime 3752594009 := by
  apply nodeValid_prime [2, 17, 83, 332441] ⟨3752594009, 3, [(2, 3), (17, 1), (83, 1), (332441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_83
    · exact prime_332441
  · decide +kernel

theorem prime_7265605489 : Nat.Prime 7265605489 := by
  apply nodeValid_prime [2, 3, 53, 101, 28277] ⟨7265605489, 17, [(2, 4), (3, 1), (53, 1), (101, 1), (28277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_101
    · exact prime_28277
  · decide +kernel

theorem prime_14768657777 : Nat.Prime 14768657777 := by
  apply nodeValid_prime [2, 67, 13776733] ⟨14768657777, 3, [(2, 4), (67, 1), (13776733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_13776733
  · decide +kernel

theorem prime_14790345653 : Nat.Prime 14790345653 := by
  apply nodeValid_prime [2, 3697586413] ⟨14790345653, 2, [(2, 2), (3697586413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3697586413
  · decide +kernel

theorem prime_15479108269 : Nat.Prime 15479108269 := by
  apply nodeValid_prime [2, 3, 13, 99225053] ⟨15479108269, 2, [(2, 2), (3, 1), (13, 1), (99225053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_99225053
  · decide +kernel

theorem prime_15661333169 : Nat.Prime 15661333169 := by
  apply nodeValid_prime [2, 13, 127, 592873] ⟨15661333169, 3, [(2, 4), (13, 1), (127, 1), (592873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_127
    · exact prime_592873
  · decide +kernel

theorem prime_24023683063 : Nat.Prime 24023683063 := by
  apply nodeValid_prime [2, 3, 257, 5193187] ⟨24023683063, 3, [(2, 1), (3, 2), (257, 1), (5193187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_5193187
  · decide +kernel

theorem prime_35499610823 : Nat.Prime 35499610823 := by
  apply nodeValid_prime [2, 13, 1365369647] ⟨35499610823, 5, [(2, 1), (13, 1), (1365369647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1365369647
  · decide +kernel

theorem prime_43017771659 : Nat.Prime 43017771659 := by
  apply nodeValid_prime [2, 359, 59913331] ⟨43017771659, 2, [(2, 1), (359, 1), (59913331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_59913331
  · decide +kernel

theorem prime_44218834307 : Nat.Prime 44218834307 := by
  apply nodeValid_prime [2, 5657, 3908329] ⟨44218834307, 2, [(2, 1), (5657, 1), (3908329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5657
    · exact prime_3908329
  · decide +kernel

theorem prime_60951005671 : Nat.Prime 60951005671 := by
  apply nodeValid_prime [2, 3, 5, 1223, 1661243] ⟨60951005671, 12, [(2, 1), (3, 1), (5, 1), (1223, 1), (1661243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1223
    · exact prime_1661243
  · decide +kernel

theorem prime_61916433077 : Nat.Prime 61916433077 := by
  apply nodeValid_prime [2, 15479108269] ⟨61916433077, 2, [(2, 2), (15479108269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15479108269
  · decide +kernel

theorem prime_99823072673 : Nat.Prime 99823072673 := by
  apply nodeValid_prime [2, 3119471021] ⟨99823072673, 3, [(2, 5), (3119471021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3119471021
  · decide +kernel

theorem prime_100305721903 : Nat.Prime 100305721903 := by
  apply nodeValid_prime [2, 3, 41, 557, 732041] ⟨100305721903, 3, [(2, 1), (3, 1), (41, 1), (557, 1), (732041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_557
    · exact prime_732041
  · decide +kernel

theorem prime_121031106029 : Nat.Prime 121031106029 := by
  apply nodeValid_prime [2, 7, 19, 32500297] ⟨121031106029, 12, [(2, 2), (7, 2), (19, 1), (32500297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_32500297
  · decide +kernel

theorem prime_121197552799 : Nat.Prime 121197552799 := by
  apply nodeValid_prime [2, 3, 7, 2885656019] ⟨121197552799, 7, [(2, 1), (3, 1), (7, 1), (2885656019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2885656019
  · decide +kernel

theorem prime_200611440431 : Nat.Prime 200611440431 := by
  apply nodeValid_prime [2, 5, 12689, 1580987] ⟨200611440431, 29, [(2, 1), (5, 1), (12689, 1), (1580987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12689
    · exact prime_1580987
  · decide +kernel

theorem prime_239410203317 : Nat.Prime 239410203317 := by
  apply nodeValid_prime [2, 22073, 2711573] ⟨239410203317, 2, [(2, 2), (22073, 1), (2711573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_22073
    · exact prime_2711573
  · decide +kernel

theorem prime_400670645539 : Nat.Prime 400670645539 := by
  apply nodeValid_prime [2, 3, 109, 612646247] ⟨400670645539, 2, [(2, 1), (3, 1), (109, 1), (612646247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_612646247
  · decide +kernel

theorem prime_603493382119 : Nat.Prime 603493382119 := by
  apply nodeValid_prime [2, 3, 11, 269, 33991967] ⟨603493382119, 3, [(2, 1), (3, 1), (11, 1), (269, 1), (33991967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_269
    · exact prime_33991967
  · decide +kernel

theorem prime_716250866719 : Nat.Prime 716250866719 := by
  apply nodeValid_prime [2, 3, 25867, 4614959] ⟨716250866719, 6, [(2, 1), (3, 1), (25867, 1), (4614959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25867
    · exact prime_4614959
  · decide +kernel

theorem prime_718726131103 : Nat.Prime 718726131103 := by
  apply nodeValid_prime [2, 3, 7, 1471, 11633261] ⟨718726131103, 5, [(2, 1), (3, 1), (7, 1), (1471, 1), (11633261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1471
    · exact prime_11633261
  · decide +kernel

theorem prime_1809234986719 : Nat.Prime 1809234986719 := by
  apply nodeValid_prime [2, 3, 17, 113, 156969893] ⟨1809234986719, 3, [(2, 1), (3, 1), (17, 1), (113, 1), (156969893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_113
    · exact prime_156969893
  · decide +kernel

theorem prime_1814219125669 : Nat.Prime 1814219125669 := by
  apply nodeValid_prime [2, 3, 211097, 238729] ⟨1814219125669, 2, [(2, 2), (3, 2), (211097, 1), (238729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211097
    · exact prime_238729
  · decide +kernel

theorem prime_3628438214273 : Nat.Prime 3628438214273 := by
  apply nodeValid_prime [2, 17, 1667480797] ⟨3628438214273, 3, [(2, 7), (17, 1), (1667480797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1667480797
  · decide +kernel

theorem prime_7157565078973 : Nat.Prime 7157565078973 := by
  apply nodeValid_prime [2, 3, 7, 11, 29221, 265093] ⟨7157565078973, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (29221, 1), (265093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29221
    · exact prime_265093
  · decide +kernel

theorem prime_7157565153257 : Nat.Prime 7157565153257 := by
  apply nodeValid_prime [2, 7, 15887, 8045173] ⟨7157565153257, 3, [(2, 3), (7, 1), (15887, 1), (8045173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15887
    · exact prime_8045173
  · decide +kernel

theorem prime_7157565153461 : Nat.Prime 7157565153461 := by
  apply nodeValid_prime [2, 5, 103, 12503, 277897] ⟨7157565153461, 2, [(2, 2), (5, 1), (103, 1), (12503, 1), (277897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_12503
    · exact prime_277897
  · decide +kernel

theorem prime_7162508665211 : Nat.Prime 7162508665211 := by
  apply nodeValid_prime [2, 5, 17, 12853, 3278021] ⟨7162508665211, 2, [(2, 1), (5, 1), (17, 1), (12853, 1), (3278021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_12853
    · exact prime_3278021
  · decide +kernel

theorem prime_7162508665967 : Nat.Prime 7162508665967 := by
  apply nodeValid_prime [2, 19, 71, 2654747467] ⟨7162508665967, 7, [(2, 1), (19, 1), (71, 1), (2654747467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71
    · exact prime_2654747467
  · decide +kernel

theorem prime_7162508667191 : Nat.Prime 7162508667191 := by
  apply nodeValid_prime [2, 5, 716250866719] ⟨7162508667191, 11, [(2, 1), (5, 1), (716250866719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_716250866719
  · decide +kernel

theorem prime_7167454538381 : Nat.Prime 7167454538381 := by
  apply nodeValid_prime [2, 5, 3677, 97463347] ⟨7167454538381, 2, [(2, 2), (5, 1), (3677, 1), (97463347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3677
    · exact prime_97463347
  · decide +kernel

theorem prime_7167454538549 : Nat.Prime 7167454538549 := by
  apply nodeValid_prime [2, 151, 619, 19170673] ⟨7167454538549, 2, [(2, 2), (151, 1), (619, 1), (19170673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_619
    · exact prime_19170673
  · decide +kernel

theorem prime_7167454557191 : Nat.Prime 7167454557191 := by
  apply nodeValid_prime [2, 5, 191, 3752594009] ⟨7167454557191, 11, [(2, 1), (5, 1), (191, 1), (3752594009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
    · exact prime_3752594009
  · decide +kernel

theorem prime_7172402731807 : Nat.Prime 7172402731807 := by
  apply nodeValid_prime [2, 3, 13, 71, 1295125087] ⟨7172402731807, 6, [(2, 1), (3, 1), (13, 1), (71, 1), (1295125087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_1295125087
  · decide +kernel

theorem prime_7172402733259 : Nat.Prime 7172402733259 := by
  apply nodeValid_prime [2, 3, 7, 4703, 36311183] ⟨7172402733259, 3, [(2, 1), (3, 1), (7, 1), (4703, 1), (36311183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4703
    · exact prime_36311183
  · decide +kernel

theorem prime_7172402760241 : Nat.Prime 7172402760241 := by
  apply nodeValid_prime [2, 3, 5, 17, 1757941853] ⟨7172402760241, 14, [(2, 4), (3, 1), (5, 1), (17, 1), (1757941853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1757941853
  · decide +kernel

theorem prime_7177353269399 : Nat.Prime 7177353269399 := by
  apply nodeValid_prime [2, 13, 2347, 117619109] ⟨7177353269399, 11, [(2, 1), (13, 1), (2347, 1), (117619109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2347
    · exact prime_117619109
  · decide +kernel

theorem prime_7177353270943 : Nat.Prime 7177353270943 := by
  apply nodeValid_prime [2, 3, 28349, 42196393] ⟨7177353270943, 3, [(2, 1), (3, 1), (28349, 1), (42196393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28349
    · exact prime_42196393
  · decide +kernel

theorem prime_7177353275461 : Nat.Prime 7177353275461 := by
  apply nodeValid_prime [2, 3, 5, 24469, 4888739] ⟨7177353275461, 6, [(2, 2), (3, 1), (5, 1), (24469, 1), (4888739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_24469
    · exact prime_4888739
  · decide +kernel

theorem prime_7182306099511 : Nat.Prime 7182306099511 := by
  apply nodeValid_prime [2, 3, 5, 239410203317] ⟨7182306099511, 3, [(2, 1), (3, 1), (5, 1), (239410203317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239410203317
  · decide +kernel

theorem prime_7182306236933 : Nat.Prime 7182306236933 := by
  apply nodeValid_prime [2, 29, 61916433077] ⟨7182306236933, 2, [(2, 2), (29, 1), (61916433077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_61916433077
  · decide +kernel

theorem prime_7182306237751 : Nat.Prime 7182306237751 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 59480797] ⟨7182306237751, 3, [(2, 1), (3, 1), (5, 3), (7, 1), (23, 1), (59480797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_59480797
  · decide +kernel

theorem prime_7187261232457 : Nat.Prime 7187261232457 := by
  apply nodeValid_prime [2, 3, 99823072673] ⟨7187261232457, 5, [(2, 3), (3, 2), (99823072673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_99823072673
  · decide +kernel

theorem prime_7187261310167 : Nat.Prime 7187261310167 := by
  apply nodeValid_prime [2, 7, 523, 16339, 60077] ⟨7187261310167, 5, [(2, 1), (7, 1), (523, 1), (16339, 1), (60077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_523
    · exact prime_16339
    · exact prime_60077
  · decide +kernel

theorem prime_7187261311031 : Nat.Prime 7187261311031 := by
  apply nodeValid_prime [2, 5, 718726131103] ⟨7187261311031, 7, [(2, 1), (5, 1), (718726131103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_718726131103
  · decide +kernel

theorem prime_7192218669101 : Nat.Prime 7192218669101 := by
  apply nodeValid_prime [2, 5, 67, 10247, 104759] ⟨7192218669101, 3, [(2, 2), (5, 2), (67, 1), (10247, 1), (104759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_10247
    · exact prime_104759
  · decide +kernel

theorem prime_7192218669179 : Nat.Prime 7192218669179 := by
  apply nodeValid_prime [2, 59, 60951005671] ⟨7192218669179, 2, [(2, 1), (59, 1), (60951005671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_60951005671
  · decide +kernel

theorem prime_7192218675613 : Nat.Prime 7192218675613 := by
  apply nodeValid_prime [2, 3, 31, 10267, 1883113] ⟨7192218675613, 2, [(2, 2), (3, 1), (31, 1), (10267, 1), (1883113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_10267
    · exact prime_1883113
  · decide +kernel

theorem prime_7197178430347 : Nat.Prime 7197178430347 := by
  apply nodeValid_prime [2, 3, 673, 21503, 82889] ⟨7197178430347, 3, [(2, 1), (3, 1), (673, 1), (21503, 1), (82889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_673
    · exact prime_21503
    · exact prime_82889
  · decide +kernel

theorem prime_7197178430737 : Nat.Prime 7197178430737 := by
  apply nodeValid_prime [2, 3, 7, 193, 383, 13799] ⟨7197178430737, 5, [(2, 4), (3, 2), (7, 2), (193, 1), (383, 1), (13799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_193
    · exact prime_383
    · exact prime_13799
  · decide +kernel

theorem prime_7197178441979 : Nat.Prime 7197178441979 := by
  apply nodeValid_prime [2, 7, 79, 881, 7386373] ⟨7197178441979, 2, [(2, 1), (7, 1), (79, 1), (881, 1), (7386373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_881
    · exact prime_7386373
  · decide +kernel

theorem prime_7202140524899 : Nat.Prime 7202140524899 := by
  apply nodeValid_prime [2, 11, 17, 53, 349, 1041091] ⟨7202140524899, 10, [(2, 1), (11, 1), (17, 1), (53, 1), (349, 1), (1041091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_53
    · exact prime_349
    · exact prime_1041091
  · decide +kernel

theorem prime_7202140558219 : Nat.Prime 7202140558219 := by
  apply nodeValid_prime [2, 3, 17, 269, 87495937] ⟨7202140558219, 3, [(2, 1), (3, 2), (17, 1), (269, 1), (87495937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_269
    · exact prime_87495937
  · decide +kernel

theorem prime_7202140559479 : Nat.Prime 7202140559479 := by
  apply nodeValid_prime [2, 3, 149, 173, 15522323] ⟨7202140559479, 6, [(2, 1), (3, 2), (149, 1), (173, 1), (15522323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_173
    · exact prime_15522323
  · decide +kernel

theorem prime_7207104918901 : Nat.Prime 7207104918901 := by
  apply nodeValid_prime [2, 3, 5, 24023683063] ⟨7207104918901, 7, [(2, 2), (3, 1), (5, 2), (24023683063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_24023683063
  · decide +kernel

theorem prime_7207104995177 : Nat.Prime 7207104995177 := by
  apply nodeValid_prime [2, 61, 14768657777] ⟨7207104995177, 3, [(2, 3), (61, 1), (14768657777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_14768657777
  · decide +kernel

theorem prime_7207104995273 : Nat.Prime 7207104995273 := by
  apply nodeValid_prime [2, 7, 13, 31, 2447, 10039] ⟨7207104995273, 3, [(2, 3), (7, 1), (13, 2), (31, 1), (2447, 1), (10039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_2447
    · exact prime_10039
  · decide +kernel

theorem prime_7212071599157 : Nat.Prime 7212071599157 := by
  apply nodeValid_prime [2, 137, 2621, 5021257] ⟨7212071599157, 2, [(2, 2), (137, 1), (2621, 1), (5021257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_2621
    · exact prime_5021257
  · decide +kernel

theorem prime_7212071600567 : Nat.Prime 7212071600567 := by
  apply nodeValid_prime [2, 7, 31, 43, 386457593] ⟨7212071600567, 7, [(2, 1), (7, 1), (31, 1), (43, 1), (386457593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_43
    · exact prime_386457593
  · decide +kernel

theorem prime_7212071619703 : Nat.Prime 7212071619703 := by
  apply nodeValid_prime [2, 3, 400670645539] ⟨7212071619703, 3, [(2, 1), (3, 2), (400670645539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_400670645539
  · decide +kernel

theorem prime_7217040637087 : Nat.Prime 7217040637087 := by
  apply nodeValid_prime [2, 3, 7, 2593, 1352419] ⟨7217040637087, 5, [(2, 1), (3, 1), (7, 3), (2593, 1), (1352419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2593
    · exact prime_1352419
  · decide +kernel

theorem prime_7217040640373 : Nat.Prime 7217040640373 := by
  apply nodeValid_prime [2, 257, 28807, 243707] ⟨7217040640373, 2, [(2, 2), (257, 1), (28807, 1), (243707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_28807
    · exact prime_243707
  · decide +kernel

theorem prime_7222011855517 : Nat.Prime 7222011855517 := by
  apply nodeValid_prime [2, 3, 200611440431] ⟨7222011855517, 5, [(2, 2), (3, 2), (200611440431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_200611440431
  · decide +kernel

theorem prime_7222011856067 : Nat.Prime 7222011856067 := by
  apply nodeValid_prime [2, 7, 71, 7265605489] ⟨7222011856067, 2, [(2, 1), (7, 1), (71, 1), (7265605489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_7265605489
  · decide +kernel

theorem prime_7222011977017 : Nat.Prime 7222011977017 := by
  apply nodeValid_prime [2, 3, 100305721903] ⟨7222011977017, 5, [(2, 3), (3, 2), (100305721903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_100305721903
  · decide +kernel

theorem prime_7226985595183 : Nat.Prime 7226985595183 := by
  apply nodeValid_prime [2, 3, 600631, 2005387] ⟨7226985595183, 3, [(2, 1), (3, 1), (600631, 1), (2005387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_600631
    · exact prime_2005387
  · decide +kernel

theorem prime_7226985638713 : Nat.Prime 7226985638713 := by
  apply nodeValid_prime [2, 3, 7, 43017771659] ⟨7226985638713, 5, [(2, 3), (3, 1), (7, 1), (43017771659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43017771659
  · decide +kernel

theorem prime_7231961626297 : Nat.Prime 7231961626297 := by
  apply nodeValid_prime [2, 3, 11, 30211, 906749] ⟨7231961626297, 5, [(2, 3), (3, 1), (11, 1), (30211, 1), (906749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_30211
    · exact prime_906749
  · decide +kernel

theorem prime_7231961643901 : Nat.Prime 7231961643901 := by
  apply nodeValid_prime [2, 3, 5, 7, 3443791259] ⟨7231961643901, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (3443791259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3443791259
  · decide +kernel

theorem prime_7231961645059 : Nat.Prime 7231961645059 := by
  apply nodeValid_prime [2, 3, 1051, 1146838193] ⟨7231961645059, 10, [(2, 1), (3, 1), (1051, 1), (1146838193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1051
    · exact prime_1146838193
  · decide +kernel

theorem prime_7236939937571 : Nat.Prime 7236939937571 := by
  apply nodeValid_prime [2, 5, 7, 62003, 1667417] ⟨7236939937571, 6, [(2, 1), (5, 1), (7, 1), (62003, 1), (1667417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_62003
    · exact prime_1667417
  · decide +kernel

theorem prime_7236939938069 : Nat.Prime 7236939938069 := by
  apply nodeValid_prime [2, 14699, 123085583] ⟨7236939938069, 2, [(2, 2), (14699, 1), (123085583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_14699
    · exact prime_123085583
  · decide +kernel

theorem prime_7236939946877 : Nat.Prime 7236939946877 := by
  apply nodeValid_prime [2, 1809234986719] ⟨7236939946877, 2, [(2, 2), (1809234986719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1809234986719
  · decide +kernel

theorem prime_7241920585429 : Nat.Prime 7241920585429 := by
  apply nodeValid_prime [2, 3, 603493382119] ⟨7241920585429, 6, [(2, 2), (3, 1), (603493382119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_603493382119
  · decide +kernel

theorem prime_7241920605571 : Nat.Prime 7241920605571 := by
  apply nodeValid_prime [2, 3, 5, 7, 114761, 300497] ⟨7241920605571, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (114761, 1), (300497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_114761
    · exact prime_300497
  · decide +kernel

theorem prime_7241920607893 : Nat.Prime 7241920607893 := by
  apply nodeValid_prime [2, 3, 17, 35499610823] ⟨7241920607893, 2, [(2, 2), (3, 1), (17, 1), (35499610823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_35499610823
  · decide +kernel

theorem prime_7246903533173 : Nat.Prime 7246903533173 := by
  apply nodeValid_prime [2, 47, 2273, 16958803] ⟨7246903533173, 2, [(2, 2), (47, 1), (2273, 1), (16958803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_2273
    · exact prime_16958803
  · decide +kernel

theorem prime_7246903534583 : Nat.Prime 7246903534583 := by
  apply nodeValid_prime [2, 47, 5897, 13073549] ⟨7246903534583, 5, [(2, 1), (47, 1), (5897, 1), (13073549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_5897
    · exact prime_13073549
  · decide +kernel

theorem prime_7246903545611 : Nat.Prime 7246903545611 := by
  apply nodeValid_prime [2, 5, 11243, 64457027] ⟨7246903545611, 2, [(2, 1), (5, 1), (11243, 1), (64457027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11243
    · exact prime_64457027
  · decide +kernel

theorem prime_7251888825983 : Nat.Prime 7251888825983 := by
  apply nodeValid_prime [2, 17, 197, 223, 4855133] ⟨7251888825983, 5, [(2, 1), (17, 1), (197, 1), (223, 1), (4855133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_197
    · exact prime_223
    · exact prime_4855133
  · decide +kernel

theorem prime_7251888826349 : Nat.Prime 7251888826349 := by
  apply nodeValid_prime [2, 41, 44218834307] ⟨7251888826349, 2, [(2, 2), (41, 1), (44218834307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_44218834307
  · decide +kernel

theorem prime_7251888828131 : Nat.Prime 7251888828131 := by
  apply nodeValid_prime [2, 5, 163, 1471, 3024481] ⟨7251888828131, 2, [(2, 1), (5, 1), (163, 1), (1471, 1), (3024481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_1471
    · exact prime_3024481
  · decide +kernel

theorem prime_7256876428547 : Nat.Prime 7256876428547 := by
  apply nodeValid_prime [2, 3628438214273] ⟨7256876428547, 2, [(2, 1), (3628438214273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3628438214273
  · decide +kernel

theorem prime_7256876502677 : Nat.Prime 7256876502677 := by
  apply nodeValid_prime [2, 1814219125669] ⟨7256876502677, 2, [(2, 2), (1814219125669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1814219125669
  · decide +kernel

theorem prime_7256876503111 : Nat.Prime 7256876503111 := by
  apply nodeValid_prime [2, 3, 5, 13, 107, 173900707] ⟨7256876503111, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (107, 1), (173900707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_107
    · exact prime_173900707
  · decide +kernel

theorem prime_7261866352183 : Nat.Prime 7261866352183 := by
  apply nodeValid_prime [2, 3, 13, 29, 163, 19695547] ⟨7261866352183, 3, [(2, 1), (3, 1), (13, 1), (29, 1), (163, 1), (19695547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_163
    · exact prime_19695547
  · decide +kernel

theorem prime_7261866361643 : Nat.Prime 7261866361643 := by
  apply nodeValid_prime [2, 19, 1307, 7013, 20849] ⟨7261866361643, 2, [(2, 1), (19, 1), (1307, 1), (7013, 1), (20849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1307
    · exact prime_7013
    · exact prime_20849
  · decide +kernel

theorem prime_7261866361741 : Nat.Prime 7261866361741 := by
  apply nodeValid_prime [2, 3, 5, 121031106029] ⟨7261866361741, 6, [(2, 2), (3, 1), (5, 1), (121031106029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_121031106029
  · decide +kernel

theorem prime_7266858589699 : Nat.Prime 7266858589699 := by
  apply nodeValid_prime [2, 3, 127, 331, 28811359] ⟨7266858589699, 3, [(2, 1), (3, 1), (127, 1), (331, 1), (28811359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_331
    · exact prime_28811359
  · decide +kernel

theorem prime_7266858590417 : Nat.Prime 7266858590417 := by
  apply nodeValid_prime [2, 29, 15661333169] ⟨7266858590417, 3, [(2, 4), (29, 1), (15661333169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_15661333169
  · decide +kernel

theorem prime_7266858597179 : Nat.Prime 7266858597179 := by
  apply nodeValid_prime [2, 1033, 3517356533] ⟨7266858597179, 2, [(2, 1), (1033, 1), (3517356533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1033
    · exact prime_3517356533
  · decide +kernel

theorem prime_7271853167941 : Nat.Prime 7271853167941 := by
  apply nodeValid_prime [2, 3, 5, 121197552799] ⟨7271853167941, 7, [(2, 2), (3, 1), (5, 1), (121197552799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_121197552799
  · decide +kernel

theorem prime_7271853378203 : Nat.Prime 7271853378203 := by
  apply nodeValid_prime [2, 7, 223, 349, 6674009] ⟨7271853378203, 2, [(2, 1), (7, 1), (223, 1), (349, 1), (6674009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_223
    · exact prime_349
    · exact prime_6674009
  · decide +kernel

theorem prime_7271853378521 : Nat.Prime 7271853378521 := by
  apply nodeValid_prime [2, 5, 71, 2560511753] ⟨7271853378521, 3, [(2, 3), (5, 1), (71, 1), (2560511753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_2560511753
  · decide +kernel

theorem prime_7276849996043 : Nat.Prime 7276849996043 := by
  apply nodeValid_prime [2, 11, 769, 430124719] ⟨7276849996043, 2, [(2, 1), (11, 1), (769, 1), (430124719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_769
    · exact prime_430124719
  · decide +kernel

theorem prime_7276849996679 : Nat.Prime 7276849996679 := by
  apply nodeValid_prime [2, 47, 773, 1451, 69019] ⟨7276849996679, 7, [(2, 1), (47, 1), (773, 1), (1451, 1), (69019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_773
    · exact prime_1451
    · exact prime_69019
  · decide +kernel

theorem prime_7276850061277 : Nat.Prime 7276850061277 := by
  apply nodeValid_prime [2, 3, 41, 14790345653] ⟨7276850061277, 2, [(2, 2), (3, 1), (41, 1), (14790345653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_14790345653
  · decide +kernel

end Sude.Lucas.Generated
