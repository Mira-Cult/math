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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0117

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7793 : Nat.Prime 7793 := by
  apply nodeValid_prime [2, 487] ⟨7793, 3, [(2, 4), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_487
  · decide +kernel

theorem prime_9103 : Nat.Prime 9103 := by
  apply nodeValid_prime [2, 3, 37, 41] ⟨9103, 6, [(2, 1), (3, 1), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_17519 : Nat.Prime 17519 := by
  apply nodeValid_prime [2, 19, 461] ⟨17519, 13, [(2, 1), (19, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_461
  · decide +kernel

theorem prime_20023 : Nat.Prime 20023 := by
  apply nodeValid_prime [2, 3, 47, 71] ⟨20023, 3, [(2, 1), (3, 1), (47, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_71
  · decide +kernel

theorem prime_20071 : Nat.Prime 20071 := by
  apply nodeValid_prime [2, 3, 5, 223] ⟨20071, 3, [(2, 1), (3, 2), (5, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
  · decide +kernel

theorem prime_21277 : Nat.Prime 21277 := by
  apply nodeValid_prime [2, 3, 197] ⟨21277, 6, [(2, 2), (3, 3), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
  · decide +kernel

theorem prime_23131 : Nat.Prime 23131 := by
  apply nodeValid_prime [2, 3, 5, 257] ⟨23131, 3, [(2, 1), (3, 2), (5, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
  · decide +kernel

theorem prime_27127 : Nat.Prime 27127 := by
  apply nodeValid_prime [2, 3, 11, 137] ⟨27127, 3, [(2, 1), (3, 2), (11, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_137
  · decide +kernel

theorem prime_28643 : Nat.Prime 28643 := by
  apply nodeValid_prime [2, 14321] ⟨28643, 2, [(2, 1), (14321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14321
  · decide +kernel

theorem prime_32377 : Nat.Prime 32377 := by
  apply nodeValid_prime [2, 3, 19, 71] ⟨32377, 5, [(2, 3), (3, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_34877 : Nat.Prime 34877 := by
  apply nodeValid_prime [2, 8719] ⟨34877, 2, [(2, 2), (8719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8719
  · decide +kernel

theorem prime_35591 : Nat.Prime 35591 := by
  apply nodeValid_prime [2, 5, 3559] ⟨35591, 17, [(2, 1), (5, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3559
  · decide +kernel

theorem prime_38149 : Nat.Prime 38149 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨38149, 6, [(2, 2), (3, 1), (11, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_38453 : Nat.Prime 38453 := by
  apply nodeValid_prime [2, 9613] ⟨38453, 2, [(2, 2), (9613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9613
  · decide +kernel

theorem prime_41233 : Nat.Prime 41233 := by
  apply nodeValid_prime [2, 3, 859] ⟨41233, 5, [(2, 4), (3, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_859
  · decide +kernel

theorem prime_46679 : Nat.Prime 46679 := by
  apply nodeValid_prime [2, 23339] ⟨46679, 17, [(2, 1), (23339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23339
  · decide +kernel

theorem prime_49211 : Nat.Prime 49211 := by
  apply nodeValid_prime [2, 5, 7, 19, 37] ⟨49211, 2, [(2, 1), (5, 1), (7, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_50387 : Nat.Prime 50387 := by
  apply nodeValid_prime [2, 7, 59, 61] ⟨50387, 2, [(2, 1), (7, 1), (59, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_61
  · decide +kernel

theorem prime_55217 : Nat.Prime 55217 := by
  apply nodeValid_prime [2, 7, 17, 29] ⟨55217, 3, [(2, 4), (7, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_63799 : Nat.Prime 63799 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨63799, 6, [(2, 1), (3, 1), (7, 3), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_85121 : Nat.Prime 85121 := by
  apply nodeValid_prime [2, 5, 7, 19] ⟨85121, 6, [(2, 7), (5, 1), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_86083 : Nat.Prime 86083 := by
  apply nodeValid_prime [2, 3, 14347] ⟨86083, 2, [(2, 1), (3, 1), (14347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14347
  · decide +kernel

theorem prime_90469 : Nat.Prime 90469 := by
  apply nodeValid_prime [2, 3, 7, 359] ⟨90469, 2, [(2, 2), (3, 2), (7, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_359
  · decide +kernel

theorem prime_101113 : Nat.Prime 101113 := by
  apply nodeValid_prime [2, 3, 11, 383] ⟨101113, 5, [(2, 3), (3, 1), (11, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_383
  · decide +kernel

theorem prime_108637 : Nat.Prime 108637 := by
  apply nodeValid_prime [2, 3, 11, 823] ⟨108637, 15, [(2, 2), (3, 1), (11, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_823
  · decide +kernel

theorem prime_136651 : Nat.Prime 136651 := by
  apply nodeValid_prime [2, 3, 5, 911] ⟨136651, 3, [(2, 1), (3, 1), (5, 2), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_911
  · decide +kernel

theorem prime_148139 : Nat.Prime 148139 := by
  apply nodeValid_prime [2, 17, 4357] ⟨148139, 2, [(2, 1), (17, 1), (4357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4357
  · decide +kernel

theorem prime_150517 : Nat.Prime 150517 := by
  apply nodeValid_prime [2, 3, 37, 113] ⟨150517, 2, [(2, 2), (3, 2), (37, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_113
  · decide +kernel

theorem prime_153533 : Nat.Prime 153533 := by
  apply nodeValid_prime [2, 131, 293] ⟨153533, 2, [(2, 2), (131, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_293
  · decide +kernel

theorem prime_155861 : Nat.Prime 155861 := by
  apply nodeValid_prime [2, 5, 7793] ⟨155861, 7, [(2, 2), (5, 1), (7793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7793
  · decide +kernel

theorem prime_156703 : Nat.Prime 156703 := by
  apply nodeValid_prime [2, 3, 7, 13, 41] ⟨156703, 3, [(2, 1), (3, 1), (7, 2), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_160687 : Nat.Prime 160687 := by
  apply nodeValid_prime [2, 3, 79, 113] ⟨160687, 6, [(2, 1), (3, 2), (79, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_113
  · decide +kernel

theorem prime_170243 : Nat.Prime 170243 := by
  apply nodeValid_prime [2, 85121] ⟨170243, 2, [(2, 1), (85121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_85121
  · decide +kernel

theorem prime_190763 : Nat.Prime 190763 := by
  apply nodeValid_prime [2, 11, 13, 23, 29] ⟨190763, 11, [(2, 1), (11, 1), (13, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_197921 : Nat.Prime 197921 := by
  apply nodeValid_prime [2, 5, 1237] ⟨197921, 3, [(2, 5), (5, 1), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1237
  · decide +kernel

theorem prime_203669 : Nat.Prime 203669 := by
  apply nodeValid_prime [2, 59, 863] ⟨203669, 2, [(2, 2), (59, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_863
  · decide +kernel

theorem prime_206233 : Nat.Prime 206233 := by
  apply nodeValid_prime [2, 3, 13, 661] ⟨206233, 7, [(2, 3), (3, 1), (13, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_661
  · decide +kernel

theorem prime_206821 : Nat.Prime 206821 := by
  apply nodeValid_prime [2, 3, 5, 383] ⟨206821, 2, [(2, 2), (3, 3), (5, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
  · decide +kernel

theorem prime_209263 : Nat.Prime 209263 := by
  apply nodeValid_prime [2, 3, 34877] ⟨209263, 13, [(2, 1), (3, 1), (34877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34877
  · decide +kernel

theorem prime_255197 : Nat.Prime 255197 := by
  apply nodeValid_prime [2, 63799] ⟨255197, 2, [(2, 2), (63799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63799
  · decide +kernel

theorem prime_272603 : Nat.Prime 272603 := by
  apply nodeValid_prime [2, 11, 12391] ⟨272603, 2, [(2, 1), (11, 1), (12391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12391
  · decide +kernel

theorem prime_307067 : Nat.Prime 307067 := by
  apply nodeValid_prime [2, 153533] ⟨307067, 2, [(2, 1), (153533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_153533
  · decide +kernel

theorem prime_325021 : Nat.Prime 325021 := by
  apply nodeValid_prime [2, 3, 5, 5417] ⟨325021, 6, [(2, 2), (3, 1), (5, 1), (5417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5417
  · decide +kernel

theorem prime_330431 : Nat.Prime 330431 := by
  apply nodeValid_prime [2, 5, 173, 191] ⟨330431, 23, [(2, 1), (5, 1), (173, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_191
  · decide +kernel

theorem prime_336029 : Nat.Prime 336029 := by
  apply nodeValid_prime [2, 7, 11, 1091] ⟨336029, 3, [(2, 2), (7, 1), (11, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1091
  · decide +kernel

theorem prime_361877 : Nat.Prime 361877 := by
  apply nodeValid_prime [2, 90469] ⟨361877, 2, [(2, 2), (90469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90469
  · decide +kernel

theorem prime_381527 : Nat.Prime 381527 := by
  apply nodeValid_prime [2, 190763] ⟨381527, 5, [(2, 1), (190763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_190763
  · decide +kernel

theorem prime_399067 : Nat.Prime 399067 := by
  apply nodeValid_prime [2, 3, 227, 293] ⟨399067, 5, [(2, 1), (3, 1), (227, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_293
  · decide +kernel

theorem prime_425549 : Nat.Prime 425549 := by
  apply nodeValid_prime [2, 191, 557] ⟨425549, 2, [(2, 2), (191, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_557
  · decide +kernel

theorem prime_468761 : Nat.Prime 468761 := by
  apply nodeValid_prime [2, 5, 11719] ⟨468761, 3, [(2, 3), (5, 1), (11719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11719
  · decide +kernel

theorem prime_488287 : Nat.Prime 488287 := by
  apply nodeValid_prime [2, 3, 27127] ⟨488287, 3, [(2, 1), (3, 2), (27127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27127
  · decide +kernel

theorem prime_507197 : Nat.Prime 507197 := by
  apply nodeValid_prime [2, 23, 37, 149] ⟨507197, 2, [(2, 2), (23, 1), (37, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_149
  · decide +kernel

theorem prime_516499 : Nat.Prime 516499 := by
  apply nodeValid_prime [2, 3, 86083] ⟨516499, 2, [(2, 1), (3, 1), (86083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_86083
  · decide +kernel

theorem prime_570107 : Nat.Prime 570107 := by
  apply nodeValid_prime [2, 61, 4673] ⟨570107, 2, [(2, 1), (61, 1), (4673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_4673
  · decide +kernel

theorem prime_672059 : Nat.Prime 672059 := by
  apply nodeValid_prime [2, 336029] ⟨672059, 2, [(2, 1), (336029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_336029
  · decide +kernel

theorem prime_683909 : Nat.Prime 683909 := by
  apply nodeValid_prime [2, 37, 4621] ⟨683909, 2, [(2, 2), (37, 1), (4621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_4621
  · decide +kernel

theorem prime_824933 : Nat.Prime 824933 := by
  apply nodeValid_prime [2, 206233] ⟨824933, 2, [(2, 2), (206233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_206233
  · decide +kernel

theorem prime_846149 : Nat.Prime 846149 := by
  apply nodeValid_prime [2, 199, 1063] ⟨846149, 2, [(2, 2), (199, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_1063
  · decide +kernel

theorem prime_928607 : Nat.Prime 928607 := by
  apply nodeValid_prime [2, 7, 19, 3491] ⟨928607, 5, [(2, 1), (7, 1), (19, 1), (3491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_3491
  · decide +kernel

theorem prime_962783 : Nat.Prime 962783 := by
  apply nodeValid_prime [2, 641, 751] ⟨962783, 5, [(2, 1), (641, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_751
  · decide +kernel

theorem prime_978743 : Nat.Prime 978743 := by
  apply nodeValid_prime [2, 23, 21277] ⟨978743, 5, [(2, 1), (23, 1), (21277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_21277
  · decide +kernel

theorem prime_1109291 : Nat.Prime 1109291 := by
  apply nodeValid_prime [2, 5, 7, 13, 23, 53] ⟨1109291, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_1367819 : Nat.Prime 1367819 := by
  apply nodeValid_prime [2, 683909] ⟨1367819, 2, [(2, 1), (683909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_683909
  · decide +kernel

theorem prime_1533347 : Nat.Prime 1533347 := by
  apply nodeValid_prime [2, 29, 26437] ⟨1533347, 2, [(2, 1), (29, 1), (26437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_26437
  · decide +kernel

theorem prime_1567031 : Nat.Prime 1567031 := by
  apply nodeValid_prime [2, 5, 156703] ⟨1567031, 7, [(2, 1), (5, 1), (156703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_156703
  · decide +kernel

theorem prime_1588159 : Nat.Prime 1588159 := by
  apply nodeValid_prime [2, 3, 11, 13, 617] ⟨1588159, 3, [(2, 1), (3, 2), (11, 1), (13, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_617
  · decide +kernel

theorem prime_1726289 : Nat.Prime 1726289 := by
  apply nodeValid_prime [2, 23, 4691] ⟨1726289, 3, [(2, 4), (23, 1), (4691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4691
  · decide +kernel

theorem prime_1779311 : Nat.Prime 1779311 := by
  apply nodeValid_prime [2, 5, 13, 13687] ⟨1779311, 7, [(2, 1), (5, 1), (13, 1), (13687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_13687
  · decide +kernel

theorem prime_2083681 : Nat.Prime 2083681 := by
  apply nodeValid_prime [2, 3, 5, 1447] ⟨2083681, 7, [(2, 5), (3, 2), (5, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1447
  · decide +kernel

theorem prime_2333869 : Nat.Prime 2333869 := by
  apply nodeValid_prime [2, 3, 43, 4523] ⟨2333869, 2, [(2, 2), (3, 1), (43, 1), (4523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_4523
  · decide +kernel

theorem prime_2359499 : Nat.Prime 2359499 := by
  apply nodeValid_prime [2, 17, 29, 2393] ⟨2359499, 2, [(2, 1), (17, 1), (29, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_2393
  · decide +kernel

theorem prime_3559417 : Nat.Prime 3559417 := by
  apply nodeValid_prime [2, 3, 7, 21187] ⟨3559417, 19, [(2, 3), (3, 1), (7, 1), (21187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_21187
  · decide +kernel

theorem prime_4294469 : Nat.Prime 4294469 := by
  apply nodeValid_prime [2, 23, 46679] ⟨4294469, 2, [(2, 2), (23, 1), (46679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_46679
  · decide +kernel

theorem prime_5075797 : Nat.Prime 5075797 := by
  apply nodeValid_prime [2, 3, 11, 38453] ⟨5075797, 2, [(2, 2), (3, 1), (11, 1), (38453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_38453
  · decide +kernel

theorem prime_5542429 : Nat.Prime 5542429 := by
  apply nodeValid_prime [2, 3, 31, 47, 317] ⟨5542429, 2, [(2, 2), (3, 1), (31, 1), (47, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_47
    · exact prime_317
  · decide +kernel

theorem prime_5872459 : Nat.Prime 5872459 := by
  apply nodeValid_prime [2, 3, 978743] ⟨5872459, 2, [(2, 1), (3, 1), (978743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_978743
  · decide +kernel

theorem prime_6622283 : Nat.Prime 6622283 := by
  apply nodeValid_prime [2, 17, 31, 61, 103] ⟨6622283, 2, [(2, 1), (17, 1), (31, 1), (61, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_61
    · exact prime_103
  · decide +kernel

theorem prime_7937357 : Nat.Prime 7937357 := by
  apply nodeValid_prime [2, 7, 67, 4231] ⟨7937357, 2, [(2, 2), (7, 1), (67, 1), (4231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_4231
  · decide +kernel

theorem prime_9710411 : Nat.Prime 9710411 := by
  apply nodeValid_prime [2, 5, 307, 3163] ⟨9710411, 6, [(2, 1), (5, 1), (307, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_307
    · exact prime_3163
  · decide +kernel

theorem prime_12172729 : Nat.Prime 12172729 := by
  apply nodeValid_prime [2, 3, 507197] ⟨12172729, 11, [(2, 3), (3, 1), (507197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_507197
  · decide +kernel

theorem prime_13895963 : Nat.Prime 13895963 := by
  apply nodeValid_prime [2, 347, 20023] ⟨13895963, 2, [(2, 1), (347, 1), (20023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_20023
  · decide +kernel

theorem prime_16292609 : Nat.Prime 16292609 := by
  apply nodeValid_prime [2, 31, 2053] ⟨16292609, 3, [(2, 8), (31, 1), (2053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2053
  · decide +kernel

theorem prime_18613891 : Nat.Prime 18613891 := by
  apply nodeValid_prime [2, 3, 5, 206821] ⟨18613891, 2, [(2, 1), (3, 2), (5, 1), (206821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_206821
  · decide +kernel

theorem prime_21913049 : Nat.Prime 21913049 := by
  apply nodeValid_prime [2, 191, 14341] ⟨21913049, 3, [(2, 3), (191, 1), (14341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_14341
  · decide +kernel

theorem prime_22898653 : Nat.Prime 22898653 := by
  apply nodeValid_prime [2, 3, 7, 272603] ⟨22898653, 2, [(2, 2), (3, 1), (7, 1), (272603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_272603
  · decide +kernel

theorem prime_24607637 : Nat.Prime 24607637 := by
  apply nodeValid_prime [2, 17, 361877] ⟨24607637, 2, [(2, 2), (17, 1), (361877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_361877
  · decide +kernel

theorem prime_25004173 : Nat.Prime 25004173 := by
  apply nodeValid_prime [2, 3, 2083681] ⟨25004173, 5, [(2, 2), (3, 1), (2083681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2083681
  · decide +kernel

theorem prime_42469991 : Nat.Prime 42469991 := by
  apply nodeValid_prime [2, 5, 103, 41233] ⟨42469991, 11, [(2, 1), (5, 1), (103, 1), (41233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_41233
  · decide +kernel

theorem prime_54341941 : Nat.Prime 54341941 := by
  apply nodeValid_prime [2, 3, 5, 29, 31231] ⟨54341941, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (31231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_31231
  · decide +kernel

theorem prime_55125701 : Nat.Prime 55125701 := by
  apply nodeValid_prime [2, 5, 7, 61, 1291] ⟨55125701, 2, [(2, 2), (5, 2), (7, 1), (61, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_1291
  · decide +kernel

theorem prime_58550497 : Nat.Prime 58550497 := by
  apply nodeValid_prime [2, 3, 67, 9103] ⟨58550497, 5, [(2, 5), (3, 1), (67, 1), (9103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_9103
  · decide +kernel

theorem prime_60122567 : Nat.Prime 60122567 := by
  apply nodeValid_prime [2, 7, 4294469] ⟨60122567, 5, [(2, 1), (7, 1), (4294469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4294469
  · decide +kernel

theorem prime_98983193 : Nat.Prime 98983193 := by
  apply nodeValid_prime [2, 7, 11, 160687] ⟨98983193, 3, [(2, 3), (7, 1), (11, 1), (160687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_160687
  · decide +kernel

theorem prime_136689599 : Nat.Prime 136689599 := by
  apply nodeValid_prime [2, 23, 211, 14083] ⟨136689599, 7, [(2, 1), (23, 1), (211, 1), (14083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_211
    · exact prime_14083
  · decide +kernel

theorem prime_237772741 : Nat.Prime 237772741 := by
  apply nodeValid_prime [2, 3, 5, 29, 136651] ⟨237772741, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (136651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_136651
  · decide +kernel

theorem prime_247009463 : Nat.Prime 247009463 := by
  apply nodeValid_prime [2, 7, 19, 928607] ⟨247009463, 5, [(2, 1), (7, 1), (19, 1), (928607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_928607
  · decide +kernel

theorem prime_323887637 : Nat.Prime 323887637 := by
  apply nodeValid_prime [2, 1607, 50387] ⟨323887637, 2, [(2, 2), (1607, 1), (50387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1607
    · exact prime_50387
  · decide +kernel

theorem prime_357388259 : Nat.Prime 357388259 := by
  apply nodeValid_prime [2, 79, 163, 13877] ⟨357388259, 2, [(2, 1), (79, 1), (163, 1), (13877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_163
    · exact prime_13877
  · decide +kernel

theorem prime_376941881 : Nat.Prime 376941881 := by
  apply nodeValid_prime [2, 5, 7, 47, 28643] ⟨376941881, 3, [(2, 3), (5, 1), (7, 1), (47, 1), (28643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_28643
  · decide +kernel

theorem prime_506004511 : Nat.Prime 506004511 := by
  apply nodeValid_prime [2, 3, 5, 11, 1533347] ⟨506004511, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (1533347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1533347
  · decide +kernel

theorem prime_552011147 : Nat.Prime 552011147 := by
  apply nodeValid_prime [2, 47, 5872459] ⟨552011147, 2, [(2, 1), (47, 1), (5872459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_5872459
  · decide +kernel

theorem prime_594596809 : Nat.Prime 594596809 := by
  apply nodeValid_prime [2, 3, 13, 37, 59, 97] ⟨594596809, 43, [(2, 3), (3, 3), (13, 1), (37, 1), (59, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_59
    · exact prime_97
  · decide +kernel

theorem prime_670100077 : Nat.Prime 670100077 := by
  apply nodeValid_prime [2, 3, 18613891] ⟨670100077, 2, [(2, 2), (3, 2), (18613891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18613891
  · decide +kernel

theorem prime_714776519 : Nat.Prime 714776519 := by
  apply nodeValid_prime [2, 357388259] ⟨714776519, 7, [(2, 1), (357388259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_357388259
  · decide +kernel

theorem prime_740071301 : Nat.Prime 740071301 := by
  apply nodeValid_prime [2, 5, 29, 255197] ⟨740071301, 2, [(2, 2), (5, 2), (29, 1), (255197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_255197
  · decide +kernel

theorem prime_750125191 : Nat.Prime 750125191 := by
  apply nodeValid_prime [2, 3, 5, 25004173] ⟨750125191, 3, [(2, 1), (3, 1), (5, 1), (25004173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_25004173
  · decide +kernel

theorem prime_801570443 : Nat.Prime 801570443 := by
  apply nodeValid_prime [2, 19, 37, 570107] ⟨801570443, 2, [(2, 1), (19, 1), (37, 1), (570107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_570107
  · decide +kernel

theorem prime_978154939 : Nat.Prime 978154939 := by
  apply nodeValid_prime [2, 3, 54341941] ⟨978154939, 2, [(2, 1), (3, 2), (54341941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54341941
  · decide +kernel

theorem prime_980768773 : Nat.Prime 980768773 := by
  apply nodeValid_prime [2, 3, 181, 150517] ⟨980768773, 5, [(2, 2), (3, 2), (181, 1), (150517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_150517
  · decide +kernel

theorem prime_1051826353 : Nat.Prime 1051826353 := by
  apply nodeValid_prime [2, 3, 21913049] ⟨1051826353, 5, [(2, 4), (3, 1), (21913049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21913049
  · decide +kernel

theorem prime_1488534329 : Nat.Prime 1488534329 := by
  apply nodeValid_prime [2, 19, 199, 49211] ⟨1488534329, 3, [(2, 3), (19, 1), (199, 1), (49211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_199
    · exact prime_49211
  · decide +kernel

theorem prime_2122059167 : Nat.Prime 2122059167 := by
  apply nodeValid_prime [2, 23, 29, 69163] ⟨2122059167, 5, [(2, 1), (23, 2), (29, 1), (69163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_69163
  · decide +kernel

theorem prime_2259305173 : Nat.Prime 2259305173 := by
  apply nodeValid_prime [2, 3, 31, 59, 34313] ⟨2259305173, 2, [(2, 2), (3, 2), (31, 1), (59, 1), (34313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_59
    · exact prime_34313
  · decide +kernel

theorem prime_3148167859 : Nat.Prime 3148167859 := by
  apply nodeValid_prime [2, 3, 11, 43, 1109291] ⟨3148167859, 2, [(2, 1), (3, 1), (11, 1), (43, 1), (1109291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_1109291
  · decide +kernel

theorem prime_3312066883 : Nat.Prime 3312066883 := by
  apply nodeValid_prime [2, 3, 552011147] ⟨3312066883, 2, [(2, 1), (3, 1), (552011147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_552011147
  · decide +kernel

theorem prime_4131560143 : Nat.Prime 4131560143 := by
  apply nodeValid_prime [2, 3, 43, 1779311] ⟨4131560143, 3, [(2, 1), (3, 3), (43, 1), (1779311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1779311
  · decide +kernel

theorem prime_5718212153 : Nat.Prime 5718212153 := by
  apply nodeValid_prime [2, 714776519] ⟨5718212153, 3, [(2, 3), (714776519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_714776519
  · decide +kernel

theorem prime_8027015599 : Nat.Prime 8027015599 := by
  apply nodeValid_prime [2, 3, 7, 2359499] ⟨8027015599, 3, [(2, 1), (3, 5), (7, 1), (2359499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2359499
  · decide +kernel

theorem prime_8330347117 : Nat.Prime 8330347117 := by
  apply nodeValid_prime [2, 3, 7, 13, 47, 59, 131] ⟨8330347117, 2, [(2, 2), (3, 2), (7, 2), (13, 1), (47, 1), (59, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_47
    · exact prime_59
    · exact prime_131
  · decide +kernel

theorem prime_23121914867 : Nat.Prime 23121914867 := by
  apply nodeValid_prime [2, 37, 181, 1726289] ⟨23121914867, 2, [(2, 1), (37, 1), (181, 1), (1726289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_181
    · exact prime_1726289
  · decide +kernel

theorem prime_31287275431 : Nat.Prime 31287275431 := by
  apply nodeValid_prime [2, 3, 5, 293, 3559417] ⟨31287275431, 3, [(2, 1), (3, 1), (5, 1), (293, 1), (3559417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_3559417
  · decide +kernel

theorem prime_57758914673 : Nat.Prime 57758914673 := by
  apply nodeValid_prime [2, 17, 499, 425549] ⟨57758914673, 3, [(2, 4), (17, 1), (499, 1), (425549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_499
    · exact prime_425549
  · decide +kernel

theorem prime_82916499857 : Nat.Prime 82916499857 := by
  apply nodeValid_prime [2, 17, 47, 381527] ⟨82916499857, 3, [(2, 4), (17, 2), (47, 1), (381527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_381527
  · decide +kernel

theorem prime_87182332957 : Nat.Prime 87182332957 := by
  apply nodeValid_prime [2, 3, 7451, 325021] ⟨87182332957, 5, [(2, 2), (3, 2), (7451, 1), (325021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7451
    · exact prime_325021
  · decide +kernel

theorem prime_105182635301 : Nat.Prime 105182635301 := by
  apply nodeValid_prime [2, 5, 1051826353] ⟨105182635301, 2, [(2, 2), (5, 2), (1051826353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1051826353
  · decide +kernel

theorem prime_139486111741 : Nat.Prime 139486111741 := by
  apply nodeValid_prime [2, 3, 5, 21773, 35591] ⟨139486111741, 2, [(2, 2), (3, 2), (5, 1), (21773, 1), (35591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21773
    · exact prime_35591
  · decide +kernel

theorem prime_354529153487 : Nat.Prime 354529153487 := by
  apply nodeValid_prime [2, 31, 5718212153] ⟨354529153487, 5, [(2, 1), (31, 1), (5718212153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_5718212153
  · decide +kernel

theorem prime_415871725909 : Nat.Prime 415871725909 := by
  apply nodeValid_prime [2, 3, 107, 323887637] ⟨415871725909, 2, [(2, 2), (3, 1), (107, 1), (323887637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_323887637
  · decide +kernel

theorem prime_417487083509 : Nat.Prime 417487083509 := by
  apply nodeValid_prime [2, 11, 107, 877, 101113] ⟨417487083509, 2, [(2, 2), (11, 1), (107, 1), (877, 1), (101113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_107
    · exact prime_877
    · exact prime_101113
  · decide +kernel

theorem prime_628660034879 : Nat.Prime 628660034879 := by
  apply nodeValid_prime [2, 197921, 1588159] ⟨628660034879, 7, [(2, 1), (197921, 1), (1588159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197921
    · exact prime_1588159
  · decide +kernel

theorem prime_631095811807 : Nat.Prime 631095811807 := by
  apply nodeValid_prime [2, 3, 105182635301] ⟨631095811807, 3, [(2, 1), (3, 1), (105182635301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105182635301
  · decide +kernel

theorem prime_1254403261519 : Nat.Prime 1254403261519 := by
  apply nodeValid_prime [2, 3, 11, 1987, 2311, 4139] ⟨1254403261519, 3, [(2, 1), (3, 1), (11, 1), (1987, 1), (2311, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1987
    · exact prime_2311
    · exact prime_4139
  · decide +kernel

theorem prime_1258293345373 : Nat.Prime 1258293345373 := by
  apply nodeValid_prime [2, 3, 7, 237772741] ⟨1258293345373, 5, [(2, 2), (3, 3), (7, 2), (237772741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_237772741
  · decide +kernel

theorem prime_2506864015871 : Nat.Prime 2506864015871 := by
  apply nodeValid_prime [2, 5, 37, 32377, 209263] ⟨2506864015871, 13, [(2, 1), (5, 1), (37, 1), (32377, 1), (209263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_32377
    · exact prime_209263
  · decide +kernel

theorem prime_2524383247229 : Nat.Prime 2524383247229 := by
  apply nodeValid_prime [2, 631095811807] ⟨2524383247229, 2, [(2, 2), (631095811807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_631095811807
  · decide +kernel

theorem prime_4963408141217 : Nat.Prime 4963408141217 := by
  apply nodeValid_prime [2, 7, 797, 2633, 10559] ⟨4963408141217, 3, [(2, 5), (7, 1), (797, 1), (2633, 1), (10559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_797
    · exact prime_2633
    · exact prime_10559
  · decide +kernel

theorem prime_4963408148819 : Nat.Prime 4963408148819 := by
  apply nodeValid_prime [2, 7, 354529153487] ⟨4963408148819, 2, [(2, 1), (7, 1), (354529153487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_354529153487
  · decide +kernel

theorem prime_4963408149523 : Nat.Prime 4963408149523 := by
  apply nodeValid_prime [2, 3, 17, 197, 247009463] ⟨4963408149523, 3, [(2, 1), (3, 1), (17, 1), (197, 1), (247009463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_197
    · exact prime_247009463
  · decide +kernel

theorem prime_4967266661879 : Nat.Prime 4967266661879 := by
  apply nodeValid_prime [2, 43, 57758914673] ⟨4967266661879, 7, [(2, 1), (43, 1), (57758914673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_57758914673
  · decide +kernel

theorem prime_4967266665709 : Nat.Prime 4967266665709 := by
  apply nodeValid_prime [2, 3, 2503, 55125701] ⟨4967266665709, 2, [(2, 2), (3, 2), (2503, 1), (55125701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2503
    · exact prime_55125701
  · decide +kernel

theorem prime_4967266698131 : Nat.Prime 4967266698131 := by
  apply nodeValid_prime [2, 5, 11, 23, 239, 1787, 4597] ⟨4967266698131, 2, [(2, 1), (5, 1), (11, 1), (23, 1), (239, 1), (1787, 1), (4597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_239
    · exact prime_1787
    · exact prime_4597
  · decide +kernel

theorem prime_4971127289707 : Nat.Prime 4971127289707 := by
  apply nodeValid_prime [2, 3, 41, 33073, 203669] ⟨4971127289707, 5, [(2, 1), (3, 2), (41, 1), (33073, 1), (203669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_33073
    · exact prime_203669
  · decide +kernel

theorem prime_4971127336433 : Nat.Prime 4971127336433 := by
  apply nodeValid_prime [2, 2273, 136689599] ⟨4971127336433, 3, [(2, 4), (2273, 1), (136689599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2273
    · exact prime_136689599
  · decide +kernel

theorem prime_4971127336559 : Nat.Prime 4971127336559 := by
  apply nodeValid_prime [2, 479, 13003, 399067] ⟨4971127336559, 13, [(2, 1), (479, 1), (13003, 1), (399067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_13003
    · exact prime_399067
  · decide +kernel

theorem prime_4974989915123 : Nat.Prime 4974989915123 := by
  apply nodeValid_prime [2, 41, 97, 4013, 155861] ⟨4974989915123, 2, [(2, 1), (41, 1), (97, 1), (4013, 1), (155861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_97
    · exact prime_4013
    · exact prime_155861
  · decide +kernel

theorem prime_4974989990947 : Nat.Prime 4974989990947 := by
  apply nodeValid_prime [2, 3, 367, 2259305173] ⟨4974989990947, 2, [(2, 1), (3, 1), (367, 1), (2259305173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_2259305173
  · decide +kernel

theorem prime_4974989991421 : Nat.Prime 4974989991421 := by
  apply nodeValid_prime [2, 3, 5, 82916499857] ⟨4974989991421, 10, [(2, 2), (3, 1), (5, 1), (82916499857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_82916499857
  · decide +kernel

theorem prime_4978854576701 : Nat.Prime 4978854576701 := by
  apply nodeValid_prime [2, 5, 47, 353, 1283, 2339] ⟨4978854576701, 2, [(2, 2), (5, 2), (47, 1), (353, 1), (1283, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_353
    · exact prime_1283
    · exact prime_2339
  · decide +kernel

theorem prime_4978854607901 : Nat.Prime 4978854607901 := by
  apply nodeValid_prime [2, 5, 503, 98983193] ⟨4978854607901, 2, [(2, 2), (5, 2), (503, 1), (98983193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_503
    · exact prime_98983193
  · decide +kernel

theorem prime_4978854610817 : Nat.Prime 4978854610817 := by
  apply nodeValid_prime [2, 67, 3919, 148139] ⟨4978854610817, 3, [(2, 7), (67, 1), (3919, 1), (148139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_3919
    · exact prime_148139
  · decide +kernel

theorem prime_4982721259267 : Nat.Prime 4982721259267 := by
  apply nodeValid_prime [2, 3, 283, 978154939] ⟨4982721259267, 2, [(2, 1), (3, 2), (283, 1), (978154939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_978154939
  · decide +kernel

theorem prime_4982721259421 : Nat.Prime 4982721259421 := by
  apply nodeValid_prime [2, 5, 419, 594596809] ⟨4982721259421, 2, [(2, 2), (5, 1), (419, 1), (594596809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_419
    · exact prime_594596809
  · decide +kernel

theorem prime_4982721265007 : Nat.Prime 4982721265007 := by
  apply nodeValid_prime [2, 107, 4201, 5542429] ⟨4982721265007, 5, [(2, 1), (107, 1), (4201, 1), (5542429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_4201
    · exact prime_5542429
  · decide +kernel

theorem prime_4986589992229 : Nat.Prime 4986589992229 := by
  apply nodeValid_prime [2, 3, 13, 433, 24607637] ⟨4986589992229, 2, [(2, 2), (3, 2), (13, 1), (433, 1), (24607637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_433
    · exact prime_24607637
  · decide +kernel

theorem prime_4986590001671 : Nat.Prime 4986590001671 := by
  apply nodeValid_prime [2, 5, 47, 211, 3571, 14081] ⟨4986590001671, 17, [(2, 1), (5, 1), (47, 1), (211, 1), (3571, 1), (14081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_211
    · exact prime_3571
    · exact prime_14081
  · decide +kernel

theorem prime_4986590002151 : Nat.Prime 4986590002151 := by
  apply nodeValid_prime [2, 5, 67, 1488534329] ⟨4986590002151, 14, [(2, 1), (5, 2), (67, 1), (1488534329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_1488534329
  · decide +kernel

theorem prime_4990460710909 : Nat.Prime 4990460710909 := by
  apply nodeValid_prime [2, 3, 415871725909] ⟨4990460710909, 2, [(2, 2), (3, 1), (415871725909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_415871725909
  · decide +kernel

theorem prime_4990460712961 : Nat.Prime 4990460712961 := by
  apply nodeValid_prime [2, 3, 5, 61, 73, 191] ⟨4990460712961, 7, [(2, 11), (3, 1), (5, 1), (61, 1), (73, 1), (191, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_73
    · exact prime_191
  · decide +kernel

theorem prime_4990460741251 : Nat.Prime 4990460741251 := by
  apply nodeValid_prime [2, 3, 5, 7817, 170243] ⟨4990460741251, 2, [(2, 1), (3, 1), (5, 4), (7817, 1), (170243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7817
    · exact prime_170243
  · decide +kernel

theorem prime_4994333521679 : Nat.Prime 4994333521679 := by
  apply nodeValid_prime [2, 3329, 750125191] ⟨4994333521679, 13, [(2, 1), (3329, 1), (750125191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3329
    · exact prime_750125191
  · decide +kernel

theorem prime_4994333611219 : Nat.Prime 4994333611219 := by
  apply nodeValid_prime [2, 3, 7, 577, 22898653] ⟨4994333611219, 2, [(2, 1), (3, 3), (7, 1), (577, 1), (22898653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_577
    · exact prime_22898653
  · decide +kernel

theorem prime_4994333611273 : Nat.Prime 4994333611273 := by
  apply nodeValid_prime [2, 3, 23121914867] ⟨4994333611273, 5, [(2, 3), (3, 3), (23121914867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23121914867
  · decide +kernel

theorem prime_4998208270201 : Nat.Prime 4998208270201 := by
  apply nodeValid_prime [2, 3, 5, 8330347117] ⟨4998208270201, 7, [(2, 3), (3, 1), (5, 2), (8330347117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8330347117
  · decide +kernel

theorem prime_4998208272271 : Nat.Prime 4998208272271 := by
  apply nodeValid_prime [2, 3, 5, 17, 20071, 488287] ⟨4998208272271, 11, [(2, 1), (3, 1), (5, 1), (17, 1), (20071, 1), (488287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_20071
    · exact prime_488287
  · decide +kernel

theorem prime_4998208332661 : Nat.Prime 4998208332661 := by
  apply nodeValid_prime [2, 3, 5, 31, 71, 631, 59981] ⟨4998208332661, 6, [(2, 2), (3, 1), (5, 1), (31, 1), (71, 1), (631, 1), (59981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_71
    · exact prime_631
    · exact prime_59981
  · decide +kernel

theorem prime_5002085176787 : Nat.Prime 5002085176787 := by
  apply nodeValid_prime [2, 181, 1423, 9710411] ⟨5002085176787, 2, [(2, 1), (181, 1), (1423, 1), (9710411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_1423
    · exact prime_9710411
  · decide +kernel

theorem prime_5002085180419 : Nat.Prime 5002085180419 := by
  apply nodeValid_prime [2, 3, 23, 23131, 1567031] ⟨5002085180419, 2, [(2, 1), (3, 1), (23, 1), (23131, 1), (1567031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_23131
    · exact prime_1567031
  · decide +kernel

theorem prime_5002085182403 : Nat.Prime 5002085182403 := by
  apply nodeValid_prime [2, 7, 11, 5717, 516499] ⟨5002085182403, 5, [(2, 1), (7, 1), (11, 2), (5717, 1), (516499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_5717
    · exact prime_516499
  · decide +kernel

theorem prime_5005964062189 : Nat.Prime 5005964062189 := by
  apply nodeValid_prime [2, 3, 17519, 7937357] ⟨5005964062189, 2, [(2, 2), (3, 2), (17519, 1), (7937357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17519
    · exact prime_7937357
  · decide +kernel

theorem prime_5005964062559 : Nat.Prime 5005964062559 := by
  apply nodeValid_prime [2, 3517, 6551, 108637] ⟨5005964062559, 11, [(2, 1), (3517, 1), (6551, 1), (108637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3517
    · exact prime_6551
    · exact prime_108637
  · decide +kernel

theorem prime_5005964068961 : Nat.Prime 5005964068961 := by
  apply nodeValid_prime [2, 5, 31287275431] ⟨5005964068961, 3, [(2, 5), (5, 1), (31287275431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31287275431
  · decide +kernel

theorem prime_5009844995989 : Nat.Prime 5009844995989 := by
  apply nodeValid_prime [2, 3, 7, 6229, 1367819] ⟨5009844995989, 10, [(2, 2), (3, 1), (7, 2), (6229, 1), (1367819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6229
    · exact prime_1367819
  · decide +kernel

theorem prime_5009844997849 : Nat.Prime 5009844997849 := by
  apply nodeValid_prime [2, 3, 263, 1181, 672059] ⟨5009844997849, 7, [(2, 3), (3, 1), (263, 1), (1181, 1), (672059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_1181
    · exact prime_672059
  · decide +kernel

theorem prime_5009845002109 : Nat.Prime 5009845002109 := by
  apply nodeValid_prime [2, 3, 417487083509] ⟨5009845002109, 2, [(2, 2), (3, 1), (417487083509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_417487083509
  · decide +kernel

theorem prime_5013727965979 : Nat.Prime 5013727965979 := by
  apply nodeValid_prime [2, 3, 19, 3613, 12172729] ⟨5013727965979, 3, [(2, 1), (3, 1), (19, 1), (3613, 1), (12172729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_3613
    · exact prime_12172729
  · decide +kernel

theorem prime_5013728031439 : Nat.Prime 5013728031439 := by
  apply nodeValid_prime [2, 3, 7, 137, 293, 330431] ⟨5013728031439, 7, [(2, 1), (3, 3), (7, 1), (137, 1), (293, 1), (330431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_293
    · exact prime_330431
  · decide +kernel

theorem prime_5013728031743 : Nat.Prime 5013728031743 := by
  apply nodeValid_prime [2, 2506864015871] ⟨5013728031743, 5, [(2, 1), (2506864015871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2506864015871
  · decide +kernel

theorem prime_5017612969529 : Nat.Prime 5017612969529 := by
  apply nodeValid_prime [2, 31, 8669, 2333869] ⟨5017612969529, 3, [(2, 3), (31, 1), (8669, 1), (2333869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_8669
    · exact prime_2333869
  · decide +kernel

theorem prime_5017613042669 : Nat.Prime 5017613042669 := by
  apply nodeValid_prime [2, 1279, 980768773] ⟨5017613042669, 2, [(2, 2), (1279, 1), (980768773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1279
    · exact prime_980768773
  · decide +kernel

theorem prime_5017613046077 : Nat.Prime 5017613046077 := by
  apply nodeValid_prime [2, 1254403261519] ⟨5017613046077, 2, [(2, 2), (1254403261519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1254403261519
  · decide +kernel

theorem prime_5021500009567 : Nat.Prime 5021500009567 := by
  apply nodeValid_prime [2, 3, 113, 8753, 846149] ⟨5021500009567, 3, [(2, 1), (3, 1), (113, 1), (8753, 1), (846149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_8753
    · exact prime_846149
  · decide +kernel

theorem prime_5021500022603 : Nat.Prime 5021500022603 := by
  apply nodeValid_prime [2, 7, 281, 389, 468761] ⟨5021500022603, 5, [(2, 1), (7, 2), (281, 1), (389, 1), (468761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_281
    · exact prime_389
    · exact prime_468761
  · decide +kernel

theorem prime_5021500022677 : Nat.Prime 5021500022677 := by
  apply nodeValid_prime [2, 3, 139486111741] ⟨5021500022677, 2, [(2, 2), (3, 2), (139486111741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139486111741
  · decide +kernel

theorem prime_5025389095049 : Nat.Prime 5025389095049 := by
  apply nodeValid_prime [2, 7, 2113, 42469991] ⟨5025389095049, 6, [(2, 3), (7, 1), (2113, 1), (42469991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2113
    · exact prime_42469991
  · decide +kernel

theorem prime_5025389157493 : Nat.Prime 5025389157493 := by
  apply nodeValid_prime [2, 3, 11, 101, 376941881] ⟨5025389157493, 6, [(2, 2), (3, 1), (11, 1), (101, 1), (376941881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_101
    · exact prime_376941881
  · decide +kernel

theorem prime_5025389157511 : Nat.Prime 5025389157511 := by
  apply nodeValid_prime [2, 3, 5, 2861, 58550497] ⟨5025389157511, 6, [(2, 1), (3, 1), (5, 1), (2861, 1), (58550497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2861
    · exact prime_58550497
  · decide +kernel

theorem prime_5029280225791 : Nat.Prime 5029280225791 := by
  apply nodeValid_prime [2, 3, 5, 79, 2122059167] ⟨5029280225791, 3, [(2, 1), (3, 1), (5, 1), (79, 1), (2122059167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_2122059167
  · decide +kernel

theorem prime_5029280277883 : Nat.Prime 5029280277883 := by
  apply nodeValid_prime [2, 3, 7, 17, 29, 113, 307067] ⟨5029280277883, 2, [(2, 1), (3, 1), (7, 2), (17, 1), (29, 1), (113, 1), (307067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_29
    · exact prime_113
    · exact prime_307067
  · decide +kernel

theorem prime_5029280279033 : Nat.Prime 5029280279033 := by
  apply nodeValid_prime [2, 628660034879] ⟨5029280279033, 3, [(2, 3), (628660034879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_628660034879
  · decide +kernel

theorem prime_5033173381493 : Nat.Prime 5033173381493 := by
  apply nodeValid_prime [2, 1258293345373] ⟨5033173381493, 2, [(2, 2), (1258293345373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1258293345373
  · decide +kernel

theorem prime_5033173382453 : Nat.Prime 5033173382453 := by
  apply nodeValid_prime [2, 23, 31, 127, 13895963] ⟨5033173382453, 2, [(2, 2), (23, 1), (31, 1), (127, 1), (13895963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_127
    · exact prime_13895963
  · decide +kernel

theorem prime_5033173383409 : Nat.Prime 5033173383409 := by
  apply nodeValid_prime [2, 3, 53, 491, 1451, 2777] ⟨5033173383409, 11, [(2, 4), (3, 1), (53, 1), (491, 1), (1451, 1), (2777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_491
    · exact prime_1451
    · exact prime_2777
  · decide +kernel

theorem prime_5037068574401 : Nat.Prime 5037068574401 := by
  apply nodeValid_prime [2, 5, 3148167859] ⟨5037068574401, 3, [(2, 6), (5, 2), (3148167859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3148167859
  · decide +kernel

theorem prime_5037068663261 : Nat.Prime 5037068663261 := by
  apply nodeValid_prime [2, 5, 59, 71, 60122567] ⟨5037068663261, 2, [(2, 2), (5, 1), (59, 1), (71, 1), (60122567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_71
    · exact prime_60122567
  · decide +kernel

theorem prime_5037068663813 : Nat.Prime 5037068663813 := by
  apply nodeValid_prime [2, 1571, 801570443] ⟨5037068663813, 2, [(2, 2), (1571, 1), (801570443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1571
    · exact prime_801570443
  · decide +kernel

theorem prime_5040965795927 : Nat.Prime 5040965795927 := by
  apply nodeValid_prime [2, 761, 3312066883] ⟨5040965795927, 5, [(2, 1), (761, 1), (3312066883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_761
    · exact prime_3312066883
  · decide +kernel

theorem prime_5040965796173 : Nat.Prime 5040965796173 := by
  apply nodeValid_prime [2, 157, 8027015599] ⟨5040965796173, 2, [(2, 2), (157, 1), (8027015599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_8027015599
  · decide +kernel

theorem prime_5040965809819 : Nat.Prime 5040965809819 := by
  apply nodeValid_prime [2, 3, 17189, 16292609] ⟨5040965809819, 7, [(2, 1), (3, 2), (17189, 1), (16292609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17189
    · exact prime_16292609
  · decide +kernel

theorem prime_5044864974671 : Nat.Prime 5044864974671 := by
  apply nodeValid_prime [2, 5, 997, 506004511] ⟨5044864974671, 7, [(2, 1), (5, 1), (997, 1), (506004511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_997
    · exact prime_506004511
  · decide +kernel

theorem prime_5044865093083 : Nat.Prime 5044865093083 := by
  apply nodeValid_prime [2, 3, 55217, 5075797] ⟨5044865093083, 2, [(2, 1), (3, 2), (55217, 1), (5075797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55217
    · exact prime_5075797
  · decide +kernel

theorem prime_5048766415423 : Nat.Prime 5048766415423 := by
  apply nodeValid_prime [2, 3, 379, 740071301] ⟨5048766415423, 3, [(2, 1), (3, 2), (379, 1), (740071301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_740071301
  · decide +kernel

theorem prime_5048766494459 : Nat.Prime 5048766494459 := by
  apply nodeValid_prime [2, 2524383247229] ⟨5048766494459, 2, [(2, 1), (2524383247229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2524383247229
  · decide +kernel

theorem prime_5048766494747 : Nat.Prime 5048766494747 := by
  apply nodeValid_prime [2, 13, 47, 4131560143] ⟨5048766494747, 2, [(2, 1), (13, 1), (47, 1), (4131560143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_4131560143
  · decide +kernel

theorem prime_5052669483341 : Nat.Prime 5052669483341 := by
  apply nodeValid_prime [2, 5, 38149, 6622283] ⟨5052669483341, 3, [(2, 2), (5, 1), (38149, 1), (6622283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_38149
    · exact prime_6622283
  · decide +kernel

theorem prime_5052669484721 : Nat.Prime 5052669484721 := by
  apply nodeValid_prime [2, 5, 11, 13, 19, 3659, 6353] ⟨5052669484721, 6, [(2, 4), (5, 1), (11, 1), (13, 1), (19, 1), (3659, 1), (6353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_3659
    · exact prime_6353
  · decide +kernel

theorem prime_5052669779473 : Nat.Prime 5052669779473 := by
  apply nodeValid_prime [2, 3, 7, 15619, 962783] ⟨5052669779473, 15, [(2, 4), (3, 1), (7, 1), (15619, 1), (962783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_15619
    · exact prime_962783
  · decide +kernel

theorem prime_5056575181043 : Nat.Prime 5056575181043 := by
  apply nodeValid_prime [2, 7, 11, 670100077] ⟨5056575181043, 5, [(2, 1), (7, 3), (11, 1), (670100077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_670100077
  · decide +kernel

theorem prime_5056575311441 : Nat.Prime 5056575311441 := by
  apply nodeValid_prime [2, 5, 193, 397, 824933] ⟨5056575311441, 3, [(2, 4), (5, 1), (193, 1), (397, 1), (824933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
    · exact prime_397
    · exact prime_824933
  · decide +kernel

theorem prime_5056575311507 : Nat.Prime 5056575311507 := by
  apply nodeValid_prime [2, 29, 87182332957] ⟨5056575311507, 2, [(2, 1), (29, 1), (87182332957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_87182332957
  · decide +kernel

end Sude.Lucas.Generated
