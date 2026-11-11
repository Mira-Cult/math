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
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4861 : Nat.Prime 4861 := by
  apply nodeValid_prime [2, 3, 5] ⟨4861, 11, [(2, 2), (3, 5), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_6203 : Nat.Prime 6203 := by
  apply nodeValid_prime [2, 7, 443] ⟨6203, 2, [(2, 1), (7, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_443
  · decide +kernel

theorem prime_7219 : Nat.Prime 7219 := by
  apply nodeValid_prime [2, 3, 401] ⟨7219, 2, [(2, 1), (3, 2), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
  · decide +kernel

theorem prime_8893 : Nat.Prime 8893 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨8893, 5, [(2, 2), (3, 2), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_11239 : Nat.Prime 11239 := by
  apply nodeValid_prime [2, 3, 1873] ⟨11239, 3, [(2, 1), (3, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1873
  · decide +kernel

theorem prime_11549 : Nat.Prime 11549 := by
  apply nodeValid_prime [2, 2887] ⟨11549, 2, [(2, 2), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2887
  · decide +kernel

theorem prime_11657 : Nat.Prime 11657 := by
  apply nodeValid_prime [2, 31, 47] ⟨11657, 3, [(2, 3), (31, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_47
  · decide +kernel

theorem prime_20029 : Nat.Prime 20029 := by
  apply nodeValid_prime [2, 3, 1669] ⟨20029, 2, [(2, 2), (3, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1669
  · decide +kernel

theorem prime_23189 : Nat.Prime 23189 := by
  apply nodeValid_prime [2, 11, 17, 31] ⟨23189, 2, [(2, 2), (11, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_26927 : Nat.Prime 26927 := by
  apply nodeValid_prime [2, 13463] ⟨26927, 5, [(2, 1), (13463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13463
  · decide +kernel

theorem prime_28571 : Nat.Prime 28571 := by
  apply nodeValid_prime [2, 5, 2857] ⟨28571, 2, [(2, 1), (5, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2857
  · decide +kernel

theorem prime_33469 : Nat.Prime 33469 := by
  apply nodeValid_prime [2, 3, 2789] ⟨33469, 2, [(2, 2), (3, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2789
  · decide +kernel

theorem prime_33521 : Nat.Prime 33521 := by
  apply nodeValid_prime [2, 5, 419] ⟨33521, 6, [(2, 4), (5, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_419
  · decide +kernel

theorem prime_35753 : Nat.Prime 35753 := by
  apply nodeValid_prime [2, 41, 109] ⟨35753, 3, [(2, 3), (41, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_109
  · decide +kernel

theorem prime_37813 : Nat.Prime 37813 := by
  apply nodeValid_prime [2, 3, 23, 137] ⟨37813, 2, [(2, 2), (3, 1), (23, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_137
  · decide +kernel

theorem prime_37991 : Nat.Prime 37991 := by
  apply nodeValid_prime [2, 5, 29, 131] ⟨37991, 7, [(2, 1), (5, 1), (29, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_131
  · decide +kernel

theorem prime_42409 : Nat.Prime 42409 := by
  apply nodeValid_prime [2, 3, 19, 31] ⟨42409, 14, [(2, 3), (3, 2), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_46183 : Nat.Prime 46183 := by
  apply nodeValid_prime [2, 3, 43, 179] ⟨46183, 3, [(2, 1), (3, 1), (43, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_179
  · decide +kernel

theorem prime_47137 : Nat.Prime 47137 := by
  apply nodeValid_prime [2, 3, 491] ⟨47137, 5, [(2, 5), (3, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_491
  · decide +kernel

theorem prime_49057 : Nat.Prime 49057 := by
  apply nodeValid_prime [2, 3, 7, 73] ⟨49057, 5, [(2, 5), (3, 1), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_50777 : Nat.Prime 50777 := by
  apply nodeValid_prime [2, 11, 577] ⟨50777, 3, [(2, 3), (11, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_577
  · decide +kernel

theorem prime_51151 : Nat.Prime 51151 := by
  apply nodeValid_prime [2, 3, 5, 11, 31] ⟨51151, 3, [(2, 1), (3, 1), (5, 2), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_52027 : Nat.Prime 52027 := by
  apply nodeValid_prime [2, 3, 13, 23, 29] ⟨52027, 2, [(2, 1), (3, 1), (13, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_57089 : Nat.Prime 57089 := by
  apply nodeValid_prime [2, 223] ⟨57089, 3, [(2, 8), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_223
  · decide +kernel

theorem prime_57143 : Nat.Prime 57143 := by
  apply nodeValid_prime [2, 28571] ⟨57143, 5, [(2, 1), (28571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28571
  · decide +kernel

theorem prime_57977 : Nat.Prime 57977 := by
  apply nodeValid_prime [2, 7247] ⟨57977, 3, [(2, 3), (7247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7247
  · decide +kernel

theorem prime_61469 : Nat.Prime 61469 := by
  apply nodeValid_prime [2, 11, 127] ⟨61469, 2, [(2, 2), (11, 2), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_71443 : Nat.Prime 71443 := by
  apply nodeValid_prime [2, 3, 7] ⟨71443, 11, [(2, 1), (3, 6), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_72647 : Nat.Prime 72647 := by
  apply nodeValid_prime [2, 7, 5189] ⟨72647, 5, [(2, 1), (7, 1), (5189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5189
  · decide +kernel

theorem prime_79549 : Nat.Prime 79549 := by
  apply nodeValid_prime [2, 3, 7, 947] ⟨79549, 2, [(2, 2), (3, 1), (7, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_947
  · decide +kernel

theorem prime_90787 : Nat.Prime 90787 := by
  apply nodeValid_prime [2, 3, 15131] ⟨90787, 3, [(2, 1), (3, 1), (15131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15131
  · decide +kernel

theorem prime_97943 : Nat.Prime 97943 := by
  apply nodeValid_prime [2, 13, 3767] ⟨97943, 5, [(2, 1), (13, 1), (3767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3767
  · decide +kernel

theorem prime_104717 : Nat.Prime 104717 := by
  apply nodeValid_prime [2, 47, 557] ⟨104717, 2, [(2, 2), (47, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_557
  · decide +kernel

theorem prime_123083 : Nat.Prime 123083 := by
  apply nodeValid_prime [2, 19, 41, 79] ⟨123083, 2, [(2, 1), (19, 1), (41, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_79
  · decide +kernel

theorem prime_125617 : Nat.Prime 125617 := by
  apply nodeValid_prime [2, 3, 2617] ⟨125617, 5, [(2, 4), (3, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2617
  · decide +kernel

theorem prime_161563 : Nat.Prime 161563 := by
  apply nodeValid_prime [2, 3, 26927] ⟨161563, 2, [(2, 1), (3, 1), (26927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26927
  · decide +kernel

theorem prime_162079 : Nat.Prime 162079 := by
  apply nodeValid_prime [2, 3, 7, 17, 227] ⟨162079, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_227
  · decide +kernel

theorem prime_168743 : Nat.Prime 168743 := by
  apply nodeValid_prime [2, 7, 17, 709] ⟨168743, 5, [(2, 1), (7, 1), (17, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_709
  · decide +kernel

theorem prime_178183 : Nat.Prime 178183 := by
  apply nodeValid_prime [2, 3, 19, 521] ⟨178183, 5, [(2, 1), (3, 2), (19, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_521
  · decide +kernel

theorem prime_206477 : Nat.Prime 206477 := by
  apply nodeValid_prime [2, 41, 1259] ⟨206477, 2, [(2, 2), (41, 1), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1259
  · decide +kernel

theorem prime_214519 : Nat.Prime 214519 := by
  apply nodeValid_prime [2, 3, 35753] ⟨214519, 3, [(2, 1), (3, 1), (35753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35753
  · decide +kernel

theorem prime_223757 : Nat.Prime 223757 := by
  apply nodeValid_prime [2, 13, 331] ⟨223757, 2, [(2, 2), (13, 2), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_331
  · decide +kernel

theorem prime_234967 : Nat.Prime 234967 := by
  apply nodeValid_prime [2, 3, 39161] ⟨234967, 5, [(2, 1), (3, 1), (39161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39161
  · decide +kernel

theorem prime_246167 : Nat.Prime 246167 := by
  apply nodeValid_prime [2, 123083] ⟨246167, 5, [(2, 1), (123083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_123083
  · decide +kernel

theorem prime_277099 : Nat.Prime 277099 := by
  apply nodeValid_prime [2, 3, 46183] ⟨277099, 2, [(2, 1), (3, 1), (46183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_46183
  · decide +kernel

theorem prime_363149 : Nat.Prime 363149 := by
  apply nodeValid_prime [2, 90787] ⟨363149, 2, [(2, 2), (90787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90787
  · decide +kernel

theorem prime_409823 : Nat.Prime 409823 := by
  apply nodeValid_prime [2, 7, 73, 401] ⟨409823, 5, [(2, 1), (7, 1), (73, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_401
  · decide +kernel

theorem prime_485059 : Nat.Prime 485059 := by
  apply nodeValid_prime [2, 3, 7, 11549] ⟨485059, 2, [(2, 1), (3, 1), (7, 1), (11549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11549
  · decide +kernel

theorem prime_490571 : Nat.Prime 490571 := by
  apply nodeValid_prime [2, 5, 49057] ⟨490571, 2, [(2, 1), (5, 1), (49057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49057
  · decide +kernel

theorem prime_527881 : Nat.Prime 527881 := by
  apply nodeValid_prime [2, 3, 5, 53, 83] ⟨527881, 11, [(2, 3), (3, 1), (5, 1), (53, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_83
  · decide +kernel

theorem prime_562607 : Nat.Prime 562607 := by
  apply nodeValid_prime [2, 11, 107, 239] ⟨562607, 5, [(2, 1), (11, 1), (107, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_107
    · exact prime_239
  · decide +kernel

theorem prime_600697 : Nat.Prime 600697 := by
  apply nodeValid_prime [2, 3, 103] ⟨600697, 5, [(2, 3), (3, 6), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_613813 : Nat.Prime 613813 := by
  apply nodeValid_prime [2, 3, 51151] ⟨613813, 2, [(2, 2), (3, 1), (51151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51151
  · decide +kernel

theorem prime_646253 : Nat.Prime 646253 := by
  apply nodeValid_prime [2, 161563] ⟨646253, 2, [(2, 2), (161563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_161563
  · decide +kernel

theorem prime_841219 : Nat.Prime 841219 := by
  apply nodeValid_prime [2, 3, 7, 20029] ⟨841219, 3, [(2, 1), (3, 1), (7, 1), (20029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_20029
  · decide +kernel

theorem prime_910453 : Nat.Prime 910453 := by
  apply nodeValid_prime [2, 3, 17, 4463] ⟨910453, 7, [(2, 2), (3, 1), (17, 1), (4463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4463
  · decide +kernel

theorem prime_990893 : Nat.Prime 990893 := by
  apply nodeValid_prime [2, 7, 43, 823] ⟨990893, 2, [(2, 2), (7, 1), (43, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_823
  · decide +kernel

theorem prime_1004911 : Nat.Prime 1004911 := by
  apply nodeValid_prime [2, 3, 5, 19, 41, 43] ⟨1004911, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_1103041 : Nat.Prime 1103041 := by
  apply nodeValid_prime [2, 3, 5, 383] ⟨1103041, 23, [(2, 6), (3, 2), (5, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
  · decide +kernel

theorem prime_1142483 : Nat.Prime 1142483 := by
  apply nodeValid_prime [2, 11, 4721] ⟨1142483, 2, [(2, 1), (11, 2), (4721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4721
  · decide +kernel

theorem prime_1324457 : Nat.Prime 1324457 := by
  apply nodeValid_prime [2, 7, 67, 353] ⟨1324457, 5, [(2, 3), (7, 1), (67, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_353
  · decide +kernel

theorem prime_1406443 : Nat.Prime 1406443 := by
  apply nodeValid_prime [2, 3, 29, 59, 137] ⟨1406443, 19, [(2, 1), (3, 1), (29, 1), (59, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_59
    · exact prime_137
  · decide +kernel

theorem prime_1571747 : Nat.Prime 1571747 := by
  apply nodeValid_prime [2, 11, 71443] ⟨1571747, 2, [(2, 1), (11, 1), (71443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71443
  · decide +kernel

theorem prime_2639201 : Nat.Prime 2639201 := by
  apply nodeValid_prime [2, 5, 3299] ⟨2639201, 3, [(2, 5), (5, 2), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3299
  · decide +kernel

theorem prime_3682429 : Nat.Prime 3682429 := by
  apply nodeValid_prime [2, 3, 19, 31, 521] ⟨3682429, 2, [(2, 2), (3, 1), (19, 1), (31, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_521
  · decide +kernel

theorem prime_3979247 : Nat.Prime 3979247 := by
  apply nodeValid_prime [2, 19, 104717] ⟨3979247, 5, [(2, 1), (19, 1), (104717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_104717
  · decide +kernel

theorem prime_4145707 : Nat.Prime 4145707 := by
  apply nodeValid_prime [2, 3, 109, 2113] ⟨4145707, 3, [(2, 1), (3, 2), (109, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_2113
  · decide +kernel

theorem prime_5322461 : Nat.Prime 5322461 := by
  apply nodeValid_prime [2, 5, 11, 13, 1861] ⟨5322461, 2, [(2, 2), (5, 1), (11, 1), (13, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_1861
  · decide +kernel

theorem prime_5462719 : Nat.Prime 5462719 := by
  apply nodeValid_prime [2, 3, 910453] ⟨5462719, 6, [(2, 1), (3, 1), (910453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_910453
  · decide +kernel

theorem prime_5634721 : Nat.Prime 5634721 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 43] ⟨5634721, 23, [(2, 5), (3, 2), (5, 1), (7, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_5828587 : Nat.Prime 5828587 := by
  apply nodeValid_prime [2, 3, 17, 57143] ⟨5828587, 13, [(2, 1), (3, 1), (17, 1), (57143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_57143
  · decide +kernel

theorem prime_6257879 : Nat.Prime 6257879 := by
  apply nodeValid_prime [2, 11, 19, 1361] ⟨6257879, 11, [(2, 1), (11, 2), (19, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1361
  · decide +kernel

theorem prime_7617557 : Nat.Prime 7617557 := by
  apply nodeValid_prime [2, 19, 113, 887] ⟨7617557, 2, [(2, 2), (19, 1), (113, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_113
    · exact prime_887
  · decide +kernel

theorem prime_9923707 : Nat.Prime 9923707 := by
  apply nodeValid_prime [2, 3, 13, 42409] ⟨9923707, 2, [(2, 1), (3, 2), (13, 1), (42409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_42409
  · decide +kernel

theorem prime_10301041 : Nat.Prime 10301041 := by
  apply nodeValid_prime [2, 3, 5, 19, 251] ⟨10301041, 17, [(2, 4), (3, 3), (5, 1), (19, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_251
  · decide +kernel

theorem prime_10644923 : Nat.Prime 10644923 := by
  apply nodeValid_prime [2, 5322461] ⟨10644923, 2, [(2, 1), (5322461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5322461
  · decide +kernel

theorem prime_10671299 : Nat.Prime 10671299 := by
  apply nodeValid_prime [2, 11, 485059] ⟨10671299, 2, [(2, 1), (11, 1), (485059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_485059
  · decide +kernel

theorem prime_11252141 : Nat.Prime 11252141 := by
  apply nodeValid_prime [2, 5, 562607] ⟨11252141, 2, [(2, 2), (5, 1), (562607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_562607
  · decide +kernel

theorem prime_12515759 : Nat.Prime 12515759 := by
  apply nodeValid_prime [2, 6257879] ⟨12515759, 7, [(2, 1), (6257879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6257879
  · decide +kernel

theorem prime_23987693 : Nat.Prime 23987693 := by
  apply nodeValid_prime [2, 37, 162079] ⟨23987693, 2, [(2, 2), (37, 1), (162079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_162079
  · decide +kernel

theorem prime_25031519 : Nat.Prime 25031519 := by
  apply nodeValid_prime [2, 12515759] ⟨25031519, 7, [(2, 1), (12515759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12515759
  · decide +kernel

theorem prime_27067841 : Nat.Prime 27067841 := by
  apply nodeValid_prime [2, 5, 251, 337] ⟨27067841, 3, [(2, 6), (5, 1), (251, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
    · exact prime_337
  · decide +kernel

theorem prime_38288161 : Nat.Prime 38288161 := by
  apply nodeValid_prime [2, 3, 5, 8863] ⟨38288161, 11, [(2, 5), (3, 3), (5, 1), (8863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8863
  · decide +kernel

theorem prime_41989967 : Nat.Prime 41989967 := by
  apply nodeValid_prime [2, 17, 72647] ⟨41989967, 5, [(2, 1), (17, 2), (72647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_72647
  · decide +kernel

theorem prime_42735893 : Nat.Prime 42735893 := by
  apply nodeValid_prime [2, 17, 179, 3511] ⟨42735893, 2, [(2, 2), (17, 1), (179, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_179
    · exact prime_3511
  · decide +kernel

theorem prime_50986217 : Nat.Prime 50986217 := by
  apply nodeValid_prime [2, 23, 277099] ⟨50986217, 3, [(2, 3), (23, 1), (277099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_277099
  · decide +kernel

theorem prime_53818601 : Nat.Prime 53818601 := by
  apply nodeValid_prime [2, 5, 11, 17, 1439] ⟨53818601, 3, [(2, 3), (5, 2), (11, 1), (17, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_1439
  · decide +kernel

theorem prime_54660097 : Nat.Prime 54660097 := by
  apply nodeValid_prime [2, 3, 659] ⟨54660097, 5, [(2, 10), (3, 4), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_659
  · decide +kernel

theorem prime_60627739 : Nat.Prime 60627739 := by
  apply nodeValid_prime [2, 3, 199, 50777] ⟨60627739, 2, [(2, 1), (3, 1), (199, 1), (50777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_50777
  · decide +kernel

theorem prime_64687027 : Nat.Prime 64687027 := by
  apply nodeValid_prime [2, 3, 37, 67, 4349] ⟨64687027, 2, [(2, 1), (3, 1), (37, 1), (67, 1), (4349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_67
    · exact prime_4349
  · decide +kernel

theorem prime_68253043 : Nat.Prime 68253043 := by
  apply nodeValid_prime [2, 3, 11, 13, 79549] ⟨68253043, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (79549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_79549
  · decide +kernel

theorem prime_73509539 : Nat.Prime 73509539 := by
  apply nodeValid_prime [2, 4133, 8893] ⟨73509539, 2, [(2, 1), (4133, 1), (8893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4133
    · exact prime_8893
  · decide +kernel

theorem prime_91398641 : Nat.Prime 91398641 := by
  apply nodeValid_prime [2, 5, 1142483] ⟨91398641, 3, [(2, 4), (5, 1), (1142483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1142483
  · decide +kernel

theorem prime_129752527 : Nat.Prime 129752527 := by
  apply nodeValid_prime [2, 3, 373, 57977] ⟨129752527, 3, [(2, 1), (3, 1), (373, 1), (57977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_57977
  · decide +kernel

theorem prime_136005047 : Nat.Prime 136005047 := by
  apply nodeValid_prime [2, 317, 214519] ⟨136005047, 5, [(2, 1), (317, 1), (214519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_214519
  · decide +kernel

theorem prime_168561119 : Nat.Prime 168561119 := by
  apply nodeValid_prime [2, 11, 43, 178183] ⟨168561119, 11, [(2, 1), (11, 1), (43, 1), (178183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_178183
  · decide +kernel

theorem prime_171958583 : Nat.Prime 171958583 := by
  apply nodeValid_prime [2, 67, 349, 3677] ⟨171958583, 5, [(2, 1), (67, 1), (349, 1), (3677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_349
    · exact prime_3677
  · decide +kernel

theorem prime_187743337 : Nat.Prime 187743337 := by
  apply nodeValid_prime [2, 3, 11, 181, 3929] ⟨187743337, 5, [(2, 3), (3, 1), (11, 1), (181, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_181
    · exact prime_3929
  · decide +kernel

theorem prime_219830719 : Nat.Prime 219830719 := by
  apply nodeValid_prime [2, 3, 1093, 33521] ⟨219830719, 3, [(2, 1), (3, 1), (1093, 1), (33521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1093
    · exact prime_33521
  · decide +kernel

theorem prime_305917303 : Nat.Prime 305917303 := by
  apply nodeValid_prime [2, 3, 50986217] ⟨305917303, 3, [(2, 1), (3, 1), (50986217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50986217
  · decide +kernel

theorem prime_306323923 : Nat.Prime 306323923 := by
  apply nodeValid_prime [2, 3, 79, 646253] ⟨306323923, 5, [(2, 1), (3, 1), (79, 1), (646253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_646253
  · decide +kernel

theorem prime_387508201 : Nat.Prime 387508201 := by
  apply nodeValid_prime [2, 3, 5, 17, 37991] ⟨387508201, 7, [(2, 3), (3, 1), (5, 2), (17, 1), (37991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_37991
  · decide +kernel

theorem prime_468648353 : Nat.Prime 468648353 := by
  apply nodeValid_prime [2, 29, 103, 4903] ⟨468648353, 5, [(2, 5), (29, 1), (103, 1), (4903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_103
    · exact prime_4903
  · decide +kernel

theorem prime_468871789 : Nat.Prime 468871789 := by
  apply nodeValid_prime [2, 3, 7, 11, 71, 1021] ⟨468871789, 2, [(2, 2), (3, 1), (7, 2), (11, 1), (71, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_71
    · exact prime_1021
  · decide +kernel

theorem prime_599195851 : Nat.Prime 599195851 := by
  apply nodeValid_prime [2, 3, 5, 11, 363149] ⟨599195851, 2, [(2, 1), (3, 1), (5, 2), (11, 1), (363149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_363149
  · decide +kernel

theorem prime_819776543 : Nat.Prime 819776543 := by
  apply nodeValid_prime [2, 13, 251, 125617] ⟨819776543, 5, [(2, 1), (13, 1), (251, 1), (125617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_251
    · exact prime_125617
  · decide +kernel

theorem prime_975661033 : Nat.Prime 975661033 := by
  apply nodeValid_prime [2, 3, 4861, 8363] ⟨975661033, 5, [(2, 3), (3, 1), (4861, 1), (8363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4861
    · exact prime_8363
  · decide +kernel

theorem prime_1217649583 : Nat.Prime 1217649583 := by
  apply nodeValid_prime [2, 3, 17, 3979247] ⟨1217649583, 3, [(2, 1), (3, 2), (17, 1), (3979247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3979247
  · decide +kernel

theorem prime_1453962817 : Nat.Prime 1453962817 := by
  apply nodeValid_prime [2, 3, 61, 41381] ⟨1453962817, 5, [(2, 6), (3, 2), (61, 1), (41381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_41381
  · decide +kernel

theorem prime_1474883197 : Nat.Prime 1474883197 := by
  apply nodeValid_prime [2, 3, 37, 337, 9857] ⟨1474883197, 2, [(2, 2), (3, 1), (37, 1), (337, 1), (9857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_337
    · exact prime_9857
  · decide +kernel

theorem prime_1725906839 : Nat.Prime 1725906839 := by
  apply nodeValid_prime [2, 19, 79, 97, 5927] ⟨1725906839, 13, [(2, 1), (19, 1), (79, 1), (97, 1), (5927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_79
    · exact prime_97
    · exact prime_5927
  · decide +kernel

theorem prime_2130460411 : Nat.Prime 2130460411 := by
  apply nodeValid_prime [2, 3, 5, 13, 5462719] ⟨2130460411, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (5462719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_5462719
  · decide +kernel

theorem prime_2259039929 : Nat.Prime 2259039929 := by
  apply nodeValid_prime [2, 281, 1004911] ⟨2259039929, 3, [(2, 3), (281, 1), (1004911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_1004911
  · decide +kernel

theorem prime_2719122311 : Nat.Prime 2719122311 := by
  apply nodeValid_prime [2, 5, 173, 1571747] ⟨2719122311, 11, [(2, 1), (5, 1), (173, 1), (1571747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_1571747
  · decide +kernel

theorem prime_3336753263 : Nat.Prime 3336753263 := by
  apply nodeValid_prime [2, 31, 53818601] ⟨3336753263, 5, [(2, 1), (31, 1), (53818601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_53818601
  · decide +kernel

theorem prime_3580251791 : Nat.Prime 3580251791 := by
  apply nodeValid_prime [2, 5, 47, 7617557] ⟨3580251791, 7, [(2, 1), (5, 1), (47, 1), (7617557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_7617557
  · decide +kernel

theorem prime_3808095853 : Nat.Prime 3808095853 := by
  apply nodeValid_prime [2, 3, 11, 47, 613813] ⟨3808095853, 5, [(2, 2), (3, 1), (11, 1), (47, 1), (613813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_613813
  · decide +kernel

theorem prime_4352286859 : Nat.Prime 4352286859 := by
  apply nodeValid_prime [2, 3, 17, 41, 487, 2137] ⟨4352286859, 3, [(2, 1), (3, 1), (17, 1), (41, 1), (487, 1), (2137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_487
    · exact prime_2137
  · decide +kernel

theorem prime_4641190007 : Nat.Prime 4641190007 := by
  apply nodeValid_prime [2, 11239, 206477] ⟨4641190007, 5, [(2, 1), (11239, 1), (206477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11239
    · exact prime_206477
  · decide +kernel

theorem prime_4854084889 : Nat.Prime 4854084889 := by
  apply nodeValid_prime [2, 3, 19, 10644923] ⟨4854084889, 14, [(2, 3), (3, 1), (19, 1), (10644923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_10644923
  · decide +kernel

theorem prime_5376266867 : Nat.Prime 5376266867 := by
  apply nodeValid_prime [2, 19, 43, 157, 1103] ⟨5376266867, 2, [(2, 1), (19, 2), (43, 1), (157, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_157
    · exact prime_1103
  · decide +kernel

theorem prime_5655788471 : Nat.Prime 5655788471 := by
  apply nodeValid_prime [2, 5, 53, 10671299] ⟨5655788471, 7, [(2, 1), (5, 1), (53, 1), (10671299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_10671299
  · decide +kernel

theorem prime_6135032983 : Nat.Prime 6135032983 := by
  apply nodeValid_prime [2, 3, 13, 149, 527881] ⟨6135032983, 3, [(2, 1), (3, 1), (13, 1), (149, 1), (527881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_149
    · exact prime_527881
  · decide +kernel

theorem prime_11247560603 : Nat.Prime 11247560603 := by
  apply nodeValid_prime [2, 23, 4283, 57089] ⟨11247560603, 2, [(2, 1), (23, 1), (4283, 1), (57089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4283
    · exact prime_57089
  · decide +kernel

theorem prime_15551829961 : Nat.Prime 15551829961 := by
  apply nodeValid_prime [2, 3, 5, 23, 5634721] ⟨15551829961, 7, [(2, 3), (3, 1), (5, 1), (23, 1), (5634721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_5634721
  · decide +kernel

theorem prime_16800833681 : Nat.Prime 16800833681 := by
  apply nodeValid_prime [2, 5, 191, 857, 1283] ⟨16800833681, 3, [(2, 4), (5, 1), (191, 1), (857, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
    · exact prime_857
    · exact prime_1283
  · decide +kernel

theorem prime_33742681417 : Nat.Prime 33742681417 := by
  apply nodeValid_prime [2, 3, 468648353] ⟨33742681417, 10, [(2, 3), (3, 2), (468648353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_468648353
  · decide +kernel

theorem prime_36758870761 : Nat.Prime 36758870761 := by
  apply nodeValid_prime [2, 3, 5, 306323923] ⟨36758870761, 11, [(2, 3), (3, 1), (5, 1), (306323923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_306323923
  · decide +kernel

theorem prime_40944813979 : Nat.Prime 40944813979 := by
  apply nodeValid_prime [2, 3, 37, 1093, 168743] ⟨40944813979, 11, [(2, 1), (3, 1), (37, 1), (1093, 1), (168743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1093
    · exact prime_168743
  · decide +kernel

theorem prime_67015759973 : Nat.Prime 67015759973 := by
  apply nodeValid_prime [2, 7, 37, 64687027] ⟨67015759973, 2, [(2, 2), (7, 1), (37, 1), (64687027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_64687027
  · decide +kernel

theorem prime_68146536893 : Nat.Prime 68146536893 := by
  apply nodeValid_prime [2, 7, 73, 149, 223757] ⟨68146536893, 2, [(2, 2), (7, 1), (73, 1), (149, 1), (223757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_149
    · exact prime_223757
  · decide +kernel

theorem prime_101086896947 : Nat.Prime 101086896947 := by
  apply nodeValid_prime [2, 7, 79, 91398641] ⟨101086896947, 2, [(2, 1), (7, 1), (79, 1), (91398641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_91398641
  · decide +kernel

theorem prime_136482713261 : Nat.Prime 136482713261 := by
  apply nodeValid_prime [2, 5, 37, 1093, 168743] ⟨136482713261, 2, [(2, 2), (5, 1), (37, 1), (1093, 1), (168743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1093
    · exact prime_168743
  · decide +kernel

theorem prime_201610004173 : Nat.Prime 201610004173 := by
  apply nodeValid_prime [2, 3, 16800833681] ⟨201610004173, 2, [(2, 2), (3, 1), (16800833681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16800833681
  · decide +kernel

theorem prime_202456088503 : Nat.Prime 202456088503 := by
  apply nodeValid_prime [2, 3, 33742681417] ⟨202456088503, 3, [(2, 1), (3, 1), (33742681417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33742681417
  · decide +kernel

theorem prime_205008757453 : Nat.Prime 205008757453 := by
  apply nodeValid_prime [2, 3, 4049, 1406443] ⟨205008757453, 2, [(2, 2), (3, 2), (4049, 1), (1406443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4049
    · exact prime_1406443
  · decide +kernel

theorem prime_403783545443 : Nat.Prime 403783545443 := by
  apply nodeValid_prime [2, 521, 387508201] ⟨403783545443, 2, [(2, 1), (521, 1), (387508201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_521
    · exact prime_387508201
  · decide +kernel

theorem prime_407175930281 : Nat.Prime 407175930281 := by
  apply nodeValid_prime [2, 5, 7, 19, 29, 2639201] ⟨407175930281, 3, [(2, 3), (5, 1), (7, 1), (19, 1), (29, 1), (2639201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_29
    · exact prime_2639201
  · decide +kernel

theorem prime_409448132231 : Nat.Prime 409448132231 := by
  apply nodeValid_prime [2, 5, 557, 73509539] ⟨409448132231, 13, [(2, 1), (5, 1), (557, 1), (73509539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_557
    · exact prime_73509539
  · decide +kernel

theorem prime_409448139791 : Nat.Prime 409448139791 := by
  apply nodeValid_prime [2, 5, 40944813979] ⟨409448139791, 11, [(2, 1), (5, 1), (40944813979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40944813979
  · decide +kernel

theorem prime_799700129131 : Nat.Prime 799700129131 := by
  apply nodeValid_prime [2, 3, 5, 7, 3808095853] ⟨799700129131, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (3808095853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3808095853
  · decide +kernel

theorem prime_799700133829 : Nat.Prime 799700133829 := by
  apply nodeValid_prime [2, 3, 23, 47137, 61469] ⟨799700133829, 2, [(2, 2), (3, 1), (23, 1), (47137, 1), (61469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47137
    · exact prime_61469
  · decide +kernel

theorem prime_799700134867 : Nat.Prime 799700134867 := by
  apply nodeValid_prime [2, 3, 59, 2259039929] ⟨799700134867, 2, [(2, 1), (3, 1), (59, 1), (2259039929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2259039929
  · decide +kernel

theorem prime_800820773297 : Nat.Prime 800820773297 := by
  apply nodeValid_prime [2, 29, 1725906839] ⟨800820773297, 3, [(2, 4), (29, 1), (1725906839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1725906839
  · decide +kernel

theorem prime_800820782057 : Nat.Prime 800820782057 := by
  apply nodeValid_prime [2, 23, 4352286859] ⟨800820782057, 3, [(2, 3), (23, 1), (4352286859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4352286859
  · decide +kernel

theorem prime_800820783121 : Nat.Prime 800820783121 := by
  apply nodeValid_prime [2, 3, 5, 3336753263] ⟨800820783121, 11, [(2, 4), (3, 1), (5, 1), (3336753263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3336753263
  · decide +kernel

theorem prime_801942462913 : Nat.Prime 801942462913 := by
  apply nodeValid_prime [2, 3, 19, 219830719] ⟨801942462913, 15, [(2, 6), (3, 1), (19, 1), (219830719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_219830719
  · decide +kernel

theorem prime_801942484891 : Nat.Prime 801942484891 := by
  apply nodeValid_prime [2, 3, 5, 43, 739, 841219] ⟨801942484891, 2, [(2, 1), (3, 1), (5, 1), (43, 1), (739, 1), (841219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_739
    · exact prime_841219
  · decide +kernel

theorem prime_803065268279 : Nat.Prime 803065268279 := by
  apply nodeValid_prime [2, 7, 13, 61, 73, 990893] ⟨803065268279, 14, [(2, 1), (7, 1), (13, 1), (61, 1), (73, 1), (990893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_73
    · exact prime_990893
  · decide +kernel

theorem prime_803065303171 : Nat.Prime 803065303171 := by
  apply nodeValid_prime [2, 3, 5, 13, 61, 11252141] ⟨803065303171, 10, [(2, 1), (3, 2), (5, 1), (13, 1), (61, 1), (11252141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_61
    · exact prime_11252141
  · decide +kernel

theorem prime_803065303939 : Nat.Prime 803065303939 := by
  apply nodeValid_prime [2, 3, 37, 53, 68253043] ⟨803065303939, 10, [(2, 1), (3, 1), (37, 1), (53, 1), (68253043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_53
    · exact prime_68253043
  · decide +kernel

theorem prime_804189115721 : Nat.Prime 804189115721 := by
  apply nodeValid_prime [2, 5, 33469, 600697] ⟨804189115721, 3, [(2, 3), (5, 1), (33469, 1), (600697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33469
    · exact prime_600697
  · decide +kernel

theorem prime_804189115733 : Nat.Prime 804189115733 := by
  apply nodeValid_prime [2, 409823, 490571] ⟨804189115733, 2, [(2, 2), (409823, 1), (490571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409823
    · exact prime_490571
  · decide +kernel

theorem prime_804189119677 : Nat.Prime 804189119677 := by
  apply nodeValid_prime [2, 3, 67015759973] ⟨804189119677, 2, [(2, 2), (3, 1), (67015759973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67015759973
  · decide +kernel

theorem prime_805314029269 : Nat.Prime 805314029269 := by
  apply nodeValid_prime [2, 3, 7, 383, 25031519] ⟨805314029269, 6, [(2, 2), (3, 1), (7, 1), (383, 1), (25031519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
    · exact prime_25031519
  · decide +kernel

theorem prime_805314029521 : Nat.Prime 805314029521 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 13, 31, 71, 1523] ⟨805314029521, 23, [(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (31, 1), (71, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_71
    · exact prime_1523
  · decide +kernel

theorem prime_805314035359 : Nat.Prime 805314035359 := by
  apply nodeValid_prime [2, 3, 7, 2130460411] ⟨805314035359, 3, [(2, 1), (3, 3), (7, 1), (2130460411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2130460411
  · decide +kernel

theorem prime_806440016693 : Nat.Prime 806440016693 := by
  apply nodeValid_prime [2, 201610004173] ⟨806440016693, 2, [(2, 2), (201610004173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_201610004173
  · decide +kernel

theorem prime_806440029817 : Nat.Prime 806440029817 := by
  apply nodeValid_prime [2, 3, 23, 113, 307, 1831] ⟨806440029817, 5, [(2, 3), (3, 1), (23, 2), (113, 1), (307, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_113
    · exact prime_307
    · exact prime_1831
  · decide +kernel

theorem prime_806440030051 : Nat.Prime 806440030051 := by
  apply nodeValid_prime [2, 3, 5, 5376266867] ⟨806440030051, 3, [(2, 1), (3, 1), (5, 2), (5376266867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5376266867
  · decide +kernel

theorem prime_807567061219 : Nat.Prime 807567061219 := by
  apply nodeValid_prime [2, 3, 29, 4641190007] ⟨807567061219, 3, [(2, 1), (3, 1), (29, 1), (4641190007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_4641190007
  · decide +kernel

theorem prime_807567090523 : Nat.Prime 807567090523 := by
  apply nodeValid_prime [2, 3, 503, 1087, 246167] ⟨807567090523, 3, [(2, 1), (3, 1), (503, 1), (1087, 1), (246167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
    · exact prime_1087
    · exact prime_246167
  · decide +kernel

theorem prime_807567090887 : Nat.Prime 807567090887 := by
  apply nodeValid_prime [2, 403783545443] ⟨807567090887, 5, [(2, 1), (403783545443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_403783545443
  · decide +kernel

theorem prime_808695156743 : Nat.Prime 808695156743 := by
  apply nodeValid_prime [2, 11, 36758870761] ⟨808695156743, 5, [(2, 1), (11, 1), (36758870761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_36758870761
  · decide +kernel

theorem prime_808695157973 : Nat.Prime 808695157973 := by
  apply nodeValid_prime [2, 13, 15551829961] ⟨808695157973, 2, [(2, 2), (13, 1), (15551829961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_15551829961
  · decide +kernel

theorem prime_808695175577 : Nat.Prime 808695175577 := by
  apply nodeValid_prime [2, 101086896947] ⟨808695175577, 3, [(2, 3), (101086896947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_101086896947
  · decide +kernel

theorem prime_809824353757 : Nat.Prime 809824353757 := by
  apply nodeValid_prime [2, 3, 11, 6135032983] ⟨809824353757, 2, [(2, 2), (3, 1), (11, 1), (6135032983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6135032983
  · decide +kernel

theorem prime_809824354013 : Nat.Prime 809824354013 := by
  apply nodeValid_prime [2, 202456088503] ⟨809824354013, 2, [(2, 2), (202456088503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_202456088503
  · decide +kernel

theorem prime_809824363417 : Nat.Prime 809824363417 := by
  apply nodeValid_prime [2, 3, 11247560603] ⟨809824363417, 5, [(2, 3), (3, 2), (11247560603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11247560603
  · decide +kernel

theorem prime_810954618967 : Nat.Prime 810954618967 := by
  apply nodeValid_prime [2, 3, 883, 1459, 11657] ⟨810954618967, 6, [(2, 1), (3, 3), (883, 1), (1459, 1), (11657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_883
    · exact prime_1459
    · exact prime_11657
  · decide +kernel

theorem prime_810954622279 : Nat.Prime 810954622279 := by
  apply nodeValid_prime [2, 3, 37, 1217649583] ⟨810954622279, 6, [(2, 1), (3, 2), (37, 1), (1217649583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1217649583
  · decide +kernel

theorem prime_810954623659 : Nat.Prime 810954623659 := by
  apply nodeValid_prime [2, 3, 23189, 5828587] ⟨810954623659, 2, [(2, 1), (3, 1), (23189, 1), (5828587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23189
    · exact prime_5828587
  · decide +kernel

theorem prime_812085938549 : Nat.Prime 812085938549 := by
  apply nodeValid_prime [2, 433, 468871789] ⟨812085938549, 2, [(2, 2), (433, 1), (468871789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_433
    · exact prime_468871789
  · decide +kernel

theorem prime_812085961403 : Nat.Prime 812085961403 := by
  apply nodeValid_prime [2, 97943, 4145707] ⟨812085961403, 2, [(2, 1), (97943, 1), (4145707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97943
    · exact prime_4145707
  · decide +kernel

theorem prime_812085961781 : Nat.Prime 812085961781 := by
  apply nodeValid_prime [2, 5, 967, 41989967] ⟨812085961781, 2, [(2, 2), (5, 1), (967, 1), (41989967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_967
    · exact prime_41989967
  · decide +kernel

theorem prime_813218330657 : Nat.Prime 813218330657 := by
  apply nodeValid_prime [2, 31, 819776543] ⟨813218330657, 3, [(2, 5), (31, 1), (819776543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_819776543
  · decide +kernel

theorem prime_813218437331 : Nat.Prime 813218437331 := by
  apply nodeValid_prime [2, 5, 13, 79, 337, 234967] ⟨813218437331, 2, [(2, 1), (5, 1), (13, 1), (79, 1), (337, 1), (234967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_79
    · exact prime_337
    · exact prime_234967
  · decide +kernel

theorem prime_813218437351 : Nat.Prime 813218437351 := by
  apply nodeValid_prime [2, 3, 5, 11, 223, 353, 2087] ⟨813218437351, 3, [(2, 1), (3, 2), (5, 2), (11, 1), (223, 1), (353, 1), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_223
    · exact prime_353
    · exact prime_2087
  · decide +kernel

theorem prime_814351790249 : Nat.Prime 814351790249 := by
  apply nodeValid_prime [2, 23, 73, 60627739] ⟨814351790249, 3, [(2, 3), (23, 1), (73, 1), (60627739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_73
    · exact prime_60627739
  · decide +kernel

theorem prime_814351860563 : Nat.Prime 814351860563 := by
  apply nodeValid_prime [2, 407175930281] ⟨814351860563, 2, [(2, 1), (407175930281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_407175930281
  · decide +kernel

theorem prime_814351860587 : Nat.Prime 814351860587 := by
  apply nodeValid_prime [2, 11, 305917303] ⟨814351860587, 2, [(2, 1), (11, 3), (305917303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_305917303
  · decide +kernel

theorem prime_815486261353 : Nat.Prime 815486261353 := by
  apply nodeValid_prime [2, 3, 7, 4854084889] ⟨815486261353, 5, [(2, 3), (3, 1), (7, 1), (4854084889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4854084889
  · decide +kernel

theorem prime_815486261813 : Nat.Prime 815486261813 := by
  apply nodeValid_prime [2, 1499, 136005047] ⟨815486261813, 2, [(2, 2), (1499, 1), (136005047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1499
    · exact prime_136005047
  · decide +kernel

theorem prime_815486310227 : Nat.Prime 815486310227 := by
  apply nodeValid_prime [2, 7, 29, 47, 42735893] ⟨815486310227, 2, [(2, 1), (7, 1), (29, 1), (47, 1), (42735893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_47
    · exact prime_42735893
  · decide +kernel

theorem prime_816621849031 : Nat.Prime 816621849031 := by
  apply nodeValid_prime [2, 3, 5, 13, 211, 9923707] ⟨816621849031, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (211, 1), (9923707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_211
    · exact prime_9923707
  · decide +kernel

theorem prime_816621849181 : Nat.Prime 816621849181 := by
  apply nodeValid_prime [2, 3, 5, 83, 54660097] ⟨816621849181, 2, [(2, 2), (3, 2), (5, 1), (83, 1), (54660097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_54660097
  · decide +kernel

theorem prime_816621893761 : Nat.Prime 816621893761 := by
  apply nodeValid_prime [2, 3, 5, 61, 769, 9067] ⟨816621893761, 19, [(2, 7), (3, 1), (5, 1), (61, 1), (769, 1), (9067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_769
    · exact prime_9067
  · decide +kernel

theorem prime_817758440827 : Nat.Prime 817758440827 := by
  apply nodeValid_prime [2, 3, 101, 131, 10301041] ⟨817758440827, 2, [(2, 1), (3, 1), (101, 1), (131, 1), (10301041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_131
    · exact prime_10301041
  · decide +kernel

theorem prime_817758442717 : Nat.Prime 817758442717 := by
  apply nodeValid_prime [2, 3, 68146536893] ⟨817758442717, 2, [(2, 2), (3, 1), (68146536893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_68146536893
  · decide +kernel

theorem prime_817758542639 : Nat.Prime 817758542639 := by
  apply nodeValid_prime [2, 59, 181, 38288161] ⟨817758542639, 17, [(2, 1), (59, 1), (181, 1), (38288161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_181
    · exact prime_38288161
  · decide +kernel

theorem prime_818896264463 : Nat.Prime 818896264463 := by
  apply nodeValid_prime [2, 409448132231] ⟨818896264463, 5, [(2, 1), (409448132231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_409448132231
  · decide +kernel

theorem prime_818896279567 : Nat.Prime 818896279567 := by
  apply nodeValid_prime [2, 3, 136482713261] ⟨818896279567, 3, [(2, 1), (3, 1), (136482713261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_136482713261
  · decide +kernel

theorem prime_818896279583 : Nat.Prime 818896279583 := by
  apply nodeValid_prime [2, 409448139791] ⟨818896279583, 5, [(2, 1), (409448139791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_409448139791
  · decide +kernel

theorem prime_820035028789 : Nat.Prime 820035028789 := by
  apply nodeValid_prime [2, 3, 47, 1453962817] ⟨820035028789, 2, [(2, 2), (3, 1), (47, 1), (1453962817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_1453962817
  · decide +kernel

theorem prime_820035029813 : Nat.Prime 820035029813 := by
  apply nodeValid_prime [2, 205008757453] ⟨820035029813, 2, [(2, 2), (205008757453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_205008757453
  · decide +kernel

theorem prime_820035057533 : Nat.Prime 820035057533 := by
  apply nodeValid_prime [2, 139, 1474883197] ⟨820035057533, 2, [(2, 2), (139, 1), (1474883197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_1474883197
  · decide +kernel

theorem prime_821174922787 : Nat.Prime 821174922787 := by
  apply nodeValid_prime [2, 3, 1033, 7219, 18353] ⟨821174922787, 3, [(2, 1), (3, 1), (1033, 1), (7219, 1), (18353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
    · exact prime_7219
    · exact prime_18353
  · decide +kernel

theorem prime_821174937923 : Nat.Prime 821174937923 := by
  apply nodeValid_prime [2, 151, 2719122311] ⟨821174937923, 2, [(2, 1), (151, 1), (2719122311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_2719122311
  · decide +kernel

theorem prime_821174938369 : Nat.Prime 821174938369 := by
  apply nodeValid_prime [2, 3, 28277, 37813] ⟨821174938369, 13, [(2, 8), (3, 1), (28277, 1), (37813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28277
    · exact prime_37813
  · decide +kernel

theorem prime_822315816061 : Nat.Prime 822315816061 := by
  apply nodeValid_prime [2, 3, 5, 73, 187743337] ⟨822315816061, 2, [(2, 2), (3, 1), (5, 1), (73, 1), (187743337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_187743337
  · decide +kernel

theorem prime_822315816499 : Nat.Prime 822315816499 := by
  apply nodeValid_prime [2, 3, 11, 73, 229, 811, 919] ⟨822315816499, 3, [(2, 1), (3, 1), (11, 1), (73, 1), (229, 1), (811, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_229
    · exact prime_811
    · exact prime_919
  · decide +kernel

theorem prime_822315855133 : Nat.Prime 822315855133 := by
  apply nodeValid_prime [2, 3, 6203, 3682429] ⟨822315855133, 2, [(2, 2), (3, 2), (6203, 1), (3682429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6203
    · exact prime_3682429
  · decide +kernel

theorem prime_823457858903 : Nat.Prime 823457858903 := by
  apply nodeValid_prime [2, 7, 41, 53, 27067841] ⟨823457858903, 5, [(2, 1), (7, 1), (41, 1), (53, 1), (27067841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_53
    · exact prime_27067841
  · decide +kernel

theorem prime_823457911853 : Nat.Prime 823457911853 := by
  apply nodeValid_prime [2, 211, 975661033] ⟨823457911853, 2, [(2, 2), (211, 1), (975661033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_975661033
  · decide +kernel

theorem prime_823457911931 : Nat.Prime 823457911931 := by
  apply nodeValid_prime [2, 5, 23, 3580251791] ⟨823457911931, 2, [(2, 1), (5, 1), (23, 1), (3580251791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_3580251791
  · decide +kernel

theorem prime_824600934569 : Nat.Prime 824600934569 := by
  apply nodeValid_prime [2, 4297, 23987693] ⟨824600934569, 3, [(2, 3), (4297, 1), (23987693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4297
    · exact prime_23987693
  · decide +kernel

theorem prime_824600994149 : Nat.Prime 824600994149 := by
  apply nodeValid_prime [2, 1223, 168561119] ⟨824600994149, 2, [(2, 2), (1223, 1), (168561119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1223
    · exact prime_168561119
  · decide +kernel

theorem prime_824600994383 : Nat.Prime 824600994383 := by
  apply nodeValid_prime [2, 11, 17, 401, 503, 643] ⟨824600994383, 5, [(2, 1), (11, 1), (17, 2), (401, 1), (503, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_401
    · exact prime_503
    · exact prime_643
  · decide +kernel

theorem prime_825745081829 : Nat.Prime 825745081829 := by
  apply nodeValid_prime [2, 37, 43, 129752527] ⟨825745081829, 2, [(2, 2), (37, 1), (43, 1), (129752527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
    · exact prime_129752527
  · decide +kernel

theorem prime_825745115567 : Nat.Prime 825745115567 := by
  apply nodeValid_prime [2, 7, 171958583] ⟨825745115567, 5, [(2, 1), (7, 4), (171958583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_171958583
  · decide +kernel

theorem prime_825745116767 : Nat.Prime 825745116767 := by
  apply nodeValid_prime [2, 73, 5655788471] ⟨825745116767, 5, [(2, 1), (73, 1), (5655788471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_5655788471
  · decide +kernel

theorem prime_826890273487 : Nat.Prime 826890273487 := by
  apply nodeValid_prime [2, 3, 41647, 1103041] ⟨826890273487, 3, [(2, 1), (3, 2), (41647, 1), (1103041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41647
    · exact prime_1103041
  · decide +kernel

theorem prime_826890274381 : Nat.Prime 826890274381 := by
  apply nodeValid_prime [2, 3, 5, 23, 599195851] ⟨826890274381, 2, [(2, 2), (3, 1), (5, 1), (23, 1), (599195851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_599195851
  · decide +kernel

theorem prime_826890292069 : Nat.Prime 826890292069 := by
  apply nodeValid_prime [2, 3, 52027, 1324457] ⟨826890292069, 6, [(2, 2), (3, 1), (52027, 1), (1324457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52027
    · exact prime_1324457
  · decide +kernel

end Sude.Lucas.Generated
