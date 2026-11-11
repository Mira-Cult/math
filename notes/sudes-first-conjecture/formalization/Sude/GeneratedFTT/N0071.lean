import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0063

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5669 : Nat.Prime 5669 := by
  apply nodeValid_prime [2, 13, 109] ⟨5669, 3, [(2, 2), (13, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_109
  · decide +kernel

theorem prime_6791 : Nat.Prime 6791 := by
  apply nodeValid_prime [2, 5, 7, 97] ⟨6791, 7, [(2, 1), (5, 1), (7, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_97
  · decide +kernel

theorem prime_7919 : Nat.Prime 7919 := by
  apply nodeValid_prime [2, 37, 107] ⟨7919, 7, [(2, 1), (37, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_107
  · decide +kernel

theorem prime_8101 : Nat.Prime 8101 := by
  apply nodeValid_prime [2, 3, 5] ⟨8101, 6, [(2, 2), (3, 4), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_12721 : Nat.Prime 12721 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨12721, 13, [(2, 4), (3, 1), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_13421 : Nat.Prime 13421 := by
  apply nodeValid_prime [2, 5, 11, 61] ⟨13421, 10, [(2, 2), (5, 1), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_18521 : Nat.Prime 18521 := by
  apply nodeValid_prime [2, 5, 463] ⟨18521, 3, [(2, 3), (5, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_463
  · decide +kernel

theorem prime_21517 : Nat.Prime 21517 := by
  apply nodeValid_prime [2, 3, 11, 163] ⟨21517, 5, [(2, 2), (3, 1), (11, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_163
  · decide +kernel

theorem prime_22391 : Nat.Prime 22391 := by
  apply nodeValid_prime [2, 5, 2239] ⟨22391, 13, [(2, 1), (5, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2239
  · decide +kernel

theorem prime_28813 : Nat.Prime 28813 := by
  apply nodeValid_prime [2, 3, 7] ⟨28813, 2, [(2, 2), (3, 1), (7, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_30307 : Nat.Prime 30307 := by
  apply nodeValid_prime [2, 3, 5051] ⟨30307, 2, [(2, 1), (3, 1), (5051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5051
  · decide +kernel

theorem prime_30671 : Nat.Prime 30671 := by
  apply nodeValid_prime [2, 5, 3067] ⟨30671, 11, [(2, 1), (5, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3067
  · decide +kernel

theorem prime_32503 : Nat.Prime 32503 := by
  apply nodeValid_prime [2, 3, 5417] ⟨32503, 3, [(2, 1), (3, 1), (5417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5417
  · decide +kernel

theorem prime_35311 : Nat.Prime 35311 := by
  apply nodeValid_prime [2, 3, 5, 11, 107] ⟨35311, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_107
  · decide +kernel

theorem prime_36943 : Nat.Prime 36943 := by
  apply nodeValid_prime [2, 3, 47, 131] ⟨36943, 3, [(2, 1), (3, 1), (47, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_131
  · decide +kernel

theorem prime_39139 : Nat.Prime 39139 := by
  apply nodeValid_prime [2, 3, 11, 593] ⟨39139, 7, [(2, 1), (3, 1), (11, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_593
  · decide +kernel

theorem prime_40823 : Nat.Prime 40823 := by
  apply nodeValid_prime [2, 20411] ⟨40823, 5, [(2, 1), (20411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20411
  · decide +kernel

theorem prime_48767 : Nat.Prime 48767 := by
  apply nodeValid_prime [2, 37, 659] ⟨48767, 5, [(2, 1), (37, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_659
  · decide +kernel

theorem prime_49811 : Nat.Prime 49811 := by
  apply nodeValid_prime [2, 5, 17, 293] ⟨49811, 6, [(2, 1), (5, 1), (17, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_293
  · decide +kernel

theorem prime_54371 : Nat.Prime 54371 := by
  apply nodeValid_prime [2, 5, 5437] ⟨54371, 6, [(2, 1), (5, 1), (5437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5437
  · decide +kernel

theorem prime_55021 : Nat.Prime 55021 := by
  apply nodeValid_prime [2, 3, 5, 7, 131] ⟨55021, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_131
  · decide +kernel

theorem prime_58147 : Nat.Prime 58147 := by
  apply nodeValid_prime [2, 3, 11, 881] ⟨58147, 3, [(2, 1), (3, 1), (11, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_881
  · decide +kernel

theorem prime_64483 : Nat.Prime 64483 := by
  apply nodeValid_prime [2, 3, 11, 977] ⟨64483, 2, [(2, 1), (3, 1), (11, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_977
  · decide +kernel

theorem prime_71333 : Nat.Prime 71333 := by
  apply nodeValid_prime [2, 17, 1049] ⟨71333, 2, [(2, 2), (17, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1049
  · decide +kernel

theorem prime_78439 : Nat.Prime 78439 := by
  apply nodeValid_prime [2, 3, 17, 769] ⟨78439, 6, [(2, 1), (3, 1), (17, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_769
  · decide +kernel

theorem prime_81019 : Nat.Prime 81019 := by
  apply nodeValid_prime [2, 3, 7, 643] ⟨81019, 2, [(2, 1), (3, 2), (7, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_643
  · decide +kernel

theorem prime_83383 : Nat.Prime 83383 := by
  apply nodeValid_prime [2, 3, 13, 1069] ⟨83383, 3, [(2, 1), (3, 1), (13, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1069
  · decide +kernel

theorem prime_83761 : Nat.Prime 83761 := by
  apply nodeValid_prime [2, 3, 5, 349] ⟨83761, 11, [(2, 4), (3, 1), (5, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_85159 : Nat.Prime 85159 := by
  apply nodeValid_prime [2, 3, 19, 83] ⟨85159, 3, [(2, 1), (3, 3), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_89597 : Nat.Prime 89597 := by
  apply nodeValid_prime [2, 13, 1723] ⟨89597, 2, [(2, 2), (13, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1723
  · decide +kernel

theorem prime_91639 : Nat.Prime 91639 := by
  apply nodeValid_prime [2, 3, 1697] ⟨91639, 3, [(2, 1), (3, 3), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1697
  · decide +kernel

theorem prime_98299 : Nat.Prime 98299 := by
  apply nodeValid_prime [2, 3, 43, 127] ⟨98299, 2, [(2, 1), (3, 2), (43, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_127
  · decide +kernel

theorem prime_100943 : Nat.Prime 100943 := by
  apply nodeValid_prime [2, 41, 1231] ⟨100943, 5, [(2, 1), (41, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1231
  · decide +kernel

theorem prime_102161 : Nat.Prime 102161 := by
  apply nodeValid_prime [2, 5, 1277] ⟨102161, 6, [(2, 4), (5, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1277
  · decide +kernel

theorem prime_112337 : Nat.Prime 112337 := by
  apply nodeValid_prime [2, 7, 17, 59] ⟨112337, 3, [(2, 4), (7, 1), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_116159 : Nat.Prime 116159 := by
  apply nodeValid_prime [2, 7, 8297] ⟨116159, 7, [(2, 1), (7, 1), (8297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8297
  · decide +kernel

theorem prime_116531 : Nat.Prime 116531 := by
  apply nodeValid_prime [2, 5, 43, 271] ⟨116531, 2, [(2, 1), (5, 1), (43, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_271
  · decide +kernel

theorem prime_118043 : Nat.Prime 118043 := by
  apply nodeValid_prime [2, 59021] ⟨118043, 2, [(2, 1), (59021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59021
  · decide +kernel

theorem prime_138401 : Nat.Prime 138401 := by
  apply nodeValid_prime [2, 5, 173] ⟨138401, 3, [(2, 5), (5, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_148091 : Nat.Prime 148091 := by
  apply nodeValid_prime [2, 5, 59, 251] ⟨148091, 2, [(2, 1), (5, 1), (59, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_251
  · decide +kernel

theorem prime_156941 : Nat.Prime 156941 := by
  apply nodeValid_prime [2, 5, 7, 19, 59] ⟨156941, 2, [(2, 2), (5, 1), (7, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_227281 : Nat.Prime 227281 := by
  apply nodeValid_prime [2, 3, 5, 947] ⟨227281, 7, [(2, 4), (3, 1), (5, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_947
  · decide +kernel

theorem prime_236087 : Nat.Prime 236087 := by
  apply nodeValid_prime [2, 118043] ⟨236087, 5, [(2, 1), (118043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_118043
  · decide +kernel

theorem prime_237571 : Nat.Prime 237571 := by
  apply nodeValid_prime [2, 3, 5, 7919] ⟨237571, 2, [(2, 1), (3, 1), (5, 1), (7919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7919
  · decide +kernel

theorem prime_247201 : Nat.Prime 247201 := by
  apply nodeValid_prime [2, 3, 5, 103] ⟨247201, 7, [(2, 5), (3, 1), (5, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_279397 : Nat.Prime 279397 := by
  apply nodeValid_prime [2, 3, 13, 199] ⟨279397, 2, [(2, 2), (3, 3), (13, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_199
  · decide +kernel

theorem prime_305407 : Nat.Prime 305407 := by
  apply nodeValid_prime [2, 3, 19, 47] ⟨305407, 3, [(2, 1), (3, 2), (19, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_339137 : Nat.Prime 339137 := by
  apply nodeValid_prime [2, 7, 757] ⟨339137, 5, [(2, 6), (7, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_757
  · decide +kernel

theorem prime_365119 : Nat.Prime 365119 := by
  apply nodeValid_prime [2, 3, 13, 31, 151] ⟨365119, 3, [(2, 1), (3, 1), (13, 1), (31, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_151
  · decide +kernel

theorem prime_450199 : Nat.Prime 450199 := by
  apply nodeValid_prime [2, 3, 7, 397] ⟨450199, 3, [(2, 1), (3, 4), (7, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_397
  · decide +kernel

theorem prime_467003 : Nat.Prime 467003 := by
  apply nodeValid_prime [2, 103, 2267] ⟨467003, 2, [(2, 1), (103, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_2267
  · decide +kernel

theorem prime_545203 : Nat.Prime 545203 := by
  apply nodeValid_prime [2, 3, 7, 4327] ⟨545203, 3, [(2, 1), (3, 2), (7, 1), (4327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4327
  · decide +kernel

theorem prime_561061 : Nat.Prime 561061 := by
  apply nodeValid_prime [2, 3, 5, 1039] ⟨561061, 2, [(2, 2), (3, 3), (5, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1039
  · decide +kernel

theorem prime_682739 : Nat.Prime 682739 := by
  apply nodeValid_prime [2, 7, 48767] ⟨682739, 2, [(2, 1), (7, 1), (48767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_48767
  · decide +kernel

theorem prime_702329 : Nat.Prime 702329 := by
  apply nodeValid_prime [2, 11, 23, 347] ⟨702329, 3, [(2, 3), (11, 1), (23, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_347
  · decide +kernel

theorem prime_837611 : Nat.Prime 837611 := by
  apply nodeValid_prime [2, 5, 83761] ⟨837611, 2, [(2, 1), (5, 1), (83761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83761
  · decide +kernel

theorem prime_984757 : Nat.Prime 984757 := by
  apply nodeValid_prime [2, 3, 137, 599] ⟨984757, 2, [(2, 2), (3, 1), (137, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_599
  · decide +kernel

theorem prime_1068887 : Nat.Prime 1068887 := by
  apply nodeValid_prime [2, 7, 13, 839] ⟨1068887, 7, [(2, 1), (7, 2), (13, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_839
  · decide +kernel

theorem prime_1168399 : Nat.Prime 1168399 := by
  apply nodeValid_prime [2, 3, 7, 11, 281] ⟨1168399, 11, [(2, 1), (3, 3), (7, 1), (11, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_281
  · decide +kernel

theorem prime_1225933 : Nat.Prime 1225933 := by
  apply nodeValid_prime [2, 3, 102161] ⟨1225933, 2, [(2, 2), (3, 1), (102161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102161
  · decide +kernel

theorem prime_1253401 : Nat.Prime 1253401 := by
  apply nodeValid_prime [2, 3, 5, 2089] ⟨1253401, 11, [(2, 3), (3, 1), (5, 2), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2089
  · decide +kernel

theorem prime_1673663 : Nat.Prime 1673663 := by
  apply nodeValid_prime [2, 283, 2957] ⟨1673663, 5, [(2, 1), (283, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_2957
  · decide +kernel

theorem prime_1676383 : Nat.Prime 1676383 := by
  apply nodeValid_prime [2, 3, 279397] ⟨1676383, 3, [(2, 1), (3, 1), (279397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_279397
  · decide +kernel

theorem prime_1907713 : Nat.Prime 1907713 := by
  apply nodeValid_prime [2, 3, 23] ⟨1907713, 5, [(2, 10), (3, 4), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_2013001 : Nat.Prime 2013001 := by
  apply nodeValid_prime [2, 3, 5, 11, 61] ⟨2013001, 19, [(2, 3), (3, 1), (5, 3), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_2022067 : Nat.Prime 2022067 := by
  apply nodeValid_prime [2, 3, 112337] ⟨2022067, 2, [(2, 1), (3, 2), (112337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_112337
  · decide +kernel

theorem prime_3347327 : Nat.Prime 3347327 := by
  apply nodeValid_prime [2, 1673663] ⟨3347327, 5, [(2, 1), (1673663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1673663
  · decide +kernel

theorem prime_3366367 : Nat.Prime 3366367 := by
  apply nodeValid_prime [2, 3, 561061] ⟨3366367, 3, [(2, 1), (3, 1), (561061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_561061
  · decide +kernel

theorem prime_3424901 : Nat.Prime 3424901 := by
  apply nodeValid_prime [2, 5, 29, 1181] ⟨3424901, 3, [(2, 2), (5, 2), (29, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_1181
  · decide +kernel

theorem prime_4667539 : Nat.Prime 4667539 := by
  apply nodeValid_prime [2, 3, 881, 883] ⟨4667539, 2, [(2, 1), (3, 1), (881, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_881
    · exact prime_883
  · decide +kernel

theorem prime_4903733 : Nat.Prime 4903733 := by
  apply nodeValid_prime [2, 1225933] ⟨4903733, 2, [(2, 2), (1225933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1225933
  · decide +kernel

theorem prime_5238293 : Nat.Prime 5238293 := by
  apply nodeValid_prime [2, 107, 12239] ⟨5238293, 2, [(2, 2), (107, 1), (12239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_12239
  · decide +kernel

theorem prime_5765471 : Nat.Prime 5765471 := by
  apply nodeValid_prime [2, 5, 251, 2297] ⟨5765471, 19, [(2, 1), (5, 1), (251, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
    · exact prime_2297
  · decide +kernel

theorem prime_6073493 : Nat.Prime 6073493 := by
  apply nodeValid_prime [2, 43, 35311] ⟨6073493, 2, [(2, 2), (43, 1), (35311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_35311
  · decide +kernel

theorem prime_7129673 : Nat.Prime 7129673 := by
  apply nodeValid_prime [2, 11, 81019] ⟨7129673, 3, [(2, 3), (11, 1), (81019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_81019
  · decide +kernel

theorem prime_7924109 : Nat.Prime 7924109 := by
  apply nodeValid_prime [2, 17, 116531] ⟨7924109, 2, [(2, 2), (17, 1), (116531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_116531
  · decide +kernel

theorem prime_10495339 : Nat.Prime 10495339 := by
  apply nodeValid_prime [2, 3, 7, 283, 883] ⟨10495339, 10, [(2, 1), (3, 1), (7, 1), (283, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
    · exact prime_883
  · decide +kernel

theorem prime_11825117 : Nat.Prime 11825117 := by
  apply nodeValid_prime [2, 1433, 2063] ⟨11825117, 2, [(2, 2), (1433, 1), (2063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1433
    · exact prime_2063
  · decide +kernel

theorem prime_13007749 : Nat.Prime 13007749 := by
  apply nodeValid_prime [2, 3, 13, 83383] ⟨13007749, 2, [(2, 2), (3, 1), (13, 1), (83383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83383
  · decide +kernel

theorem prime_14106839 : Nat.Prime 14106839 := by
  apply nodeValid_prime [2, 17, 43, 9649] ⟨14106839, 13, [(2, 1), (17, 1), (43, 1), (9649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_43
    · exact prime_9649
  · decide +kernel

theorem prime_14524369 : Nat.Prime 14524369 := by
  apply nodeValid_prime [2, 3, 31, 43, 227] ⟨14524369, 7, [(2, 4), (3, 1), (31, 1), (43, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
    · exact prime_227
  · decide +kernel

theorem prime_16315267 : Nat.Prime 16315267 := by
  apply nodeValid_prime [2, 3, 11, 247201] ⟨16315267, 3, [(2, 1), (3, 1), (11, 1), (247201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_247201
  · decide +kernel

theorem prime_19077131 : Nat.Prime 19077131 := by
  apply nodeValid_prime [2, 5, 1907713] ⟨19077131, 6, [(2, 1), (5, 1), (1907713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1907713
  · decide +kernel

theorem prime_22900357 : Nat.Prime 22900357 := by
  apply nodeValid_prime [2, 3, 173, 3677] ⟨22900357, 2, [(2, 2), (3, 2), (173, 1), (3677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_3677
  · decide +kernel

theorem prime_34384261 : Nat.Prime 34384261 := by
  apply nodeValid_prime [2, 3, 5, 47, 89, 137] ⟨34384261, 6, [(2, 2), (3, 1), (5, 1), (47, 1), (89, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_89
    · exact prime_137
  · decide +kernel

theorem prime_45051901 : Nat.Prime 45051901 := by
  apply nodeValid_prime [2, 3, 5, 263, 571] ⟨45051901, 2, [(2, 2), (3, 1), (5, 2), (263, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
    · exact prime_571
  · decide +kernel

theorem prime_50782789 : Nat.Prime 50782789 := by
  apply nodeValid_prime [2, 3, 7, 22391] ⟨50782789, 6, [(2, 2), (3, 4), (7, 1), (22391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_22391
  · decide +kernel

theorem prime_55187623 : Nat.Prime 55187623 := by
  apply nodeValid_prime [2, 3, 7, 20857] ⟨55187623, 5, [(2, 1), (3, 3), (7, 2), (20857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_20857
  · decide +kernel

theorem prime_81050869 : Nat.Prime 81050869 := by
  apply nodeValid_prime [2, 3, 37, 6761] ⟨81050869, 2, [(2, 2), (3, 4), (37, 1), (6761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_6761
  · decide +kernel

theorem prime_119262277 : Nat.Prime 119262277 := by
  apply nodeValid_prime [2, 3, 7, 17, 41, 97] ⟨119262277, 2, [(2, 2), (3, 2), (7, 2), (17, 1), (41, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_41
    · exact prime_97
  · decide +kernel

theorem prime_164160287 : Nat.Prime 164160287 := by
  apply nodeValid_prime [2, 523, 156941] ⟨164160287, 5, [(2, 1), (523, 1), (156941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_523
    · exact prime_156941
  · decide +kernel

theorem prime_229315447 : Nat.Prime 229315447 := by
  apply nodeValid_prime [2, 3, 19, 257, 2609] ⟨229315447, 5, [(2, 1), (3, 2), (19, 1), (257, 1), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_257
    · exact prime_2609
  · decide +kernel

theorem prime_265183679 : Nat.Prime 265183679 := by
  apply nodeValid_prime [2, 7159, 18521] ⟨265183679, 13, [(2, 1), (7159, 1), (18521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7159
    · exact prime_18521
  · decide +kernel

theorem prime_308336647 : Nat.Prime 308336647 := by
  apply nodeValid_prime [2, 3, 41, 1253401] ⟨308336647, 3, [(2, 1), (3, 1), (41, 1), (1253401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1253401
  · decide +kernel

theorem prime_375691703 : Nat.Prime 375691703 := by
  apply nodeValid_prime [2, 139, 199, 6791] ⟨375691703, 5, [(2, 1), (139, 1), (199, 1), (6791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_199
    · exact prime_6791
  · decide +kernel

theorem prime_431206879 : Nat.Prime 431206879 := by
  apply nodeValid_prime [2, 3, 3083, 23311] ⟨431206879, 3, [(2, 1), (3, 1), (3083, 1), (23311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3083
    · exact prime_23311
  · decide +kernel

theorem prime_531839569 : Nat.Prime 531839569 := by
  apply nodeValid_prime [2, 3, 13, 67, 12721] ⟨531839569, 11, [(2, 4), (3, 1), (13, 1), (67, 1), (12721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
    · exact prime_12721
  · decide +kernel

theorem prime_559378279 : Nat.Prime 559378279 := by
  apply nodeValid_prime [2, 3, 19, 545203] ⟨559378279, 3, [(2, 1), (3, 3), (19, 1), (545203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_545203
  · decide +kernel

theorem prime_560199901 : Nat.Prime 560199901 := by
  apply nodeValid_prime [2, 3, 5, 13, 379] ⟨560199901, 6, [(2, 2), (3, 1), (5, 2), (13, 1), (379, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_379
  · decide +kernel

theorem prime_607641989 : Nat.Prime 607641989 := by
  apply nodeValid_prime [2, 29, 5238293] ⟨607641989, 2, [(2, 2), (29, 1), (5238293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_5238293
  · decide +kernel

theorem prime_700853341 : Nat.Prime 700853341 := by
  apply nodeValid_prime [2, 3, 5, 11, 281, 3779] ⟨700853341, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (281, 1), (3779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_281
    · exact prime_3779
  · decide +kernel

theorem prime_863864671 : Nat.Prime 863864671 := by
  apply nodeValid_prime [2, 3, 5, 41, 702329] ⟨863864671, 6, [(2, 1), (3, 1), (5, 1), (41, 1), (702329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_702329
  · decide +kernel

theorem prime_868444009 : Nat.Prime 868444009 := by
  apply nodeValid_prime [2, 3, 53, 682739] ⟨868444009, 7, [(2, 3), (3, 1), (53, 1), (682739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_682739
  · decide +kernel

theorem prime_883001969 : Nat.Prime 883001969 := by
  apply nodeValid_prime [2, 55187623] ⟨883001969, 3, [(2, 4), (55187623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_55187623
  · decide +kernel

theorem prime_885994237 : Nat.Prime 885994237 := by
  apply nodeValid_prime [2, 3, 17, 85159] ⟨885994237, 6, [(2, 2), (3, 2), (17, 2), (85159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_85159
  · decide +kernel

theorem prime_1002486343 : Nat.Prime 1002486343 := by
  apply nodeValid_prime [2, 3, 11, 13, 1168399] ⟨1002486343, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (1168399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1168399
  · decide +kernel

theorem prime_1051489247 : Nat.Prime 1051489247 := by
  apply nodeValid_prime [2, 2213, 237571] ⟨1051489247, 5, [(2, 1), (2213, 1), (237571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2213
    · exact prime_237571
  · decide +kernel

theorem prime_2121693361 : Nat.Prime 2121693361 := by
  apply nodeValid_prime [2, 3, 5, 29, 223, 1367] ⟨2121693361, 11, [(2, 4), (3, 1), (5, 1), (29, 1), (223, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_223
    · exact prime_1367
  · decide +kernel

theorem prime_2979274591 : Nat.Prime 2979274591 := by
  apply nodeValid_prime [2, 3, 5, 397, 83383] ⟨2979274591, 3, [(2, 1), (3, 2), (5, 1), (397, 1), (83383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_397
    · exact prime_83383
  · decide +kernel

theorem prime_5304233321 : Nat.Prime 5304233321 := by
  apply nodeValid_prime [2, 5, 23, 5765471] ⟨5304233321, 3, [(2, 3), (5, 1), (23, 1), (5765471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_5765471
  · decide +kernel

theorem prime_6389180803 : Nat.Prime 6389180803 := by
  apply nodeValid_prime [2, 3, 71, 863, 1931] ⟨6389180803, 2, [(2, 1), (3, 3), (71, 1), (863, 1), (1931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_863
    · exact prime_1931
  · decide +kernel

theorem prime_9790206917 : Nat.Prime 9790206917 := by
  apply nodeValid_prime [2, 7, 1031, 339137] ⟨9790206917, 3, [(2, 2), (7, 1), (1031, 1), (339137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1031
    · exact prime_339137
  · decide +kernel

theorem prime_10608466643 : Nat.Prime 10608466643 := by
  apply nodeValid_prime [2, 5304233321] ⟨10608466643, 2, [(2, 1), (5304233321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5304233321
  · decide +kernel

theorem prime_11453679767 : Nat.Prime 11453679767 := by
  apply nodeValid_prime [2, 149, 661, 58147] ⟨11453679767, 5, [(2, 1), (149, 1), (661, 1), (58147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_661
    · exact prime_58147
  · decide +kernel

theorem prime_78321655337 : Nat.Prime 78321655337 := by
  apply nodeValid_prime [2, 9790206917] ⟨78321655337, 3, [(2, 3), (9790206917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9790206917
  · decide +kernel

theorem prime_99232977247 : Nat.Prime 99232977247 := by
  apply nodeValid_prime [2, 3, 13, 37, 34384261] ⟨99232977247, 3, [(2, 1), (3, 1), (13, 1), (37, 1), (34384261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_34384261
  · decide +kernel

theorem prime_113027549897 : Nat.Prime 113027549897 := by
  apply nodeValid_prime [2, 43, 8101, 40559] ⟨113027549897, 3, [(2, 3), (43, 1), (8101, 1), (40559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_8101
    · exact prime_40559
  · decide +kernel

theorem prime_132013746521 : Nat.Prime 132013746521 := by
  apply nodeValid_prime [2, 5, 173, 19077131] ⟨132013746521, 7, [(2, 3), (5, 1), (173, 1), (19077131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_19077131
  · decide +kernel

theorem prime_155585880481 : Nat.Prime 155585880481 := by
  apply nodeValid_prime [2, 3, 5, 233, 577, 2411] ⟨155585880481, 7, [(2, 5), (3, 1), (5, 1), (233, 1), (577, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233
    · exact prime_577
    · exact prime_2411
  · decide +kernel

theorem prime_157883117347 : Nat.Prime 157883117347 := by
  apply nodeValid_prime [2, 3, 67, 1669, 78439] ⟨157883117347, 3, [(2, 1), (3, 2), (67, 1), (1669, 1), (78439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1669
    · exact prime_78439
  · decide +kernel

theorem prime_198465956267 : Nat.Prime 198465956267 := by
  apply nodeValid_prime [2, 100769, 984757] ⟨198465956267, 2, [(2, 1), (100769, 1), (984757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_100769
    · exact prime_984757
  · decide +kernel

theorem prime_388964695027 : Nat.Prime 388964695027 := by
  apply nodeValid_prime [2, 3, 17, 19, 43, 4667539] ⟨388964695027, 3, [(2, 1), (3, 1), (17, 1), (19, 1), (43, 1), (4667539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_43
    · exact prime_4667539
  · decide +kernel

theorem prime_394263996367 : Nat.Prime 394263996367 := by
  apply nodeValid_prime [2, 3, 269, 2437, 100237] ⟨394263996367, 3, [(2, 1), (3, 1), (269, 1), (2437, 1), (100237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_2437
    · exact prime_100237
  · decide +kernel

theorem prime_780569942843 : Nat.Prime 780569942843 := by
  apply nodeValid_prime [2, 131, 2979274591] ⟨780569942843, 2, [(2, 1), (131, 1), (2979274591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_2979274591
  · decide +kernel

theorem prime_1547083853167 : Nat.Prime 1547083853167 := by
  apply nodeValid_prime [2, 3, 179, 12401, 116159] ⟨1547083853167, 3, [(2, 1), (3, 1), (179, 1), (12401, 1), (116159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_12401
    · exact prime_116159
  · decide +kernel

theorem prime_1547083866547 : Nat.Prime 1547083866547 := by
  apply nodeValid_prime [2, 3, 42697, 2013001] ⟨1547083866547, 3, [(2, 1), (3, 2), (42697, 1), (2013001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42697
    · exact prime_2013001
  · decide +kernel

theorem prime_1547083870987 : Nat.Prime 1547083870987 := by
  apply nodeValid_prime [2, 3, 19, 91639, 148091] ⟨1547083870987, 3, [(2, 1), (3, 1), (19, 1), (91639, 1), (148091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_91639
    · exact prime_148091
  · decide +kernel

theorem prime_1548836129429 : Nat.Prime 1548836129429 := by
  apply nodeValid_prime [2, 7, 31, 521, 3424901] ⟨1548836129429, 2, [(2, 2), (7, 1), (31, 1), (521, 1), (3424901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_521
    · exact prime_3424901
  · decide +kernel

theorem prime_1548836129879 : Nat.Prime 1548836129879 := by
  apply nodeValid_prime [2, 73, 10608466643] ⟨1548836129879, 11, [(2, 1), (73, 1), (10608466643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_10608466643
  · decide +kernel

theorem prime_1548836153531 : Nat.Prime 1548836153531 := by
  apply nodeValid_prime [2, 5, 73, 2121693361] ⟨1548836153531, 2, [(2, 1), (5, 1), (73, 1), (2121693361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_2121693361
  · decide +kernel

theorem prime_1550589796999 : Nat.Prime 1550589796999 := by
  apply nodeValid_prime [2, 3, 11, 1597, 4903733] ⟨1550589796999, 3, [(2, 1), (3, 2), (11, 1), (1597, 1), (4903733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1597
    · exact prime_4903733
  · decide +kernel

theorem prime_1550589802169 : Nat.Prime 1550589802169 := by
  apply nodeValid_prime [2, 11, 39139, 450199] ⟨1550589802169, 3, [(2, 3), (11, 1), (39139, 1), (450199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_39139
    · exact prime_450199
  · decide +kernel

theorem prime_1550589802733 : Nat.Prime 1550589802733 := by
  apply nodeValid_prime [2, 54371, 7129673] ⟨1550589802733, 2, [(2, 2), (54371, 1), (7129673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_54371
    · exact prime_7129673
  · decide +kernel

theorem prime_1552344764401 : Nat.Prime 1552344764401 := by
  apply nodeValid_prime [2, 3, 5, 431206879] ⟨1552344764401, 11, [(2, 4), (3, 2), (5, 2), (431206879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_431206879
  · decide +kernel

theorem prime_1552344765661 : Nat.Prime 1552344765661 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 13007749] ⟨1552344765661, 10, [(2, 2), (3, 3), (5, 1), (13, 1), (17, 1), (13007749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_13007749
  · decide +kernel

theorem prime_1552344777239 : Nat.Prime 1552344777239 := by
  apply nodeValid_prime [2, 55021, 14106839] ⟨1552344777239, 7, [(2, 1), (55021, 1), (14106839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_55021
    · exact prime_14106839
  · decide +kernel

theorem prime_1554101107067 : Nat.Prime 1554101107067 := by
  apply nodeValid_prime [2, 739, 1051489247] ⟨1554101107067, 2, [(2, 1), (739, 1), (1051489247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_739
    · exact prime_1051489247
  · decide +kernel

theorem prime_1554101112479 : Nat.Prime 1554101112479 := by
  apply nodeValid_prime [2, 23, 397, 1193, 71333] ⟨1554101112479, 11, [(2, 1), (23, 1), (397, 1), (1193, 1), (71333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_397
    · exact prime_1193
    · exact prime_71333
  · decide +kernel

theorem prime_1554101112677 : Nat.Prime 1554101112677 := by
  apply nodeValid_prime [2, 7, 19, 12853, 227281] ⟨1554101112677, 2, [(2, 2), (7, 1), (19, 1), (12853, 1), (227281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_12853
    · exact prime_227281
  · decide +kernel

theorem prime_1555858780109 : Nat.Prime 1555858780109 := by
  apply nodeValid_prime [2, 388964695027] ⟨1555858780109, 2, [(2, 2), (388964695027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_388964695027
  · decide +kernel

theorem prime_1555858804337 : Nat.Prime 1555858804337 := by
  apply nodeValid_prime [2, 97, 1002486343] ⟨1555858804337, 3, [(2, 4), (97, 1), (1002486343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1002486343
  · decide +kernel

theorem prime_1555858804811 : Nat.Prime 1555858804811 := by
  apply nodeValid_prime [2, 5, 155585880481] ⟨1555858804811, 2, [(2, 1), (5, 1), (155585880481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_155585880481
  · decide +kernel

theorem prime_1557617800639 : Nat.Prime 1557617800639 := by
  apply nodeValid_prime [2, 3, 691, 375691703] ⟨1557617800639, 3, [(2, 1), (3, 1), (691, 1), (375691703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_375691703
  · decide +kernel

theorem prime_1557617808251 : Nat.Prime 1557617808251 := by
  apply nodeValid_prime [2, 5, 7, 31, 41, 53, 73, 181] ⟨1557617808251, 2, [(2, 1), (5, 3), (7, 1), (31, 1), (41, 1), (53, 1), (73, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_41
    · exact prime_53
    · exact prime_73
    · exact prime_181
  · decide +kernel

theorem prime_1557617808277 : Nat.Prime 1557617808277 := by
  apply nodeValid_prime [2, 3, 769, 1523, 36943] ⟨1557617808277, 2, [(2, 2), (3, 2), (769, 1), (1523, 1), (36943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_769
    · exact prime_1523
    · exact prime_36943
  · decide +kernel

theorem prime_1559378172133 : Nat.Prime 1559378172133 := by
  apply nodeValid_prime [2, 3, 11, 29, 1676383] ⟨1559378172133, 5, [(2, 2), (3, 6), (11, 1), (29, 1), (1676383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_1676383
  · decide +kernel

theorem prime_1559378178791 : Nat.Prime 1559378178791 := by
  apply nodeValid_prime [2, 5, 13187, 11825117] ⟨1559378178791, 11, [(2, 1), (5, 1), (13187, 1), (11825117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13187
    · exact prime_11825117
  · decide +kernel

theorem prime_1559378178979 : Nat.Prime 1559378178979 := by
  apply nodeValid_prime [2, 3, 197, 13421, 98299] ⟨1559378178979, 2, [(2, 1), (3, 1), (197, 1), (13421, 1), (98299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_13421
    · exact prime_98299
  · decide +kernel

theorem prime_1561139885687 : Nat.Prime 1561139885687 := by
  apply nodeValid_prime [2, 780569942843] ⟨1561139885687, 5, [(2, 1), (780569942843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_780569942843
  · decide +kernel

theorem prime_1561139891921 : Nat.Prime 1561139891921 := by
  apply nodeValid_prime [2, 5, 7, 199, 431, 32503] ⟨1561139891921, 3, [(2, 4), (5, 1), (7, 1), (199, 1), (431, 1), (32503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_199
    · exact prime_431
    · exact prime_32503
  · decide +kernel

theorem prime_1562902911527 : Nat.Prime 1562902911527 := by
  apply nodeValid_prime [2, 11, 127, 559378279] ⟨1562902911527, 5, [(2, 1), (11, 1), (127, 1), (559378279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_559378279
  · decide +kernel

theorem prime_1562902911847 : Nat.Prime 1562902911847 := by
  apply nodeValid_prime [2, 3, 8273, 10495339] ⟨1562902911847, 3, [(2, 1), (3, 2), (8273, 1), (10495339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8273
    · exact prime_10495339
  · decide +kernel

theorem prime_1562902950431 : Nat.Prime 1562902950431 := by
  apply nodeValid_prime [2, 5, 223, 700853341] ⟨1562902950431, 7, [(2, 1), (5, 1), (223, 1), (700853341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_223
    · exact prime_700853341
  · decide +kernel

theorem prime_1564667356333 : Nat.Prime 1564667356333 := by
  apply nodeValid_prime [2, 3, 64483, 2022067] ⟨1564667356333, 2, [(2, 2), (3, 1), (64483, 1), (2022067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_64483
    · exact prime_2022067
  · decide +kernel

theorem prime_1564667398513 : Nat.Prime 1564667398513 := by
  apply nodeValid_prime [2, 3, 17, 401, 1033, 1543] ⟨1564667398513, 10, [(2, 4), (3, 2), (17, 1), (401, 1), (1033, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_401
    · exact prime_1033
    · exact prime_1543
  · decide +kernel

theorem prime_1564667399333 : Nat.Prime 1564667399333 := by
  apply nodeValid_prime [2, 467003, 837611] ⟨1564667399333, 2, [(2, 2), (467003, 1), (837611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_467003
    · exact prime_837611
  · decide +kernel

theorem prime_1566433036249 : Nat.Prime 1566433036249 := by
  apply nodeValid_prime [2, 3, 373, 6073, 28813] ⟨1566433036249, 17, [(2, 3), (3, 1), (373, 1), (6073, 1), (28813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
    · exact prime_6073
    · exact prime_28813
  · decide +kernel

theorem prime_1566433036477 : Nat.Prime 1566433036477 := by
  apply nodeValid_prime [2, 3, 7, 11, 1361, 138401] ⟨1566433036477, 5, [(2, 2), (3, 3), (7, 1), (11, 1), (1361, 1), (138401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1361
    · exact prime_138401
  · decide +kernel

theorem prime_1566433106741 : Nat.Prime 1566433106741 := by
  apply nodeValid_prime [2, 5, 78321655337] ⟨1566433106741, 2, [(2, 2), (5, 1), (78321655337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_78321655337
  · decide +kernel

theorem prime_1568200186573 : Nat.Prime 1568200186573 := by
  apply nodeValid_prime [2, 3, 21517, 6073493] ⟨1568200186573, 2, [(2, 2), (3, 1), (21517, 1), (6073493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21517
    · exact prime_6073493
  · decide +kernel

theorem prime_1568200186643 : Nat.Prime 1568200186643 := by
  apply nodeValid_prime [2, 2543, 308336647] ⟨1568200186643, 2, [(2, 1), (2543, 1), (308336647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2543
    · exact prime_308336647
  · decide +kernel

theorem prime_1568200198717 : Nat.Prime 1568200198717 := by
  apply nodeValid_prime [2, 3, 19, 7507, 305407] ⟨1568200198717, 2, [(2, 2), (3, 2), (19, 1), (7507, 1), (305407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7507
    · exact prime_305407
  · decide +kernel

theorem prime_1569968614429 : Nat.Prime 1569968614429 := by
  apply nodeValid_prime [2, 3, 1097, 119262277] ⟨1569968614429, 2, [(2, 2), (3, 1), (1097, 1), (119262277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1097
    · exact prime_119262277
  · decide +kernel

theorem prime_1569968615959 : Nat.Prime 1569968615959 := by
  apply nodeValid_prime [2, 3, 137, 5231, 365119] ⟨1569968615959, 3, [(2, 1), (3, 1), (137, 1), (5231, 1), (365119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_5231
    · exact prime_365119
  · decide +kernel

theorem prime_1569968646049 : Nat.Prime 1569968646049 := by
  apply nodeValid_prime [2, 3, 11, 45051901] ⟨1569968646049, 13, [(2, 5), (3, 2), (11, 2), (45051901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_45051901
  · decide +kernel

theorem prime_1571738451649 : Nat.Prime 1571738451649 := by
  apply nodeValid_prime [2, 3, 101, 81050869] ⟨1571738451649, 13, [(2, 6), (3, 1), (101, 1), (81050869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_81050869
  · decide +kernel

theorem prime_1571738475829 : Nat.Prime 1571738475829 := by
  apply nodeValid_prime [2, 3, 181, 677, 1068887] ⟨1571738475829, 2, [(2, 2), (3, 1), (181, 1), (677, 1), (1068887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_677
    · exact prime_1068887
  · decide +kernel

theorem prime_1571738477539 : Nat.Prime 1571738477539 := by
  apply nodeValid_prime [2, 3, 41, 6389180803] ⟨1571738477539, 2, [(2, 1), (3, 1), (41, 1), (6389180803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_6389180803
  · decide +kernel

theorem prime_1573509508759 : Nat.Prime 1573509508759 := by
  apply nodeValid_prime [2, 3, 11, 883001969] ⟨1573509508759, 3, [(2, 1), (3, 4), (11, 1), (883001969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_883001969
  · decide +kernel

theorem prime_1573509511003 : Nat.Prime 1573509511003 := by
  apply nodeValid_prime [2, 3, 11, 13, 47, 5669, 6883] ⟨1573509511003, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (47, 1), (5669, 1), (6883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_47
    · exact prime_5669
    · exact prime_6883
  · decide +kernel

theorem prime_1573509610549 : Nat.Prime 1573509610549 := by
  apply nodeValid_prime [2, 3, 19, 47, 16315267] ⟨1573509610549, 2, [(2, 2), (3, 3), (19, 1), (47, 1), (16315267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_47
    · exact prime_16315267
  · decide +kernel

theorem prime_1575282114053 : Nat.Prime 1575282114053 := by
  apply nodeValid_prime [2, 2399, 164160287] ⟨1575282114053, 2, [(2, 2), (2399, 1), (164160287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2399
    · exact prime_164160287
  · decide +kernel

theorem prime_1575282114781 : Nat.Prime 1575282114781 := by
  apply nodeValid_prime [2, 3, 5, 11, 47, 50782789] ⟨1575282114781, 29, [(2, 2), (3, 1), (5, 1), (11, 1), (47, 1), (50782789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_47
    · exact prime_50782789
  · decide +kernel

theorem prime_1575282121613 : Nat.Prime 1575282121613 := by
  apply nodeValid_prime [2, 19, 37, 560199901] ⟨1575282121613, 2, [(2, 2), (19, 1), (37, 1), (560199901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_560199901
  · decide +kernel

theorem prime_1577055985163 : Nat.Prime 1577055985163 := by
  apply nodeValid_prime [2, 7, 4919, 22900357] ⟨1577055985163, 2, [(2, 1), (7, 1), (4919, 1), (22900357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4919
    · exact prime_22900357
  · decide +kernel

theorem prime_1577055985469 : Nat.Prime 1577055985469 := by
  apply nodeValid_prime [2, 394263996367] ⟨1577055985469, 2, [(2, 2), (394263996367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_394263996367
  · decide +kernel

theorem prime_1577055986021 : Nat.Prime 1577055986021 := by
  apply nodeValid_prime [2, 5, 61, 89, 14524369] ⟨1577055986021, 2, [(2, 2), (5, 1), (61, 1), (89, 1), (14524369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_89
    · exact prime_14524369
  · decide +kernel

theorem prime_1578831173471 : Nat.Prime 1578831173471 := by
  apply nodeValid_prime [2, 5, 157883117347] ⟨1578831173471, 13, [(2, 1), (5, 1), (157883117347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157883117347
  · decide +kernel

theorem prime_1578831173597 : Nat.Prime 1578831173597 := by
  apply nodeValid_prime [2, 49811, 7924109] ⟨1578831173597, 2, [(2, 2), (49811, 1), (7924109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_49811
    · exact prime_7924109
  · decide +kernel

theorem prime_1578831208363 : Nat.Prime 1578831208363 := by
  apply nodeValid_prime [2, 3, 101, 868444009] ⟨1578831208363, 2, [(2, 1), (3, 2), (101, 1), (868444009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_868444009
  · decide +kernel

theorem prime_1580607779197 : Nat.Prime 1580607779197 := by
  apply nodeValid_prime [2, 3, 17, 29, 31, 281, 30671] ⟨1580607779197, 2, [(2, 2), (3, 1), (17, 1), (29, 1), (31, 1), (281, 1), (30671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_31
    · exact prime_281
    · exact prime_30671
  · decide +kernel

theorem prime_1580607807847 : Nat.Prime 1580607807847 := by
  apply nodeValid_prime [2, 3, 23, 11453679767] ⟨1580607807847, 3, [(2, 1), (3, 1), (23, 1), (11453679767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_11453679767
  · decide +kernel

theorem prime_1580607809401 : Nat.Prime 1580607809401 := by
  apply nodeValid_prime [2, 3, 5, 787, 3347327] ⟨1580607809401, 7, [(2, 3), (3, 1), (5, 2), (787, 1), (3347327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_787
    · exact prime_3347327
  · decide +kernel

theorem prime_1582385698177 : Nat.Prime 1582385698177 := by
  apply nodeValid_prime [2, 3, 40823, 100943] ⟨1582385698177, 10, [(2, 7), (3, 1), (40823, 1), (100943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40823
    · exact prime_100943
  · decide +kernel

theorem prime_1582385698559 : Nat.Prime 1582385698559 := by
  apply nodeValid_prime [2, 7, 113027549897] ⟨1582385698559, 7, [(2, 1), (7, 1), (113027549897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113027549897
  · decide +kernel

theorem prime_1582385707283 : Nat.Prime 1582385707283 := by
  apply nodeValid_prime [2, 19, 47, 885994237] ⟨1582385707283, 2, [(2, 1), (19, 1), (47, 1), (885994237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_885994237
  · decide +kernel

theorem prime_1584164952973 : Nat.Prime 1584164952973 := by
  apply nodeValid_prime [2, 3, 7, 19, 1213, 30307] ⟨1584164952973, 2, [(2, 2), (3, 4), (7, 1), (19, 1), (1213, 1), (30307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_1213
    · exact prime_30307
  · decide +kernel

theorem prime_1584164958253 : Nat.Prime 1584164958253 := by
  apply nodeValid_prime [2, 3, 132013746521] ⟨1584164958253, 2, [(2, 2), (3, 1), (132013746521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132013746521
  · decide +kernel

theorem prime_1584164988299 : Nat.Prime 1584164988299 := by
  apply nodeValid_prime [2, 37, 167, 4861, 26371] ⟨1584164988299, 2, [(2, 1), (37, 1), (167, 1), (4861, 1), (26371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_167
    · exact prime_4861
    · exact prime_26371
  · decide +kernel

theorem prime_1585945591291 : Nat.Prime 1585945591291 := by
  apply nodeValid_prime [2, 3, 5, 29, 607641989] ⟨1585945591291, 2, [(2, 1), (3, 2), (5, 1), (29, 1), (607641989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_607641989
  · decide +kernel

theorem prime_1585945594759 : Nat.Prime 1585945594759 := by
  apply nodeValid_prime [2, 3, 7, 71, 531839569] ⟨1585945594759, 3, [(2, 1), (3, 1), (7, 1), (71, 1), (531839569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_531839569
  · decide +kernel

theorem prime_1585945631453 : Nat.Prime 1585945631453 := by
  apply nodeValid_prime [2, 7, 13, 19, 229315447] ⟨1585945631453, 2, [(2, 2), (7, 1), (13, 1), (19, 1), (229315447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_229315447
  · decide +kernel

theorem prime_1587727635953 : Nat.Prime 1587727635953 := by
  apply nodeValid_prime [2, 99232977247] ⟨1587727635953, 3, [(2, 4), (99232977247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_99232977247
  · decide +kernel

theorem prime_1587727650137 : Nat.Prime 1587727650137 := by
  apply nodeValid_prime [2, 198465956267] ⟨1587727650137, 3, [(2, 3), (198465956267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_198465956267
  · decide +kernel

theorem prime_1587727650497 : Nat.Prime 1587727650497 := by
  apply nodeValid_prime [2, 13, 19, 59, 89597] ⟨1587727650497, 5, [(2, 6), (13, 1), (19, 2), (59, 1), (89597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_59
    · exact prime_89597
  · decide +kernel

theorem prime_1589510971859 : Nat.Prime 1589510971859 := by
  apply nodeValid_prime [2, 236087, 3366367] ⟨1589510971859, 2, [(2, 1), (236087, 1), (3366367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_236087
    · exact prime_3366367
  · decide +kernel

theorem prime_1589510971927 : Nat.Prime 1589510971927 := by
  apply nodeValid_prime [2, 3, 37, 265183679] ⟨1589510971927, 6, [(2, 1), (3, 4), (37, 1), (265183679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_265183679
  · decide +kernel

theorem prime_1589510994641 : Nat.Prime 1589510994641 := by
  apply nodeValid_prime [2, 5, 23, 863864671] ⟨1589510994641, 6, [(2, 4), (5, 1), (23, 1), (863864671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_863864671
  · decide +kernel

end Sude.Lucas.Generated
