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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0086

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7589 : Nat.Prime 7589 := by
  apply nodeValid_prime [2, 7, 271] ⟨7589, 2, [(2, 2), (7, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_271
  · decide +kernel

theorem prime_10499 : Nat.Prime 10499 := by
  apply nodeValid_prime [2, 29, 181] ⟨10499, 2, [(2, 1), (29, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_181
  · decide +kernel

theorem prime_12899 : Nat.Prime 12899 := by
  apply nodeValid_prime [2, 6449] ⟨12899, 2, [(2, 1), (6449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6449
  · decide +kernel

theorem prime_20357 : Nat.Prime 20357 := by
  apply nodeValid_prime [2, 7, 727] ⟨20357, 2, [(2, 2), (7, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_727
  · decide +kernel

theorem prime_20359 : Nat.Prime 20359 := by
  apply nodeValid_prime [2, 3, 13, 29] ⟨20359, 11, [(2, 1), (3, 3), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_22691 : Nat.Prime 22691 := by
  apply nodeValid_prime [2, 5, 2269] ⟨22691, 2, [(2, 1), (5, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2269
  · decide +kernel

theorem prime_25799 : Nat.Prime 25799 := by
  apply nodeValid_prime [2, 12899] ⟨25799, 7, [(2, 1), (12899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12899
  · decide +kernel

theorem prime_36527 : Nat.Prime 36527 := by
  apply nodeValid_prime [2, 7, 2609] ⟨36527, 5, [(2, 1), (7, 1), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2609
  · decide +kernel

theorem prime_37699 : Nat.Prime 37699 := by
  apply nodeValid_prime [2, 3, 61, 103] ⟨37699, 3, [(2, 1), (3, 1), (61, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_103
  · decide +kernel

theorem prime_42013 : Nat.Prime 42013 := by
  apply nodeValid_prime [2, 3, 389] ⟨42013, 6, [(2, 2), (3, 3), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
  · decide +kernel

theorem prime_49123 : Nat.Prime 49123 := by
  apply nodeValid_prime [2, 3, 2729] ⟨49123, 2, [(2, 1), (3, 2), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2729
  · decide +kernel

theorem prime_51949 : Nat.Prime 51949 := by
  apply nodeValid_prime [2, 3, 13, 37] ⟨51949, 2, [(2, 2), (3, 3), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_55793 : Nat.Prime 55793 := by
  apply nodeValid_prime [2, 11, 317] ⟨55793, 3, [(2, 4), (11, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_317
  · decide +kernel

theorem prime_71699 : Nat.Prime 71699 := by
  apply nodeValid_prime [2, 11, 3259] ⟨71699, 2, [(2, 1), (11, 1), (3259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3259
  · decide +kernel

theorem prime_72043 : Nat.Prime 72043 := by
  apply nodeValid_prime [2, 3, 12007] ⟨72043, 5, [(2, 1), (3, 1), (12007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12007
  · decide +kernel

theorem prime_81071 : Nat.Prime 81071 := by
  apply nodeValid_prime [2, 5, 11, 67] ⟨81071, 7, [(2, 1), (5, 1), (11, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_83227 : Nat.Prime 83227 := by
  apply nodeValid_prime [2, 3, 11, 13, 97] ⟨83227, 5, [(2, 1), (3, 1), (11, 1), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_96221 : Nat.Prime 96221 := by
  apply nodeValid_prime [2, 5, 17, 283] ⟨96221, 2, [(2, 2), (5, 1), (17, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_283
  · decide +kernel

theorem prime_103357 : Nat.Prime 103357 := by
  apply nodeValid_prime [2, 3, 11, 29] ⟨103357, 6, [(2, 2), (3, 4), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_105491 : Nat.Prime 105491 := by
  apply nodeValid_prime [2, 5, 7, 11, 137] ⟨105491, 2, [(2, 1), (5, 1), (7, 1), (11, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_137
  · decide +kernel

theorem prime_109873 : Nat.Prime 109873 := by
  apply nodeValid_prime [2, 3, 7, 109] ⟨109873, 15, [(2, 4), (3, 2), (7, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
  · decide +kernel

theorem prime_112139 : Nat.Prime 112139 := by
  apply nodeValid_prime [2, 13, 19, 227] ⟨112139, 2, [(2, 1), (13, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_128399 : Nat.Prime 128399 := by
  apply nodeValid_prime [2, 43, 1493] ⟨128399, 13, [(2, 1), (43, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1493
  · decide +kernel

theorem prime_133853 : Nat.Prime 133853 := by
  apply nodeValid_prime [2, 109, 307] ⟨133853, 2, [(2, 2), (109, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_307
  · decide +kernel

theorem prime_157243 : Nat.Prime 157243 := by
  apply nodeValid_prime [2, 3, 73, 359] ⟨157243, 3, [(2, 1), (3, 1), (73, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_359
  · decide +kernel

theorem prime_167971 : Nat.Prime 167971 := by
  apply nodeValid_prime [2, 3, 5, 11, 509] ⟨167971, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_509
  · decide +kernel

theorem prime_174917 : Nat.Prime 174917 := by
  apply nodeValid_prime [2, 7, 6247] ⟨174917, 2, [(2, 2), (7, 1), (6247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6247
  · decide +kernel

theorem prime_175699 : Nat.Prime 175699 := by
  apply nodeValid_prime [2, 3, 43, 227] ⟨175699, 3, [(2, 1), (3, 2), (43, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_227
  · decide +kernel

theorem prime_207797 : Nat.Prime 207797 := by
  apply nodeValid_prime [2, 51949] ⟨207797, 2, [(2, 2), (51949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_51949
  · decide +kernel

theorem prime_208261 : Nat.Prime 208261 := by
  apply nodeValid_prime [2, 3, 5, 13, 89] ⟨208261, 2, [(2, 2), (3, 2), (5, 1), (13, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_89
  · decide +kernel

theorem prime_225581 : Nat.Prime 225581 := by
  apply nodeValid_prime [2, 5, 11279] ⟨225581, 2, [(2, 2), (5, 1), (11279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11279
  · decide +kernel

theorem prime_302681 : Nat.Prime 302681 := by
  apply nodeValid_prime [2, 5, 7, 23, 47] ⟨302681, 3, [(2, 3), (5, 1), (7, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_336031 : Nat.Prime 336031 := by
  apply nodeValid_prime [2, 3, 5, 23, 487] ⟨336031, 15, [(2, 1), (3, 1), (5, 1), (23, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_487
  · decide +kernel

theorem prime_379633 : Nat.Prime 379633 := by
  apply nodeValid_prime [2, 3, 11, 719] ⟨379633, 5, [(2, 4), (3, 1), (11, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_719
  · decide +kernel

theorem prime_426389 : Nat.Prime 426389 := by
  apply nodeValid_prime [2, 37, 43, 67] ⟨426389, 2, [(2, 2), (37, 1), (43, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
    · exact prime_67
  · decide +kernel

theorem prime_439493 : Nat.Prime 439493 := by
  apply nodeValid_prime [2, 109873] ⟨439493, 2, [(2, 2), (109873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_109873
  · decide +kernel

theorem prime_456107 : Nat.Prime 456107 := by
  apply nodeValid_prime [2, 7, 32579] ⟨456107, 2, [(2, 1), (7, 1), (32579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_32579
  · decide +kernel

theorem prime_507049 : Nat.Prime 507049 := by
  apply nodeValid_prime [2, 3, 37, 571] ⟨507049, 17, [(2, 3), (3, 1), (37, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_571
  · decide +kernel

theorem prime_552137 : Nat.Prime 552137 := by
  apply nodeValid_prime [2, 13, 5309] ⟨552137, 3, [(2, 3), (13, 1), (5309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5309
  · decide +kernel

theorem prime_577327 : Nat.Prime 577327 := by
  apply nodeValid_prime [2, 3, 96221] ⟨577327, 6, [(2, 1), (3, 1), (96221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_96221
  · decide +kernel

theorem prime_596179 : Nat.Prime 596179 := by
  apply nodeValid_prime [2, 3, 11, 3011] ⟨596179, 10, [(2, 1), (3, 2), (11, 1), (3011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3011
  · decide +kernel

theorem prime_612971 : Nat.Prime 612971 := by
  apply nodeValid_prime [2, 5, 61297] ⟨612971, 2, [(2, 1), (5, 1), (61297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61297
  · decide +kernel

theorem prime_748441 : Nat.Prime 748441 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨748441, 13, [(2, 3), (3, 5), (5, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_773567 : Nat.Prime 773567 := by
  apply nodeValid_prime [2, 19, 20357] ⟨773567, 5, [(2, 1), (19, 1), (20357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_20357
  · decide +kernel

theorem prime_878987 : Nat.Prime 878987 := by
  apply nodeValid_prime [2, 439493] ⟨878987, 2, [(2, 1), (439493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_439493
  · decide +kernel

theorem prime_893873 : Nat.Prime 893873 := by
  apply nodeValid_prime [2, 7, 23, 347] ⟨893873, 3, [(2, 4), (7, 1), (23, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_347
  · decide +kernel

theorem prime_902767 : Nat.Prime 902767 := by
  apply nodeValid_prime [2, 3, 19, 7919] ⟨902767, 3, [(2, 1), (3, 1), (19, 1), (7919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7919
  · decide +kernel

theorem prime_938207 : Nat.Prime 938207 := by
  apply nodeValid_prime [2, 53, 167] ⟨938207, 5, [(2, 1), (53, 2), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_167
  · decide +kernel

theorem prime_1239607 : Nat.Prime 1239607 := by
  apply nodeValid_prime [2, 3, 17, 4051] ⟨1239607, 3, [(2, 1), (3, 2), (17, 1), (4051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4051
  · decide +kernel

theorem prime_1353487 : Nat.Prime 1353487 := by
  apply nodeValid_prime [2, 3, 225581] ⟨1353487, 5, [(2, 1), (3, 1), (225581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_225581
  · decide +kernel

theorem prime_1369747 : Nat.Prime 1369747 := by
  apply nodeValid_prime [2, 3, 7, 1553] ⟨1369747, 5, [(2, 1), (3, 2), (7, 2), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1553
  · decide +kernel

theorem prime_1386479 : Nat.Prime 1386479 := by
  apply nodeValid_prime [2, 163, 4253] ⟨1386479, 17, [(2, 1), (163, 1), (4253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_4253
  · decide +kernel

theorem prime_1611079 : Nat.Prime 1611079 := by
  apply nodeValid_prime [2, 3, 7, 89, 431] ⟨1611079, 3, [(2, 1), (3, 1), (7, 1), (89, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_431
  · decide +kernel

theorem prime_1729033 : Nat.Prime 1729033 := by
  apply nodeValid_prime [2, 3, 72043] ⟨1729033, 5, [(2, 3), (3, 1), (72043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_72043
  · decide +kernel

theorem prime_1756991 : Nat.Prime 1756991 := by
  apply nodeValid_prime [2, 5, 175699] ⟨1756991, 11, [(2, 1), (5, 1), (175699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_175699
  · decide +kernel

theorem prime_1856069 : Nat.Prime 1856069 := by
  apply nodeValid_prime [2, 37, 12541] ⟨1856069, 2, [(2, 2), (37, 1), (12541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_12541
  · decide +kernel

theorem prime_1911529 : Nat.Prime 1911529 := by
  apply nodeValid_prime [2, 3, 139, 191] ⟨1911529, 19, [(2, 3), (3, 2), (139, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_191
  · decide +kernel

theorem prime_1925533 : Nat.Prime 1925533 := by
  apply nodeValid_prime [2, 3, 7, 283] ⟨1925533, 2, [(2, 2), (3, 5), (7, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
  · decide +kernel

theorem prime_2204077 : Nat.Prime 2204077 := by
  apply nodeValid_prime [2, 3, 7, 19, 1381] ⟨2204077, 2, [(2, 2), (3, 1), (7, 1), (19, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_1381
  · decide +kernel

theorem prime_2242781 : Nat.Prime 2242781 := by
  apply nodeValid_prime [2, 5, 112139] ⟨2242781, 10, [(2, 2), (5, 1), (112139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_112139
  · decide +kernel

theorem prime_2583169 : Nat.Prime 2583169 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨2583169, 22, [(2, 7), (3, 1), (7, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_2659949 : Nat.Prime 2659949 := by
  apply nodeValid_prime [2, 149, 4463] ⟨2659949, 2, [(2, 2), (149, 1), (4463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_4463
  · decide +kernel

theorem prime_3111341 : Nat.Prime 3111341 := by
  apply nodeValid_prime [2, 5, 17, 9151] ⟨3111341, 2, [(2, 2), (5, 1), (17, 1), (9151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_9151
  · decide +kernel

theorem prime_3111491 : Nat.Prime 3111491 := by
  apply nodeValid_prime [2, 5, 41, 7589] ⟨3111491, 2, [(2, 1), (5, 1), (41, 1), (7589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_7589
  · decide +kernel

theorem prime_3135287 : Nat.Prime 3135287 := by
  apply nodeValid_prime [2, 7, 11, 20359] ⟨3135287, 5, [(2, 1), (7, 1), (11, 1), (20359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_20359
  · decide +kernel

theorem prime_3404983 : Nat.Prime 3404983 := by
  apply nodeValid_prime [2, 3, 7, 81071] ⟨3404983, 5, [(2, 1), (3, 1), (7, 1), (81071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_81071
  · decide +kernel

theorem prime_3712139 : Nat.Prime 3712139 := by
  apply nodeValid_prime [2, 1856069] ⟨3712139, 2, [(2, 1), (1856069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1856069
  · decide +kernel

theorem prime_3983279 : Nat.Prime 3983279 := by
  apply nodeValid_prime [2, 13, 23, 6661] ⟨3983279, 11, [(2, 1), (13, 1), (23, 1), (6661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_6661
  · decide +kernel

theorem prime_4160719 : Nat.Prime 4160719 := by
  apply nodeValid_prime [2, 3, 97, 2383] ⟨4160719, 3, [(2, 1), (3, 2), (97, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_2383
  · decide +kernel

theorem prime_4359587 : Nat.Prime 4359587 := by
  apply nodeValid_prime [2, 7, 11, 28309] ⟨4359587, 2, [(2, 1), (7, 1), (11, 1), (28309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_28309
  · decide +kernel

theorem prime_5273263 : Nat.Prime 5273263 := by
  apply nodeValid_prime [2, 3, 43, 757] ⟨5273263, 5, [(2, 1), (3, 4), (43, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_757
  · decide +kernel

theorem prime_5649557 : Nat.Prime 5649557 := by
  apply nodeValid_prime [2, 11, 128399] ⟨5649557, 2, [(2, 2), (11, 1), (128399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_128399
  · decide +kernel

theorem prime_6008971 : Nat.Prime 6008971 := by
  apply nodeValid_prime [2, 3, 5, 11, 131, 139] ⟨6008971, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (131, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_131
    · exact prime_139
  · decide +kernel

theorem prime_7424279 : Nat.Prime 7424279 := by
  apply nodeValid_prime [2, 3712139] ⟨7424279, 7, [(2, 1), (3712139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3712139
  · decide +kernel

theorem prime_7966559 : Nat.Prime 7966559 := by
  apply nodeValid_prime [2, 3983279] ⟨7966559, 19, [(2, 1), (3983279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3983279
  · decide +kernel

theorem prime_8666137 : Nat.Prime 8666137 := by
  apply nodeValid_prime [2, 3, 53, 757] ⟨8666137, 5, [(2, 3), (3, 3), (53, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_757
  · decide +kernel

theorem prime_10870729 : Nat.Prime 10870729 := by
  apply nodeValid_prime [2, 3, 11, 41177] ⟨10870729, 19, [(2, 3), (3, 1), (11, 1), (41177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41177
  · decide +kernel

theorem prime_13134899 : Nat.Prime 13134899 := by
  apply nodeValid_prime [2, 7, 938207] ⟨13134899, 2, [(2, 1), (7, 1), (938207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_938207
  · decide +kernel

theorem prime_14795237 : Nat.Prime 14795237 := by
  apply nodeValid_prime [2, 17, 217577] ⟨14795237, 2, [(2, 2), (17, 1), (217577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_217577
  · decide +kernel

theorem prime_21829319 : Nat.Prime 21829319 := by
  apply nodeValid_prime [2, 7, 941, 1657] ⟨21829319, 7, [(2, 1), (7, 1), (941, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_941
    · exact prime_1657
  · decide +kernel

theorem prime_22040771 : Nat.Prime 22040771 := by
  apply nodeValid_prime [2, 5, 2204077] ⟨22040771, 2, [(2, 1), (5, 1), (2204077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2204077
  · decide +kernel

theorem prime_25465513 : Nat.Prime 25465513 := by
  apply nodeValid_prime [2, 3, 439, 2417] ⟨25465513, 5, [(2, 3), (3, 1), (439, 1), (2417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_439
    · exact prime_2417
  · decide +kernel

theorem prime_26161717 : Nat.Prime 26161717 := by
  apply nodeValid_prime [2, 3, 7, 43, 7243] ⟨26161717, 2, [(2, 2), (3, 1), (7, 1), (43, 1), (7243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_7243
  · decide +kernel

theorem prime_51996823 : Nat.Prime 51996823 := by
  apply nodeValid_prime [2, 3, 8666137] ⟨51996823, 6, [(2, 1), (3, 1), (8666137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8666137
  · decide +kernel

theorem prime_54789881 : Nat.Prime 54789881 := by
  apply nodeValid_prime [2, 5, 1369747] ⟨54789881, 3, [(2, 3), (5, 1), (1369747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1369747
  · decide +kernel

theorem prime_56000221 : Nat.Prime 56000221 := by
  apply nodeValid_prime [2, 3, 5, 19, 49123] ⟨56000221, 11, [(2, 2), (3, 1), (5, 1), (19, 1), (49123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_49123
  · decide +kernel

theorem prime_72443593 : Nat.Prime 72443593 := by
  apply nodeValid_prime [2, 3, 13, 25799] ⟨72443593, 5, [(2, 3), (3, 3), (13, 1), (25799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_25799
  · decide +kernel

theorem prime_96342359 : Nat.Prime 96342359 := by
  apply nodeValid_prime [2, 7, 31, 221987] ⟨96342359, 7, [(2, 1), (7, 1), (31, 1), (221987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_221987
  · decide +kernel

theorem prime_109579763 : Nat.Prime 109579763 := by
  apply nodeValid_prime [2, 54789881] ⟨109579763, 2, [(2, 1), (54789881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54789881
  · decide +kernel

theorem prime_115997689 : Nat.Prime 115997689 := by
  apply nodeValid_prime [2, 3, 1611079] ⟨115997689, 7, [(2, 3), (3, 2), (1611079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1611079
  · decide +kernel

theorem prime_132244627 : Nat.Prime 132244627 := by
  apply nodeValid_prime [2, 3, 22040771] ⟨132244627, 2, [(2, 1), (3, 1), (22040771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22040771
  · decide +kernel

theorem prime_143056489 : Nat.Prime 143056489 := by
  apply nodeValid_prime [2, 3, 751, 7937] ⟨143056489, 17, [(2, 3), (3, 1), (751, 1), (7937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_751
    · exact prime_7937
  · decide +kernel

theorem prime_145506857 : Nat.Prime 145506857 := by
  apply nodeValid_prime [2, 11, 191, 787] ⟨145506857, 3, [(2, 3), (11, 2), (191, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_191
    · exact prime_787
  · decide +kernel

theorem prime_150504091 : Nat.Prime 150504091 := by
  apply nodeValid_prime [2, 3, 5, 11, 137, 3329] ⟨150504091, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (137, 1), (3329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_137
    · exact prime_3329
  · decide +kernel

theorem prime_246070969 : Nat.Prime 246070969 := by
  apply nodeValid_prime [2, 3, 11, 13, 71699] ⟨246070969, 31, [(2, 3), (3, 1), (11, 1), (13, 1), (71699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_71699
  · decide +kernel

theorem prime_387097283 : Nat.Prime 387097283 := by
  apply nodeValid_prime [2, 11, 13, 1353487] ⟨387097283, 5, [(2, 1), (11, 1), (13, 1), (1353487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_1353487
  · decide +kernel

theorem prime_394729457 : Nat.Prime 394729457 := by
  apply nodeValid_prime [2, 11, 2242781] ⟨394729457, 3, [(2, 4), (11, 1), (2242781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2242781
  · decide +kernel

theorem prime_520168751 : Nat.Prime 520168751 := by
  apply nodeValid_prime [2, 5, 83227] ⟨520168751, 7, [(2, 1), (5, 5), (83227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83227
  · decide +kernel

theorem prime_526728217 : Nat.Prime 526728217 := by
  apply nodeValid_prime [2, 3, 7, 3135287] ⟨526728217, 5, [(2, 3), (3, 1), (7, 1), (3135287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3135287
  · decide +kernel

theorem prime_546697043 : Nat.Prime 546697043 := by
  apply nodeValid_prime [2, 101, 991, 2731] ⟨546697043, 2, [(2, 1), (101, 1), (991, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_991
    · exact prime_2731
  · decide +kernel

theorem prime_572225957 : Nat.Prime 572225957 := by
  apply nodeValid_prime [2, 143056489] ⟨572225957, 2, [(2, 2), (143056489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_143056489
  · decide +kernel

theorem prime_657478579 : Nat.Prime 657478579 := by
  apply nodeValid_prime [2, 3, 109579763] ⟨657478579, 2, [(2, 1), (3, 1), (109579763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109579763
  · decide +kernel

theorem prime_781302671 : Nat.Prime 781302671 := by
  apply nodeValid_prime [2, 5, 101, 773567] ⟨781302671, 7, [(2, 1), (5, 1), (101, 1), (773567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_773567
  · decide +kernel

theorem prime_946263473 : Nat.Prime 946263473 := by
  apply nodeValid_prime [2, 7, 11, 103, 7457] ⟨946263473, 3, [(2, 4), (7, 1), (11, 1), (103, 1), (7457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_103
    · exact prime_7457
  · decide +kernel

theorem prime_1232004863 : Nat.Prime 1232004863 := by
  apply nodeValid_prime [2, 11, 56000221] ⟨1232004863, 5, [(2, 1), (11, 1), (56000221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_56000221
  · decide +kernel

theorem prime_1392121091 : Nat.Prime 1392121091 := by
  apply nodeValid_prime [2, 5, 89, 569, 2749] ⟨1392121091, 2, [(2, 1), (5, 1), (89, 1), (569, 1), (2749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_569
    · exact prime_2749
  · decide +kernel

theorem prime_2836868467 : Nat.Prime 2836868467 := by
  apply nodeValid_prime [2, 3, 31, 571, 26711] ⟨2836868467, 2, [(2, 1), (3, 1), (31, 1), (571, 1), (26711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_571
    · exact prime_26711
  · decide +kernel

theorem prime_2875079293 : Nat.Prime 2875079293 := by
  apply nodeValid_prime [2, 3, 1153, 207797] ⟨2875079293, 2, [(2, 2), (3, 1), (1153, 1), (207797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1153
    · exact prime_207797
  · decide +kernel

theorem prime_3593558431 : Nat.Prime 3593558431 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 17, 47, 59] ⟨3593558431, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (11, 2), (17, 1), (47, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_47
    · exact prime_59
  · decide +kernel

theorem prime_7623938719 : Nat.Prime 7623938719 := by
  apply nodeValid_prime [2, 3, 11, 223, 1427] ⟨7623938719, 3, [(2, 1), (3, 2), (11, 3), (223, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_223
    · exact prime_1427
  · decide +kernel

theorem prime_10550559367 : Nat.Prime 10550559367 := by
  apply nodeValid_prime [2, 3, 113, 1729033] ⟨10550559367, 3, [(2, 1), (3, 3), (113, 1), (1729033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_1729033
  · decide +kernel

theorem prime_33965749463 : Nat.Prime 33965749463 := by
  apply nodeValid_prime [2, 22691, 748441] ⟨33965749463, 5, [(2, 1), (22691, 1), (748441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_22691
    · exact prime_748441
  · decide +kernel

theorem prime_59209418551 : Nat.Prime 59209418551 := by
  apply nodeValid_prime [2, 3, 5, 394729457] ⟨59209418551, 6, [(2, 1), (3, 1), (5, 2), (394729457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_394729457
  · decide +kernel

theorem prime_83296482959 : Nat.Prime 83296482959 := by
  apply nodeValid_prime [2, 13, 19073, 167971] ⟨83296482959, 14, [(2, 1), (13, 1), (19073, 1), (167971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19073
    · exact prime_167971
  · decide +kernel

theorem prime_104626380401 : Nat.Prime 104626380401 := by
  apply nodeValid_prime [2, 5, 19, 47, 83, 3529] ⟨104626380401, 6, [(2, 4), (5, 2), (19, 1), (47, 1), (83, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_47
    · exact prime_83
    · exact prime_3529
  · decide +kernel

theorem prime_105540973633 : Nat.Prime 105540973633 := by
  apply nodeValid_prime [2, 3, 23, 7966559] ⟨105540973633, 10, [(2, 6), (3, 2), (23, 1), (7966559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_7966559
  · decide +kernel

theorem prime_113806601203 : Nat.Prime 113806601203 := by
  apply nodeValid_prime [2, 3, 7, 387097283] ⟨113806601203, 5, [(2, 1), (3, 1), (7, 2), (387097283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_387097283
  · decide +kernel

theorem prime_206830596629 : Nat.Prime 206830596629 := by
  apply nodeValid_prime [2, 17, 23, 132244627] ⟨206830596629, 2, [(2, 2), (17, 1), (23, 1), (132244627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_132244627
  · decide +kernel

theorem prime_208039286969 : Nat.Prime 208039286969 := by
  apply nodeValid_prime [2, 4603, 5649557] ⟨208039286969, 3, [(2, 3), (4603, 1), (5649557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4603
    · exact prime_5649557
  · decide +kernel

theorem prime_415271726621 : Nat.Prime 415271726621 := by
  apply nodeValid_prime [2, 5, 179, 115997689] ⟨415271726621, 3, [(2, 2), (5, 1), (179, 1), (115997689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_115997689
  · decide +kernel

theorem prime_419722585267 : Nat.Prime 419722585267 := by
  apply nodeValid_prime [2, 3, 41, 67, 25465513] ⟨419722585267, 3, [(2, 1), (3, 1), (41, 1), (67, 1), (25465513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_67
    · exact prime_25465513
  · decide +kernel

theorem prime_627758282407 : Nat.Prime 627758282407 := by
  apply nodeValid_prime [2, 3, 104626380401] ⟨627758282407, 3, [(2, 1), (3, 1), (104626380401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_104626380401
  · decide +kernel

theorem prime_2479555317391 : Nat.Prime 2479555317391 := by
  apply nodeValid_prime [2, 3, 5, 23, 3593558431] ⟨2479555317391, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (3593558431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_3593558431
  · decide +kernel

theorem prime_2479555523737 : Nat.Prime 2479555523737 := by
  apply nodeValid_prime [2, 3, 31, 89, 4160719] ⟨2479555523737, 5, [(2, 3), (3, 3), (31, 1), (89, 1), (4160719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_89
    · exact prime_4160719
  · decide +kernel

theorem prime_2479555523989 : Nat.Prime 2479555523989 := by
  apply nodeValid_prime [2, 3, 127, 617, 878987] ⟨2479555523989, 7, [(2, 2), (3, 2), (127, 1), (617, 1), (878987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_617
    · exact prime_878987
  · decide +kernel

theorem prime_2481967102213 : Nat.Prime 2481967102213 := by
  apply nodeValid_prime [2, 3, 13, 17, 349, 893873] ⟨2481967102213, 2, [(2, 2), (3, 2), (13, 1), (17, 1), (349, 1), (893873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_349
    · exact prime_893873
  · decide +kernel

theorem prime_2481967103197 : Nat.Prime 2481967103197 := by
  apply nodeValid_prime [2, 3, 7, 29, 1709, 596179] ⟨2481967103197, 5, [(2, 2), (3, 1), (7, 1), (29, 1), (1709, 1), (596179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_1709
    · exact prime_596179
  · decide +kernel

theorem prime_2481967159549 : Nat.Prime 2481967159549 := by
  apply nodeValid_prime [2, 3, 206830596629] ⟨2481967159549, 2, [(2, 2), (3, 1), (206830596629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_206830596629
  · decide +kernel

theorem prime_2484380578343 : Nat.Prime 2484380578343 := by
  apply nodeValid_prime [2, 13, 1319, 72443593] ⟨2484380578343, 5, [(2, 1), (13, 1), (1319, 1), (72443593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1319
    · exact prime_72443593
  · decide +kernel

theorem prime_2484380680549 : Nat.Prime 2484380680549 := by
  apply nodeValid_prime [2, 3, 13, 83, 571, 336031] ⟨2484380680549, 6, [(2, 2), (3, 1), (13, 1), (83, 1), (571, 1), (336031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
    · exact prime_571
    · exact prime_336031
  · decide +kernel

theorem prime_2484380681977 : Nat.Prime 2484380681977 := by
  apply nodeValid_prime [2, 3, 113, 739, 1239607] ⟨2484380681977, 7, [(2, 3), (3, 1), (113, 1), (739, 1), (1239607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_739
    · exact prime_1239607
  · decide +kernel

theorem prime_2486795579143 : Nat.Prime 2486795579143 := by
  apply nodeValid_prime [2, 3, 7, 59209418551] ⟨2486795579143, 5, [(2, 1), (3, 1), (7, 1), (59209418551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59209418551
  · decide +kernel

theorem prime_2486795616541 : Nat.Prime 2486795616541 := by
  apply nodeValid_prime [2, 3, 5, 3169, 4359587] ⟨2486795616541, 2, [(2, 2), (3, 2), (5, 1), (3169, 1), (4359587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3169
    · exact prime_4359587
  · decide +kernel

theorem prime_2486795617177 : Nat.Prime 2486795617177 := by
  apply nodeValid_prime [2, 3, 13, 17, 1549, 302681] ⟨2486795617177, 10, [(2, 3), (3, 1), (13, 1), (17, 1), (1549, 1), (302681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_1549
    · exact prime_302681
  · decide +kernel

theorem prime_2489212159573 : Nat.Prime 2489212159573 := by
  apply nodeValid_prime [2, 3, 139, 283, 5273263] ⟨2489212159573, 6, [(2, 2), (3, 1), (139, 1), (283, 1), (5273263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_283
    · exact prime_5273263
  · decide +kernel

theorem prime_2489212263023 : Nat.Prime 2489212263023 := by
  apply nodeValid_prime [2, 17, 19, 36527, 105491] ⟨2489212263023, 13, [(2, 1), (17, 1), (19, 1), (36527, 1), (105491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_36527
    · exact prime_105491
  · decide +kernel

theorem prime_2489212263121 : Nat.Prime 2489212263121 := by
  apply nodeValid_prime [2, 3, 5, 11, 127, 7424279] ⟨2489212263121, 7, [(2, 4), (3, 1), (5, 1), (11, 1), (127, 1), (7424279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_127
    · exact prime_7424279
  · decide +kernel

theorem prime_2491630322303 : Nat.Prime 2491630322303 := by
  apply nodeValid_prime [2, 11, 89, 409, 3111341] ⟨2491630322303, 5, [(2, 1), (11, 1), (89, 1), (409, 1), (3111341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
    · exact prime_409
    · exact prime_3111341
  · decide +kernel

theorem prime_2491630359727 : Nat.Prime 2491630359727 := by
  apply nodeValid_prime [2, 3, 415271726621] ⟨2491630359727, 3, [(2, 1), (3, 1), (415271726621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_415271726621
  · decide +kernel

theorem prime_2491630360081 : Nat.Prime 2491630360081 := by
  apply nodeValid_prime [2, 3, 5, 3049, 3404983] ⟨2491630360081, 26, [(2, 4), (3, 1), (5, 1), (3049, 1), (3404983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3049
    · exact prime_3404983
  · decide +kernel

theorem prime_2494050092161 : Nat.Prime 2494050092161 := by
  apply nodeValid_prime [2, 3, 5, 11, 751, 157243] ⟨2494050092161, 14, [(2, 7), (3, 1), (5, 1), (11, 1), (751, 1), (157243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_751
    · exact prime_157243
  · decide +kernel

theorem prime_2494050153037 : Nat.Prime 2494050153037 := by
  apply nodeValid_prime [2, 3, 13, 443, 859, 42013] ⟨2494050153037, 2, [(2, 2), (3, 1), (13, 1), (443, 1), (859, 1), (42013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_443
    · exact prime_859
    · exact prime_42013
  · decide +kernel

theorem prime_2496471443537 : Nat.Prime 2496471443537 := by
  apply nodeValid_prime [2, 7, 1697, 13134899] ⟨2496471443537, 3, [(2, 4), (7, 1), (1697, 1), (13134899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1697
    · exact prime_13134899
  · decide +kernel

theorem prime_2496471443629 : Nat.Prime 2496471443629 := by
  apply nodeValid_prime [2, 3, 208039286969] ⟨2496471443629, 2, [(2, 2), (3, 1), (208039286969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_208039286969
  · decide +kernel

theorem prime_2496471465877 : Nat.Prime 2496471465877 := by
  apply nodeValid_prime [2, 3, 4001, 51996823] ⟨2496471465877, 2, [(2, 2), (3, 1), (4001, 1), (51996823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4001
    · exact prime_51996823
  · decide +kernel

theorem prime_2498894428939 : Nat.Prime 2498894428939 := by
  apply nodeValid_prime [2, 3, 133853, 3111491] ⟨2498894428939, 2, [(2, 1), (3, 1), (133853, 1), (3111491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_133853
    · exact prime_3111491
  · decide +kernel

theorem prime_2498894488483 : Nat.Prime 2498894488483 := by
  apply nodeValid_prime [2, 3, 7, 523, 2039, 55793] ⟨2498894488483, 2, [(2, 1), (3, 1), (7, 1), (523, 1), (2039, 1), (55793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_523
    · exact prime_2039
    · exact prime_55793
  · decide +kernel

theorem prime_2498894488771 : Nat.Prime 2498894488771 := by
  apply nodeValid_prime [2, 3, 5, 83296482959] ⟨2498894488771, 3, [(2, 1), (3, 1), (5, 1), (83296482959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83296482959
  · decide +kernel

theorem prime_2501318984911 : Nat.Prime 2501318984911 := by
  apply nodeValid_prime [2, 3, 5, 29, 2875079293] ⟨2501318984911, 13, [(2, 1), (3, 1), (5, 1), (29, 1), (2875079293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_2875079293
  · decide +kernel

theorem prime_2501319034321 : Nat.Prime 2501319034321 := by
  apply nodeValid_prime [2, 3, 5, 7517, 1386479] ⟨2501319034321, 17, [(2, 4), (3, 1), (5, 1), (7517, 1), (1386479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7517
    · exact prime_1386479
  · decide +kernel

theorem prime_2501319034553 : Nat.Prime 2501319034553 := by
  apply nodeValid_prime [2, 13, 31, 139, 2281, 2447] ⟨2501319034553, 3, [(2, 3), (13, 1), (31, 1), (139, 1), (2281, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_139
    · exact prime_2281
    · exact prime_2447
  · decide +kernel

theorem prime_2503745121887 : Nat.Prime 2503745121887 := by
  apply nodeValid_prime [2, 37, 73, 1087, 426389] ⟨2503745121887, 5, [(2, 1), (37, 1), (73, 1), (1087, 1), (426389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_73
    · exact prime_1087
    · exact prime_426389
  · decide +kernel

theorem prime_2503745225693 : Nat.Prime 2503745225693 := by
  apply nodeValid_prime [2, 73, 89, 96342359] ⟨2503745225693, 2, [(2, 2), (73, 1), (89, 1), (96342359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_89
    · exact prime_96342359
  · decide +kernel

theorem prime_2503745226467 : Nat.Prime 2503745226467 := by
  apply nodeValid_prime [2, 11, 113806601203] ⟨2503745226467, 2, [(2, 1), (11, 1), (113806601203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113806601203
  · decide +kernel

theorem prime_2506172856487 : Nat.Prime 2506172856487 := by
  apply nodeValid_prime [2, 3, 13, 61, 526728217] ⟨2506172856487, 3, [(2, 1), (3, 1), (13, 1), (61, 1), (526728217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
    · exact prime_526728217
  · decide +kernel

theorem prime_2506173042319 : Nat.Prime 2506173042319 := by
  apply nodeValid_prime [2, 3, 11, 73, 520168751] ⟨2506173042319, 3, [(2, 1), (3, 1), (11, 1), (73, 1), (520168751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_520168751
  · decide +kernel

theorem prime_2506173043039 : Nat.Prime 2506173043039 := by
  apply nodeValid_prime [2, 3, 7, 103357, 577327] ⟨2506173043039, 3, [(2, 1), (3, 1), (7, 1), (103357, 1), (577327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103357
    · exact prime_577327
  · decide +kernel

theorem prime_2508602188789 : Nat.Prime 2508602188789 := by
  apply nodeValid_prime [2, 3, 463, 150504091] ⟨2508602188789, 10, [(2, 2), (3, 2), (463, 1), (150504091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
    · exact prime_150504091
  · decide +kernel

theorem prime_2508602205983 : Nat.Prime 2508602205983 := by
  apply nodeValid_prime [2, 17, 53, 1392121091] ⟨2508602205983, 5, [(2, 1), (17, 1), (53, 1), (1392121091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_53
    · exact prime_1392121091
  · decide +kernel

theorem prime_2508602206631 : Nat.Prime 2508602206631 := by
  apply nodeValid_prime [2, 5, 13, 31481, 612971] ⟨2508602206631, 11, [(2, 1), (5, 1), (13, 1), (31481, 1), (612971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31481
    · exact prime_612971
  · decide +kernel

theorem prime_2511033126211 : Nat.Prime 2511033126211 := by
  apply nodeValid_prime [2, 3, 5, 7, 10499, 379633] ⟨2511033126211, 10, [(2, 1), (3, 2), (5, 1), (7, 1), (10499, 1), (379633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_10499
    · exact prime_379633
  · decide +kernel

theorem prime_2511033129347 : Nat.Prime 2511033129347 := by
  apply nodeValid_prime [2, 7, 17, 10550559367] ⟨2511033129347, 2, [(2, 1), (7, 1), (17, 1), (10550559367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_10550559367
  · decide +kernel

theorem prime_2511033129629 : Nat.Prime 2511033129629 := by
  apply nodeValid_prime [2, 627758282407] ⟨2511033129629, 2, [(2, 2), (627758282407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_627758282407
  · decide +kernel

theorem prime_2513465460263 : Nat.Prime 2513465460263 := by
  apply nodeValid_prime [2, 37, 33965749463] ⟨2513465460263, 5, [(2, 1), (37, 1), (33965749463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_33965749463
  · decide +kernel

theorem prime_2513465461763 : Nat.Prime 2513465461763 := by
  apply nodeValid_prime [2, 443, 2836868467] ⟨2513465461763, 2, [(2, 1), (443, 1), (2836868467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_2836868467
  · decide +kernel

theorem prime_2513465659043 : Nat.Prime 2513465659043 := by
  apply nodeValid_prime [2, 13, 103, 491, 1911529] ⟨2513465659043, 2, [(2, 1), (13, 1), (103, 1), (491, 1), (1911529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_103
    · exact prime_491
    · exact prime_1911529
  · decide +kernel

theorem prime_2515899777271 : Nat.Prime 2515899777271 := by
  apply nodeValid_prime [2, 3, 5, 11, 7623938719] ⟨2515899777271, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (7623938719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_7623938719
  · decide +kernel

theorem prime_2515899778303 : Nat.Prime 2515899778303 := by
  apply nodeValid_prime [2, 3, 17, 2269, 10870729] ⟨2515899778303, 7, [(2, 1), (3, 1), (17, 1), (2269, 1), (10870729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2269
    · exact prime_10870729
  · decide +kernel

theorem prime_2515899791887 : Nat.Prime 2515899791887 := by
  apply nodeValid_prime [2, 3, 13, 59, 546697043] ⟨2515899791887, 3, [(2, 1), (3, 1), (13, 1), (59, 1), (546697043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_546697043
  · decide +kernel

theorem prime_2518335506591 : Nat.Prime 2518335506591 := by
  apply nodeValid_prime [2, 5, 456107, 552137] ⟨2518335506591, 7, [(2, 1), (5, 1), (456107, 1), (552137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_456107
    · exact prime_552137
  · decide +kernel

theorem prime_2518335506917 : Nat.Prime 2518335506917 := by
  apply nodeValid_prime [2, 3, 1721, 2819, 14419] ⟨2518335506917, 2, [(2, 2), (3, 2), (1721, 1), (2819, 1), (14419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1721
    · exact prime_2819
    · exact prime_14419
  · decide +kernel

theorem prime_2518335511603 : Nat.Prime 2518335511603 := by
  apply nodeValid_prime [2, 3, 419722585267] ⟨2518335511603, 2, [(2, 1), (3, 1), (419722585267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419722585267
  · decide +kernel

theorem prime_2520772817033 : Nat.Prime 2520772817033 := by
  apply nodeValid_prime [2, 19, 79631, 208261] ⟨2520772817033, 3, [(2, 3), (19, 1), (79631, 1), (208261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_79631
    · exact prime_208261
  · decide +kernel

theorem prime_2520772871887 : Nat.Prime 2520772871887 := by
  apply nodeValid_prime [2, 3, 71, 657478579] ⟨2520772871887, 7, [(2, 1), (3, 3), (71, 1), (657478579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_657478579
  · decide +kernel

theorem prime_2523211713119 : Nat.Prime 2523211713119 := by
  apply nodeValid_prime [2, 6199, 9319, 21839] ⟨2523211713119, 11, [(2, 1), (6199, 1), (9319, 1), (21839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_6199
    · exact prime_9319
    · exact prime_21839
  · decide +kernel

theorem prime_2523211713133 : Nat.Prime 2523211713133 := by
  apply nodeValid_prime [2, 3, 11, 37699, 507049] ⟨2523211713133, 5, [(2, 2), (3, 1), (11, 1), (37699, 1), (507049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37699
    · exact prime_507049
  · decide +kernel

theorem prime_2523211716127 : Nat.Prime 2523211716127 := by
  apply nodeValid_prime [2, 3, 1709, 246070969] ⟨2523211716127, 3, [(2, 1), (3, 1), (1709, 1), (246070969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1709
    · exact prime_246070969
  · decide +kernel

theorem prime_2525652159047 : Nat.Prime 2525652159047 := by
  apply nodeValid_prime [2, 43, 11369, 2583169] ⟨2525652159047, 5, [(2, 1), (43, 1), (11369, 1), (2583169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_11369
    · exact prime_2583169
  · decide +kernel

theorem prime_2525652159181 : Nat.Prime 2525652159181 := by
  apply nodeValid_prime [2, 3, 5, 1609, 26161717] ⟨2525652159181, 6, [(2, 2), (3, 1), (5, 1), (1609, 1), (26161717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1609
    · exact prime_26161717
  · decide +kernel

theorem prime_2525652208301 : Nat.Prime 2525652208301 := by
  apply nodeValid_prime [2, 5, 13, 89, 21829319] ⟨2525652208301, 2, [(2, 2), (5, 2), (13, 1), (89, 1), (21829319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_89
    · exact prime_21829319
  · decide +kernel

theorem prime_2528094278027 : Nat.Prime 2528094278027 := by
  apply nodeValid_prime [2, 47, 572225957] ⟨2528094278027, 2, [(2, 1), (47, 2), (572225957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_572225957
  · decide +kernel

theorem prime_2528094279121 : Nat.Prime 2528094279121 := by
  apply nodeValid_prime [2, 3, 5, 1753, 6008971] ⟨2528094279121, 17, [(2, 4), (3, 1), (5, 1), (1753, 1), (6008971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1753
    · exact prime_6008971
  · decide +kernel

theorem prime_2528094292037 : Nat.Prime 2528094292037 := by
  apply nodeValid_prime [2, 23, 127, 1237, 174917] ⟨2528094292037, 2, [(2, 2), (23, 1), (127, 1), (1237, 1), (174917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_127
    · exact prime_1237
    · exact prime_174917
  · decide +kernel

theorem prime_2530537972483 : Nat.Prime 2530537972483 := by
  apply nodeValid_prime [2, 3, 13, 19, 521, 1217, 2693] ⟨2530537972483, 2, [(2, 1), (3, 1), (13, 1), (19, 1), (521, 1), (1217, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_521
    · exact prime_1217
    · exact prime_2693
  · decide +kernel

theorem prime_2530537988603 : Nat.Prime 2530537988603 := by
  apply nodeValid_prime [2, 13, 79, 1232004863] ⟨2530537988603, 5, [(2, 1), (13, 1), (79, 1), (1232004863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_1232004863
  · decide +kernel

theorem prime_2530537988851 : Nat.Prime 2530537988851 := by
  apply nodeValid_prime [2, 3, 5, 29, 4813, 40289] ⟨2530537988851, 2, [(2, 1), (3, 2), (5, 2), (29, 1), (4813, 1), (40289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_4813
    · exact prime_40289
  · decide +kernel

theorem prime_2532983259383 : Nat.Prime 2532983259383 := by
  apply nodeValid_prime [2, 1621, 781302671] ⟨2532983259383, 5, [(2, 1), (1621, 1), (781302671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1621
    · exact prime_781302671
  · decide +kernel

theorem prime_2532983366657 : Nat.Prime 2532983366657 := by
  apply nodeValid_prime [2, 17, 145506857] ⟨2532983366657, 3, [(2, 10), (17, 1), (145506857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_145506857
  · decide +kernel

theorem prime_2532983367193 : Nat.Prime 2532983367193 := by
  apply nodeValid_prime [2, 3, 105540973633] ⟨2532983367193, 5, [(2, 3), (3, 1), (105540973633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105540973633
  · decide +kernel

theorem prime_2535430147171 : Nat.Prime 2535430147171 := by
  apply nodeValid_prime [2, 3, 5, 179, 523, 902767] ⟨2535430147171, 2, [(2, 1), (3, 1), (5, 1), (179, 1), (523, 1), (902767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_523
    · exact prime_902767
  · decide +kernel

theorem prime_2535430173487 : Nat.Prime 2535430173487 := by
  apply nodeValid_prime [2, 3, 7, 107, 293, 1925533] ⟨2535430173487, 5, [(2, 1), (3, 1), (7, 1), (107, 1), (293, 1), (1925533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_293
    · exact prime_1925533
  · decide +kernel

theorem prime_2535430174217 : Nat.Prime 2535430174217 := by
  apply nodeValid_prime [2, 31, 691, 14795237] ⟨2535430174217, 3, [(2, 3), (31, 1), (691, 1), (14795237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_691
    · exact prime_14795237
  · decide +kernel

theorem prime_2537878620493 : Nat.Prime 2537878620493 := by
  apply nodeValid_prime [2, 3, 17, 1559, 2659949] ⟨2537878620493, 2, [(2, 2), (3, 2), (17, 1), (1559, 1), (2659949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1559
    · exact prime_2659949
  · decide +kernel

theorem prime_2537878621987 : Nat.Prime 2537878621987 := by
  apply nodeValid_prime [2, 3, 23, 1163, 1756991] ⟨2537878621987, 3, [(2, 1), (3, 3), (23, 1), (1163, 1), (1756991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1163
    · exact prime_1756991
  · decide +kernel

theorem prime_2537878634587 : Nat.Prime 2537878634587 := by
  apply nodeValid_prime [2, 3, 149, 946263473] ⟨2537878634587, 3, [(2, 1), (3, 2), (149, 1), (946263473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_946263473
  · decide +kernel

end Sude.Lucas.Generated
