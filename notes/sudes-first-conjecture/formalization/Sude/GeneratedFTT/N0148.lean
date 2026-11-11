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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0128
import Sude.GeneratedFTT.N0140

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11161 : Nat.Prime 11161 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨11161, 7, [(2, 3), (3, 2), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_13921 : Nat.Prime 13921 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨13921, 7, [(2, 5), (3, 1), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_22787 : Nat.Prime 22787 := by
  apply nodeValid_prime [2, 11393] ⟨22787, 2, [(2, 1), (11393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11393
  · decide +kernel

theorem prime_24473 : Nat.Prime 24473 := by
  apply nodeValid_prime [2, 7, 19, 23] ⟨24473, 3, [(2, 3), (7, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_28393 : Nat.Prime 28393 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨28393, 15, [(2, 3), (3, 1), (7, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_36713 : Nat.Prime 36713 := by
  apply nodeValid_prime [2, 13, 353] ⟨36713, 3, [(2, 3), (13, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_353
  · decide +kernel

theorem prime_38039 : Nat.Prime 38039 := by
  apply nodeValid_prime [2, 7, 11, 13, 19] ⟨38039, 7, [(2, 1), (7, 1), (11, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_38839 : Nat.Prime 38839 := by
  apply nodeValid_prime [2, 3, 6473] ⟨38839, 6, [(2, 1), (3, 1), (6473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6473
  · decide +kernel

theorem prime_47419 : Nat.Prime 47419 := by
  apply nodeValid_prime [2, 3, 7, 1129] ⟨47419, 2, [(2, 1), (3, 1), (7, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1129
  · decide +kernel

theorem prime_47951 : Nat.Prime 47951 := by
  apply nodeValid_prime [2, 5, 7, 137] ⟨47951, 7, [(2, 1), (5, 2), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_48623 : Nat.Prime 48623 := by
  apply nodeValid_prime [2, 7, 23, 151] ⟨48623, 5, [(2, 1), (7, 1), (23, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_151
  · decide +kernel

theorem prime_48947 : Nat.Prime 48947 := by
  apply nodeValid_prime [2, 24473] ⟨48947, 2, [(2, 1), (24473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24473
  · decide +kernel

theorem prime_50839 : Nat.Prime 50839 := by
  apply nodeValid_prime [2, 3, 37, 229] ⟨50839, 3, [(2, 1), (3, 1), (37, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_229
  · decide +kernel

theorem prime_51973 : Nat.Prime 51973 := by
  apply nodeValid_prime [2, 3, 61, 71] ⟨51973, 2, [(2, 2), (3, 1), (61, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_71
  · decide +kernel

theorem prime_56957 : Nat.Prime 56957 := by
  apply nodeValid_prime [2, 29, 491] ⟨56957, 2, [(2, 2), (29, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_491
  · decide +kernel

theorem prime_57173 : Nat.Prime 57173 := by
  apply nodeValid_prime [2, 14293] ⟨57173, 2, [(2, 2), (14293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14293
  · decide +kernel

theorem prime_57641 : Nat.Prime 57641 := by
  apply nodeValid_prime [2, 5, 11, 131] ⟨57641, 3, [(2, 3), (5, 1), (11, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_131
  · decide +kernel

theorem prime_58477 : Nat.Prime 58477 := by
  apply nodeValid_prime [2, 3, 11, 443] ⟨58477, 5, [(2, 2), (3, 1), (11, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_443
  · decide +kernel

theorem prime_59611 : Nat.Prime 59611 := by
  apply nodeValid_prime [2, 3, 5, 1987] ⟨59611, 2, [(2, 1), (3, 1), (5, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1987
  · decide +kernel

theorem prime_64877 : Nat.Prime 64877 := by
  apply nodeValid_prime [2, 7, 331] ⟨64877, 3, [(2, 2), (7, 2), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_331
  · decide +kernel

theorem prime_67043 : Nat.Prime 67043 := by
  apply nodeValid_prime [2, 33521] ⟨67043, 2, [(2, 1), (33521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33521
  · decide +kernel

theorem prime_68711 : Nat.Prime 68711 := by
  apply nodeValid_prime [2, 5, 6871] ⟨68711, 11, [(2, 1), (5, 1), (6871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6871
  · decide +kernel

theorem prime_77731 : Nat.Prime 77731 := by
  apply nodeValid_prime [2, 3, 5, 2591] ⟨77731, 2, [(2, 1), (3, 1), (5, 1), (2591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2591
  · decide +kernel

theorem prime_79451 : Nat.Prime 79451 := by
  apply nodeValid_prime [2, 5, 7, 227] ⟨79451, 6, [(2, 1), (5, 2), (7, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_227
  · decide +kernel

theorem prime_80683 : Nat.Prime 80683 := by
  apply nodeValid_prime [2, 3, 7, 17, 113] ⟨80683, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_113
  · decide +kernel

theorem prime_87277 : Nat.Prime 87277 := by
  apply nodeValid_prime [2, 3, 7, 1039] ⟨87277, 5, [(2, 2), (3, 1), (7, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1039
  · decide +kernel

theorem prime_91591 : Nat.Prime 91591 := by
  apply nodeValid_prime [2, 3, 5, 43, 71] ⟨91591, 3, [(2, 1), (3, 1), (5, 1), (43, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_71
  · decide +kernel

theorem prime_102149 : Nat.Prime 102149 := by
  apply nodeValid_prime [2, 25537] ⟨102149, 2, [(2, 2), (25537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25537
  · decide +kernel

theorem prime_104231 : Nat.Prime 104231 := by
  apply nodeValid_prime [2, 5, 7, 1489] ⟨104231, 7, [(2, 1), (5, 1), (7, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1489
  · decide +kernel

theorem prime_107137 : Nat.Prime 107137 := by
  apply nodeValid_prime [2, 3, 31] ⟨107137, 10, [(2, 7), (3, 3), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_108041 : Nat.Prime 108041 := by
  apply nodeValid_prime [2, 5, 37, 73] ⟨108041, 6, [(2, 3), (5, 1), (37, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_73
  · decide +kernel

theorem prime_149921 : Nat.Prime 149921 := by
  apply nodeValid_prime [2, 5, 937] ⟨149921, 6, [(2, 5), (5, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_937
  · decide +kernel

theorem prime_158269 : Nat.Prime 158269 := by
  apply nodeValid_prime [2, 3, 11, 109] ⟨158269, 2, [(2, 2), (3, 1), (11, 2), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_192193 : Nat.Prime 192193 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨192193, 5, [(2, 6), (3, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_204299 : Nat.Prime 204299 := by
  apply nodeValid_prime [2, 102149] ⟨204299, 2, [(2, 1), (102149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_102149
  · decide +kernel

theorem prime_206651 : Nat.Prime 206651 := by
  apply nodeValid_prime [2, 5, 4133] ⟨206651, 2, [(2, 1), (5, 2), (4133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4133
  · decide +kernel

theorem prime_208463 : Nat.Prime 208463 := by
  apply nodeValid_prime [2, 104231] ⟨208463, 5, [(2, 1), (104231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_104231
  · decide +kernel

theorem prime_211499 : Nat.Prime 211499 := by
  apply nodeValid_prime [2, 7, 15107] ⟨211499, 6, [(2, 1), (7, 1), (15107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15107
  · decide +kernel

theorem prime_258623 : Nat.Prime 258623 := by
  apply nodeValid_prime [2, 7, 13, 29] ⟨258623, 7, [(2, 1), (7, 3), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_282091 : Nat.Prime 282091 := by
  apply nodeValid_prime [2, 3, 5, 9403] ⟨282091, 3, [(2, 1), (3, 1), (5, 1), (9403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9403
  · decide +kernel

theorem prime_299843 : Nat.Prime 299843 := by
  apply nodeValid_prime [2, 149921] ⟨299843, 2, [(2, 1), (149921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_149921
  · decide +kernel

theorem prime_319237 : Nat.Prime 319237 := by
  apply nodeValid_prime [2, 3, 37, 719] ⟨319237, 2, [(2, 2), (3, 1), (37, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_719
  · decide +kernel

theorem prime_346649 : Nat.Prime 346649 := by
  apply nodeValid_prime [2, 43331] ⟨346649, 3, [(2, 3), (43331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43331
  · decide +kernel

theorem prime_349109 : Nat.Prime 349109 := by
  apply nodeValid_prime [2, 87277] ⟨349109, 2, [(2, 2), (87277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_87277
  · decide +kernel

theorem prime_417881 : Nat.Prime 417881 := by
  apply nodeValid_prime [2, 5, 31, 337] ⟨417881, 3, [(2, 3), (5, 1), (31, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_337
  · decide +kernel

theorem prime_440731 : Nat.Prime 440731 := by
  apply nodeValid_prime [2, 3, 5, 59, 83] ⟨440731, 2, [(2, 1), (3, 2), (5, 1), (59, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_83
  · decide +kernel

theorem prime_449473 : Nat.Prime 449473 := by
  apply nodeValid_prime [2, 3, 2341] ⟨449473, 5, [(2, 6), (3, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2341
  · decide +kernel

theorem prime_495701 : Nat.Prime 495701 := by
  apply nodeValid_prime [2, 5, 4957] ⟨495701, 2, [(2, 2), (5, 2), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4957
  · decide +kernel

theorem prime_534431 : Nat.Prime 534431 := by
  apply nodeValid_prime [2, 5, 13, 4111] ⟨534431, 7, [(2, 1), (5, 1), (13, 1), (4111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4111
  · decide +kernel

theorem prime_538597 : Nat.Prime 538597 := by
  apply nodeValid_prime [2, 3, 4987] ⟨538597, 6, [(2, 2), (3, 3), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4987
  · decide +kernel

theorem prime_693697 : Nat.Prime 693697 := by
  apply nodeValid_prime [2, 3, 3613] ⟨693697, 5, [(2, 6), (3, 1), (3613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3613
  · decide +kernel

theorem prime_713833 : Nat.Prime 713833 := by
  apply nodeValid_prime [2, 3, 7, 607] ⟨713833, 5, [(2, 3), (3, 1), (7, 2), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_607
  · decide +kernel

theorem prime_732827 : Nat.Prime 732827 := by
  apply nodeValid_prime [2, 23, 89, 179] ⟨732827, 2, [(2, 1), (23, 1), (89, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_89
    · exact prime_179
  · decide +kernel

theorem prime_783131 : Nat.Prime 783131 := by
  apply nodeValid_prime [2, 5, 71, 1103] ⟨783131, 2, [(2, 1), (5, 1), (71, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_1103
  · decide +kernel

theorem prime_784181 : Nat.Prime 784181 := by
  apply nodeValid_prime [2, 5, 39209] ⟨784181, 2, [(2, 2), (5, 1), (39209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_39209
  · decide +kernel

theorem prime_838247 : Nat.Prime 838247 := by
  apply nodeValid_prime [2, 283, 1481] ⟨838247, 5, [(2, 1), (283, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_1481
  · decide +kernel

theorem prime_881813 : Nat.Prime 881813 := by
  apply nodeValid_prime [2, 89, 2477] ⟨881813, 2, [(2, 2), (89, 1), (2477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_2477
  · decide +kernel

theorem prime_1058461 : Nat.Prime 1058461 := by
  apply nodeValid_prime [2, 3, 5, 13, 23, 59] ⟨1058461, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (23, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_1566263 : Nat.Prime 1566263 := by
  apply nodeValid_prime [2, 783131] ⟨1566263, 5, [(2, 1), (783131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_783131
  · decide +kernel

theorem prime_1586023 : Nat.Prime 1586023 := by
  apply nodeValid_prime [2, 3, 31, 8527] ⟨1586023, 3, [(2, 1), (3, 1), (31, 1), (8527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_8527
  · decide +kernel

theorem prime_1674151 : Nat.Prime 1674151 := by
  apply nodeValid_prime [2, 3, 5, 11161] ⟨1674151, 3, [(2, 1), (3, 1), (5, 2), (11161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11161
  · decide +kernel

theorem prime_1699793 : Nat.Prime 1699793 := by
  apply nodeValid_prime [2, 23, 31, 149] ⟨1699793, 3, [(2, 4), (23, 1), (31, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_149
  · decide +kernel

theorem prime_1763627 : Nat.Prime 1763627 := by
  apply nodeValid_prime [2, 881813] ⟨1763627, 2, [(2, 1), (881813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_881813
  · decide +kernel

theorem prime_1902539 : Nat.Prime 1902539 := by
  apply nodeValid_prime [2, 11, 17, 5087] ⟨1902539, 2, [(2, 1), (11, 1), (17, 1), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_5087
  · decide +kernel

theorem prime_1928467 : Nat.Prime 1928467 := by
  apply nodeValid_prime [2, 3, 107137] ⟨1928467, 2, [(2, 1), (3, 2), (107137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107137
  · decide +kernel

theorem prime_2790769 : Nat.Prime 2790769 := by
  apply nodeValid_prime [2, 3, 53, 1097] ⟨2790769, 13, [(2, 4), (3, 1), (53, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1097
  · decide +kernel

theorem prime_2845303 : Nat.Prime 2845303 := by
  apply nodeValid_prime [2, 3, 199, 2383] ⟨2845303, 3, [(2, 1), (3, 1), (199, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_2383
  · decide +kernel

theorem prime_2921951 : Nat.Prime 2921951 := by
  apply nodeValid_prime [2, 5, 58439] ⟨2921951, 14, [(2, 1), (5, 2), (58439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_58439
  · decide +kernel

theorem prime_2936821 : Nat.Prime 2936821 := by
  apply nodeValid_prime [2, 3, 5, 48947] ⟨2936821, 2, [(2, 2), (3, 1), (5, 1), (48947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_48947
  · decide +kernel

theorem prime_3407161 : Nat.Prime 3407161 := by
  apply nodeValid_prime [2, 3, 5, 28393] ⟨3407161, 31, [(2, 3), (3, 1), (5, 1), (28393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28393
  · decide +kernel

theorem prime_3438767 : Nat.Prime 3438767 := by
  apply nodeValid_prime [2, 107, 16069] ⟨3438767, 5, [(2, 1), (107, 1), (16069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_16069
  · decide +kernel

theorem prime_4123787 : Nat.Prime 4123787 := by
  apply nodeValid_prime [2, 43, 47951] ⟨4123787, 2, [(2, 1), (43, 1), (47951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_47951
  · decide +kernel

theorem prime_4272157 : Nat.Prime 4272157 := by
  apply nodeValid_prime [2, 3, 7, 5651] ⟨4272157, 2, [(2, 2), (3, 3), (7, 1), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5651
  · decide +kernel

theorem prime_4853087 : Nat.Prime 4853087 := by
  apply nodeValid_prime [2, 7, 346649] ⟨4853087, 7, [(2, 1), (7, 1), (346649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_346649
  · decide +kernel

theorem prime_5107793 : Nat.Prime 5107793 := by
  apply nodeValid_prime [2, 319237] ⟨5107793, 3, [(2, 4), (319237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_319237
  · decide +kernel

theorem prime_5393677 : Nat.Prime 5393677 := by
  apply nodeValid_prime [2, 3, 449473] ⟨5393677, 2, [(2, 2), (3, 1), (449473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449473
  · decide +kernel

theorem prime_7791499 : Nat.Prime 7791499 := by
  apply nodeValid_prime [2, 3, 11, 13, 1009] ⟨7791499, 11, [(2, 1), (3, 3), (11, 1), (13, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1009
  · decide +kernel

theorem prime_8253911 : Nat.Prime 8253911 := by
  apply nodeValid_prime [2, 5, 7, 61, 1933] ⟨8253911, 14, [(2, 1), (5, 1), (7, 1), (61, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_1933
  · decide +kernel

theorem prime_8520737 : Nat.Prime 8520737 := by
  apply nodeValid_prime [2, 7, 38039] ⟨8520737, 3, [(2, 5), (7, 1), (38039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_38039
  · decide +kernel

theorem prime_10444073 : Nat.Prime 10444073 := by
  apply nodeValid_prime [2, 19, 68711] ⟨10444073, 3, [(2, 3), (19, 1), (68711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_68711
  · decide +kernel

theorem prime_10581763 : Nat.Prime 10581763 := by
  apply nodeValid_prime [2, 3, 1763627] ⟨10581763, 2, [(2, 1), (3, 1), (1763627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1763627
  · decide +kernel

theorem prime_11126473 : Nat.Prime 11126473 := by
  apply nodeValid_prime [2, 3, 7, 103, 643] ⟨11126473, 5, [(2, 3), (3, 1), (7, 1), (103, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_643
  · decide +kernel

theorem prime_11163077 : Nat.Prime 11163077 := by
  apply nodeValid_prime [2, 2790769] ⟨11163077, 2, [(2, 2), (2790769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2790769
  · decide +kernel

theorem prime_11641351 : Nat.Prime 11641351 := by
  apply nodeValid_prime [2, 3, 5, 7, 11087] ⟨11641351, 6, [(2, 1), (3, 1), (5, 2), (7, 1), (11087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11087
  · decide +kernel

theorem prime_12864941 : Nat.Prime 12864941 := by
  apply nodeValid_prime [2, 5, 11, 58477] ⟨12864941, 2, [(2, 2), (5, 1), (11, 1), (58477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_58477
  · decide +kernel

theorem prime_14482889 : Nat.Prime 14482889 := by
  apply nodeValid_prime [2, 7, 258623] ⟨14482889, 3, [(2, 3), (7, 1), (258623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_258623
  · decide +kernel

theorem prime_14780741 : Nat.Prime 14780741 := by
  apply nodeValid_prime [2, 5, 13, 4373] ⟨14780741, 2, [(2, 2), (5, 1), (13, 2), (4373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4373
  · decide +kernel

theorem prime_16507823 : Nat.Prime 16507823 := by
  apply nodeValid_prime [2, 8253911] ⟨16507823, 5, [(2, 1), (8253911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8253911
  · decide +kernel

theorem prime_17872223 : Nat.Prime 17872223 := by
  apply nodeValid_prime [2, 997, 8963] ⟨17872223, 5, [(2, 1), (997, 1), (8963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_997
    · exact prime_8963
  · decide +kernel

theorem prime_17893189 : Nat.Prime 17893189 := by
  apply nodeValid_prime [2, 3, 307, 1619] ⟨17893189, 7, [(2, 2), (3, 2), (307, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_1619
  · decide +kernel

theorem prime_25852657 : Nat.Prime 25852657 := by
  apply nodeValid_prime [2, 3, 538597] ⟨25852657, 7, [(2, 4), (3, 1), (538597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_538597
  · decide +kernel

theorem prime_37516651 : Nat.Prime 37516651 := by
  apply nodeValid_prime [2, 3, 5, 67, 3733] ⟨37516651, 7, [(2, 1), (3, 1), (5, 2), (67, 1), (3733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_3733
  · decide +kernel

theorem prime_44298431 : Nat.Prime 44298431 := by
  apply nodeValid_prime [2, 5, 11, 17, 23689] ⟨44298431, 7, [(2, 1), (5, 1), (11, 1), (17, 1), (23689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_23689
  · decide +kernel

theorem prime_62664439 : Nat.Prime 62664439 := by
  apply nodeValid_prime [2, 3, 10444073] ⟨62664439, 3, [(2, 1), (3, 1), (10444073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10444073
  · decide +kernel

theorem prime_69434737 : Nat.Prime 69434737 := by
  apply nodeValid_prime [2, 3, 7, 206651] ⟨69434737, 5, [(2, 4), (3, 1), (7, 1), (206651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_206651
  · decide +kernel

theorem prime_82219229 : Nat.Prime 82219229 := by
  apply nodeValid_prime [2, 7, 13, 107, 2111] ⟨82219229, 2, [(2, 2), (7, 1), (13, 1), (107, 1), (2111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_107
    · exact prime_2111
  · decide +kernel

theorem prime_91518671 : Nat.Prime 91518671 := by
  apply nodeValid_prime [2, 5, 193, 47419] ⟨91518671, 37, [(2, 1), (5, 1), (193, 1), (47419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
    · exact prime_47419
  · decide +kernel

theorem prime_118245929 : Nat.Prime 118245929 := by
  apply nodeValid_prime [2, 14780741] ⟨118245929, 3, [(2, 3), (14780741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14780741
  · decide +kernel

theorem prime_120828077 : Nat.Prime 120828077 := by
  apply nodeValid_prime [2, 2897, 10427] ⟨120828077, 2, [(2, 2), (2897, 1), (10427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2897
    · exact prime_10427
  · decide +kernel

theorem prime_128845723 : Nat.Prime 128845723 := by
  apply nodeValid_prime [2, 3, 331, 64877] ⟨128845723, 2, [(2, 1), (3, 1), (331, 1), (64877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
    · exact prime_64877
  · decide +kernel

theorem prime_159756287 : Nat.Prime 159756287 := by
  apply nodeValid_prime [2, 109, 732827] ⟨159756287, 5, [(2, 1), (109, 1), (732827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_732827
  · decide +kernel

theorem prime_163849501 : Nat.Prime 163849501 := by
  apply nodeValid_prime [2, 3, 5, 53, 229] ⟨163849501, 10, [(2, 2), (3, 3), (5, 3), (53, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_229
  · decide +kernel

theorem prime_164438459 : Nat.Prime 164438459 := by
  apply nodeValid_prime [2, 82219229] ⟨164438459, 2, [(2, 1), (82219229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82219229
  · decide +kernel

theorem prime_173794669 : Nat.Prime 173794669 := by
  apply nodeValid_prime [2, 3, 14482889] ⟨173794669, 6, [(2, 2), (3, 1), (14482889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14482889
  · decide +kernel

theorem prime_179549389 : Nat.Prime 179549389 := by
  apply nodeValid_prime [2, 3, 1697, 2939] ⟨179549389, 2, [(2, 2), (3, 2), (1697, 1), (2939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1697
    · exact prime_2939
  · decide +kernel

theorem prime_206815909 : Nat.Prime 206815909 := by
  apply nodeValid_prime [2, 3, 13, 23, 57641] ⟨206815909, 2, [(2, 2), (3, 1), (13, 1), (23, 1), (57641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_57641
  · decide +kernel

theorem prime_223261541 : Nat.Prime 223261541 := by
  apply nodeValid_prime [2, 5, 11163077] ⟨223261541, 2, [(2, 2), (5, 1), (11163077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11163077
  · decide +kernel

theorem prime_239515613 : Nat.Prime 239515613 := by
  apply nodeValid_prime [2, 7, 233, 36713] ⟨239515613, 2, [(2, 2), (7, 1), (233, 1), (36713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_233
    · exact prime_36713
  · decide +kernel

theorem prime_257300359 : Nat.Prime 257300359 := by
  apply nodeValid_prime [2, 3, 7, 419, 14621] ⟨257300359, 3, [(2, 1), (3, 1), (7, 1), (419, 1), (14621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_419
    · exact prime_14621
  · decide +kernel

theorem prime_313441519 : Nat.Prime 313441519 := by
  apply nodeValid_prime [2, 3, 13, 19, 211499] ⟨313441519, 6, [(2, 1), (3, 1), (13, 1), (19, 1), (211499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_211499
  · decide +kernel

theorem prime_318673937 : Nat.Prime 318673937 := by
  apply nodeValid_prime [2, 7, 2845303] ⟨318673937, 3, [(2, 4), (7, 1), (2845303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2845303
  · decide +kernel

theorem prime_446523083 : Nat.Prime 446523083 := by
  apply nodeValid_prime [2, 223261541] ⟨446523083, 2, [(2, 1), (223261541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_223261541
  · decide +kernel

theorem prime_586518259 : Nat.Prime 586518259 := by
  apply nodeValid_prime [2, 3, 17, 19, 127, 2383] ⟨586518259, 3, [(2, 1), (3, 1), (17, 1), (19, 1), (127, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_127
    · exact prime_2383
  · decide +kernel

theorem prime_706478293 : Nat.Prime 706478293 := by
  apply nodeValid_prime [2, 3, 13, 19, 79451] ⟨706478293, 2, [(2, 2), (3, 2), (13, 1), (19, 1), (79451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_79451
  · decide +kernel

theorem prime_863861917 : Nat.Prime 863861917 := by
  apply nodeValid_prime [2, 3, 43, 1674151] ⟨863861917, 5, [(2, 2), (3, 1), (43, 1), (1674151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1674151
  · decide +kernel

theorem prime_1462103927 : Nat.Prime 1462103927 := by
  apply nodeValid_prime [2, 89, 379, 21673] ⟨1462103927, 5, [(2, 1), (89, 1), (379, 1), (21673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_379
    · exact prime_21673
  · decide +kernel

theorem prime_1597660433 : Nat.Prime 1597660433 := by
  apply nodeValid_prime [2, 479, 208463] ⟨1597660433, 3, [(2, 4), (479, 1), (208463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_208463
  · decide +kernel

theorem prime_2083042111 : Nat.Prime 2083042111 := by
  apply nodeValid_prime [2, 3, 5, 69434737] ⟨2083042111, 13, [(2, 1), (3, 1), (5, 1), (69434737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_69434737
  · decide +kernel

theorem prime_5540193569 : Nat.Prime 5540193569 := by
  apply nodeValid_prime [2, 7, 13, 1902539] ⟨5540193569, 3, [(2, 5), (7, 1), (13, 1), (1902539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1902539
  · decide +kernel

theorem prime_16138184497 : Nat.Prime 16138184497 := by
  apply nodeValid_prime [2, 3, 7, 41, 113, 1481] ⟨16138184497, 11, [(2, 4), (3, 1), (7, 2), (41, 1), (113, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_113
    · exact prime_1481
  · decide +kernel

theorem prime_21893473403 : Nat.Prime 21893473403 := by
  apply nodeValid_prime [2, 56957, 192193] ⟨21893473403, 2, [(2, 1), (56957, 1), (192193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_56957
    · exact prime_192193
  · decide +kernel

theorem prime_26081237893 : Nat.Prime 26081237893 := by
  apply nodeValid_prime [2, 3, 27961, 77731] ⟨26081237893, 5, [(2, 2), (3, 1), (27961, 1), (77731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27961
    · exact prime_77731
  · decide +kernel

theorem prime_40425581689 : Nat.Prime 40425581689 := by
  apply nodeValid_prime [2, 3, 13921, 120997] ⟨40425581689, 7, [(2, 3), (3, 1), (13921, 1), (120997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13921
    · exact prime_120997
  · decide +kernel

theorem prime_43786946351 : Nat.Prime 43786946351 := by
  apply nodeValid_prime [2, 5, 7, 17872223] ⟨43786946351, 11, [(2, 1), (5, 2), (7, 2), (17872223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17872223
  · decide +kernel

theorem prime_46744763183 : Nat.Prime 46744763183 := by
  apply nodeValid_prime [2, 13, 211, 8520737] ⟨46744763183, 10, [(2, 1), (13, 1), (211, 1), (8520737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_211
    · exact prime_8520737
  · decide +kernel

theorem prime_54584011241 : Nat.Prime 54584011241 := by
  apply nodeValid_prime [2, 5, 11, 23, 5393677] ⟨54584011241, 3, [(2, 3), (5, 1), (11, 1), (23, 1), (5393677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_5393677
  · decide +kernel

theorem prime_54629619199 : Nat.Prime 54629619199 := by
  apply nodeValid_prime [2, 3, 7, 11, 118245929] ⟨54629619199, 7, [(2, 1), (3, 1), (7, 1), (11, 1), (118245929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_118245929
  · decide +kernel

theorem prime_56042393237 : Nat.Prime 56042393237 := by
  apply nodeValid_prime [2, 19, 1063, 693697] ⟨56042393237, 2, [(2, 2), (19, 1), (1063, 1), (693697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1063
    · exact prime_693697
  · decide +kernel

theorem prime_65767459063 : Nat.Prime 65767459063 := by
  apply nodeValid_prime [2, 3, 53, 206815909] ⟨65767459063, 3, [(2, 1), (3, 1), (53, 1), (206815909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_206815909
  · decide +kernel

theorem prime_89537517757 : Nat.Prime 89537517757 := by
  apply nodeValid_prime [2, 3, 139, 17893189] ⟨89537517757, 5, [(2, 2), (3, 2), (139, 1), (17893189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_17893189
  · decide +kernel

theorem prime_93951364973 : Nat.Prime 93951364973 := by
  apply nodeValid_prime [2, 7703, 3049181] ⟨93951364973, 2, [(2, 2), (7703, 1), (3049181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7703
    · exact prime_3049181
  · decide +kernel

theorem prime_101266213267 : Nat.Prime 101266213267 := by
  apply nodeValid_prime [2, 3, 127, 44298431] ⟨101266213267, 2, [(2, 1), (3, 2), (127, 1), (44298431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_44298431
  · decide +kernel

theorem prime_120008308181 : Nat.Prime 120008308181 := by
  apply nodeValid_prime [2, 5, 5669, 1058461] ⟨120008308181, 2, [(2, 2), (5, 1), (5669, 1), (1058461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5669
    · exact prime_1058461
  · decide +kernel

theorem prime_149825046083 : Nat.Prime 149825046083 := by
  apply nodeValid_prime [2, 239, 313441519] ⟨149825046083, 2, [(2, 1), (239, 1), (313441519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_313441519
  · decide +kernel

theorem prime_161381844971 : Nat.Prime 161381844971 := by
  apply nodeValid_prime [2, 5, 16138184497] ⟨161381844971, 2, [(2, 1), (5, 1), (16138184497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16138184497
  · decide +kernel

theorem prime_185221983839 : Nat.Prime 185221983839 := by
  apply nodeValid_prime [2, 17, 6947, 784181] ⟨185221983839, 7, [(2, 1), (17, 1), (6947, 1), (784181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_6947
    · exact prime_784181
  · decide +kernel

theorem prime_224290380091 : Nat.Prime 224290380091 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 4297, 14621] ⟨224290380091, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (4297, 1), (14621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_4297
    · exact prime_14621
  · decide +kernel

theorem prime_312415970813 : Nat.Prime 312415970813 := by
  apply nodeValid_prime [2, 11, 61, 10581763] ⟨312415970813, 2, [(2, 2), (11, 2), (61, 1), (10581763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_10581763
  · decide +kernel

theorem prime_368729608831 : Nat.Prime 368729608831 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 233, 282091] ⟨368729608831, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (233, 1), (282091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_233
    · exact prime_282091
  · decide +kernel

theorem prime_405064853069 : Nat.Prime 405064853069 := by
  apply nodeValid_prime [2, 101266213267] ⟨405064853069, 2, [(2, 2), (101266213267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_101266213267
  · decide +kernel

theorem prime_453965132501 : Nat.Prime 453965132501 := by
  apply nodeValid_prime [2, 5, 11, 16507823] ⟨453965132501, 3, [(2, 2), (5, 4), (11, 1), (16507823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_16507823
  · decide +kernel

theorem prime_1020070625807 : Nat.Prime 1020070625807 := by
  apply nodeValid_prime [2, 19, 9187, 2921951] ⟨1020070625807, 5, [(2, 1), (19, 1), (9187, 1), (2921951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_9187
    · exact prime_2921951
  · decide +kernel

theorem prime_4069489633361 : Nat.Prime 4069489633361 := by
  apply nodeValid_prime [2, 5, 421, 120828077] ⟨4069489633361, 3, [(2, 4), (5, 1), (421, 1), (120828077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_421
    · exact prime_120828077
  · decide +kernel

theorem prime_8058376525811 : Nat.Prime 8058376525811 := by
  apply nodeValid_prime [2, 5, 13, 61, 17047, 59611] ⟨8058376525811, 2, [(2, 1), (5, 1), (13, 1), (61, 1), (17047, 1), (59611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_61
    · exact prime_17047
    · exact prime_59611
  · decide +kernel

theorem prime_8058376597529 : Nat.Prime 8058376597529 := by
  apply nodeValid_prime [2, 47, 829, 25852657] ⟨8058376597529, 3, [(2, 3), (47, 1), (829, 1), (25852657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_829
    · exact prime_25852657
  · decide +kernel

theorem prime_8058376598131 : Nat.Prime 8058376598131 := by
  apply nodeValid_prime [2, 3, 5, 89537517757] ⟨8058376598131, 2, [(2, 1), (3, 2), (5, 1), (89537517757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89537517757
  · decide +kernel

theorem prime_8063733152443 : Nat.Prime 8063733152443 := by
  apply nodeValid_prime [2, 3, 11, 743, 164438459] ⟨8063733152443, 11, [(2, 1), (3, 1), (11, 1), (743, 1), (164438459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_743
    · exact prime_164438459
  · decide +kernel

theorem prime_8063733283183 : Nat.Prime 8063733283183 := by
  apply nodeValid_prime [2, 3, 13421, 11126473] ⟨8063733283183, 19, [(2, 1), (3, 3), (13421, 1), (11126473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13421
    · exact prime_11126473
  · decide +kernel

theorem prime_8063733284227 : Nat.Prime 8063733284227 := by
  apply nodeValid_prime [2, 3, 534431, 838247] ⟨8063733284227, 2, [(2, 1), (3, 2), (534431, 1), (838247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_534431
    · exact prime_838247
  · decide +kernel

theorem prime_8069092185461 : Nat.Prime 8069092185461 := by
  apply nodeValid_prime [2, 5, 23, 37, 89, 599, 8893] ⟨8069092185461, 2, [(2, 2), (5, 1), (23, 1), (37, 1), (89, 1), (599, 1), (8893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_89
    · exact prime_599
    · exact prime_8893
  · decide +kernel

theorem prime_8069092248551 : Nat.Prime 8069092248551 := by
  apply nodeValid_prime [2, 5, 161381844971] ⟨8069092248551, 11, [(2, 1), (5, 2), (161381844971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_161381844971
  · decide +kernel

theorem prime_8069092248599 : Nat.Prime 8069092248599 := by
  apply nodeValid_prime [2, 173, 181, 128845723] ⟨8069092248599, 7, [(2, 1), (173, 1), (181, 1), (128845723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_181
    · exact prime_128845723
  · decide +kernel

theorem prime_8074453628827 : Nat.Prime 8074453628827 := by
  apply nodeValid_prime [2, 3, 13, 41, 197, 4272157] ⟨8074453628827, 2, [(2, 1), (3, 2), (13, 1), (41, 1), (197, 1), (4272157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_197
    · exact prime_4272157
  · decide +kernel

theorem prime_8074453681529 : Nat.Prime 8074453681529 := by
  apply nodeValid_prime [2, 13, 22787, 3407161] ⟨8074453681529, 3, [(2, 3), (13, 1), (22787, 1), (3407161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_22787
    · exact prime_3407161
  · decide +kernel

theorem prime_8074453683277 : Nat.Prime 8074453683277 := by
  apply nodeValid_prime [2, 3, 224290380091] ⟨8074453683277, 5, [(2, 2), (3, 2), (224290380091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_224290380091
  · decide +kernel

theorem prime_8079817387679 : Nat.Prime 8079817387679 := by
  apply nodeValid_prime [2, 43, 93951364973] ⟨8079817387679, 7, [(2, 1), (43, 1), (93951364973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_93951364973
  · decide +kernel

theorem prime_8079817387907 : Nat.Prime 8079817387907 := by
  apply nodeValid_prime [2, 11, 4013, 91518671] ⟨8079817387907, 2, [(2, 1), (11, 1), (4013, 1), (91518671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4013
    · exact prime_91518671
  · decide +kernel

theorem prime_8079817478543 : Nat.Prime 8079817478543 := by
  apply nodeValid_prime [2, 37, 569, 11587, 16561] ⟨8079817478543, 5, [(2, 1), (37, 1), (569, 1), (11587, 1), (16561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_569
    · exact prime_11587
    · exact prime_16561
  · decide +kernel

theorem prime_8085183640757 : Nat.Prime 8085183640757 := by
  apply nodeValid_prime [2, 467, 2729, 1586023] ⟨8085183640757, 2, [(2, 2), (467, 1), (2729, 1), (1586023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_467
    · exact prime_2729
    · exact prime_1586023
  · decide +kernel

theorem prime_8085183641453 : Nat.Prime 8085183641453 := by
  apply nodeValid_prime [2, 37, 54629619199] ⟨8085183641453, 2, [(2, 2), (37, 1), (54629619199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_54629619199
  · decide +kernel

theorem prime_8085183746831 : Nat.Prime 8085183746831 := by
  apply nodeValid_prime [2, 5, 31, 26081237893] ⟨8085183746831, 7, [(2, 1), (5, 1), (31, 1), (26081237893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_26081237893
  · decide +kernel

theorem prime_8090552432713 : Nat.Prime 8090552432713 := by
  apply nodeValid_prime [2, 3, 211, 1597660433] ⟨8090552432713, 5, [(2, 3), (3, 1), (211, 1), (1597660433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_1597660433
  · decide +kernel

theorem prime_8090552488397 : Nat.Prime 8090552488397 := by
  apply nodeValid_prime [2, 7, 1123, 257300359] ⟨8090552488397, 2, [(2, 2), (7, 1), (1123, 1), (257300359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1123
    · exact prime_257300359
  · decide +kernel

theorem prime_8090552488483 : Nat.Prime 8090552488483 := by
  apply nodeValid_prime [2, 3, 149825046083] ⟨8090552488483, 2, [(2, 1), (3, 3), (149825046083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149825046083
  · decide +kernel

theorem prime_8095923212467 : Nat.Prime 8095923212467 := by
  apply nodeValid_prime [2, 3, 137, 191, 563, 91591] ⟨8095923212467, 2, [(2, 1), (3, 1), (137, 1), (191, 1), (563, 1), (91591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_191
    · exact prime_563
    · exact prime_91591
  · decide +kernel

theorem prime_8095923214033 : Nat.Prime 8095923214033 := by
  apply nodeValid_prime [2, 3, 17, 107, 1907, 48623] ⟨8095923214033, 5, [(2, 4), (3, 1), (17, 1), (107, 1), (1907, 1), (48623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_107
    · exact prime_1907
    · exact prime_48623
  · decide +kernel

theorem prime_8095923535771 : Nat.Prime 8095923535771 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 101, 3438767] ⟨8095923535771, 10, [(2, 1), (3, 2), (5, 1), (7, 1), (37, 1), (101, 1), (3438767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_101
    · exact prime_3438767
  · decide +kernel

theorem prime_8101297057627 : Nat.Prime 8101297057627 := by
  apply nodeValid_prime [2, 3, 521, 863861917] ⟨8101297057627, 3, [(2, 1), (3, 2), (521, 1), (863861917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_863861917
  · decide +kernel

theorem prime_8101297061381 : Nat.Prime 8101297061381 := by
  apply nodeValid_prime [2, 5, 405064853069] ⟨8101297061381, 2, [(2, 2), (5, 1), (405064853069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_405064853069
  · decide +kernel

theorem prime_8101297061551 : Nat.Prime 8101297061551 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 61, 107, 113, 317] ⟨8101297061551, 6, [(2, 1), (3, 2), (5, 2), (7, 1), (11, 1), (61, 1), (107, 1), (113, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_61
    · exact prime_107
    · exact prime_113
    · exact prime_317
  · decide +kernel

theorem prime_8106672981383 : Nat.Prime 8106672981383 := by
  apply nodeValid_prime [2, 108041, 37516651] ⟨8106672981383, 5, [(2, 1), (108041, 1), (37516651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_108041
    · exact prime_37516651
  · decide +kernel

theorem prime_8106673025189 : Nat.Prime 8106673025189 := by
  apply nodeValid_prime [2, 191, 67043, 158269] ⟨8106673025189, 2, [(2, 2), (191, 1), (67043, 1), (158269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_67043
    · exact prime_158269
  · decide +kernel

theorem prime_8106673027529 : Nat.Prime 8106673027529 := by
  apply nodeValid_prime [2, 6343, 159756287] ⟨8106673027529, 3, [(2, 3), (6343, 1), (159756287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6343
    · exact prime_159756287
  · decide +kernel

theorem prime_8112051318169 : Nat.Prime 8112051318169 := by
  apply nodeValid_prime [2, 3, 7, 17, 557, 1699793] ⟨8112051318169, 22, [(2, 3), (3, 2), (7, 1), (17, 1), (557, 1), (1699793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_557
    · exact prime_1699793
  · decide +kernel

theorem prime_8112051394283 : Nat.Prime 8112051394283 := by
  apply nodeValid_prime [2, 11, 368729608831] ⟨8112051394283, 2, [(2, 1), (11, 1), (368729608831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_368729608831
  · decide +kernel

theorem prime_8112051394589 : Nat.Prime 8112051394589 := by
  apply nodeValid_prime [2, 417881, 4853087] ⟨8112051394589, 2, [(2, 2), (417881, 1), (4853087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_417881
    · exact prime_4853087
  · decide +kernel

theorem prime_8117431978543 : Nat.Prime 8117431978543 := by
  apply nodeValid_prime [2, 3, 23, 359, 163849501] ⟨8117431978543, 3, [(2, 1), (3, 1), (23, 1), (359, 1), (163849501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_359
    · exact prime_163849501
  · decide +kernel

theorem prime_8117431980421 : Nat.Prime 8117431980421 := by
  apply nodeValid_prime [2, 3, 5, 7, 6581, 2936821] ⟨8117431980421, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (6581, 1), (2936821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_6581
    · exact prime_2936821
  · decide +kernel

theorem prime_8117432074217 : Nat.Prime 8117432074217 := by
  apply nodeValid_prime [2, 19, 47, 14083, 80683] ⟨8117432074217, 3, [(2, 3), (19, 1), (47, 1), (14083, 1), (80683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_14083
    · exact prime_80683
  · decide +kernel

theorem prime_8122815239723 : Nat.Prime 8122815239723 := by
  apply nodeValid_prime [2, 23369, 173794669] ⟨8122815239723, 2, [(2, 1), (23369, 1), (173794669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23369
    · exact prime_173794669
  · decide +kernel

theorem prime_8122815240937 : Nat.Prime 8122815240937 := by
  apply nodeValid_prime [2, 3, 11, 491, 62664439] ⟨8122815240937, 5, [(2, 3), (3, 1), (11, 1), (491, 1), (62664439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_491
    · exact prime_62664439
  · decide +kernel

theorem prime_8122815241139 : Nat.Prime 8122815241139 := by
  apply nodeValid_prime [2, 13, 312415970813] ⟨8122815241139, 2, [(2, 1), (13, 1), (312415970813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_312415970813
  · decide +kernel

theorem prime_8128200812519 : Nat.Prime 8128200812519 := by
  apply nodeValid_prime [2, 349109, 11641351] ⟨8128200812519, 7, [(2, 1), (349109, 1), (11641351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_349109
    · exact prime_11641351
  · decide +kernel

theorem prime_8128200837787 : Nat.Prime 8128200837787 := by
  apply nodeValid_prime [2, 3, 19, 9151, 7791499] ⟨8128200837787, 2, [(2, 1), (3, 1), (19, 1), (9151, 1), (7791499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_9151
    · exact prime_7791499
  · decide +kernel

theorem prime_8128200840031 : Nat.Prime 8128200840031 := by
  apply nodeValid_prime [2, 3, 5, 503, 179549389] ⟨8128200840031, 3, [(2, 1), (3, 2), (5, 1), (503, 1), (179549389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_503
    · exact prime_179549389
  · decide +kernel

theorem prime_8133588793843 : Nat.Prime 8133588793843 := by
  apply nodeValid_prime [2, 3, 29, 46744763183] ⟨8133588793843, 2, [(2, 1), (3, 1), (29, 1), (46744763183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_46744763183
  · decide +kernel

theorem prime_8133588803609 : Nat.Prime 8133588803609 := by
  apply nodeValid_prime [2, 587, 14737, 117529] ⟨8133588803609, 3, [(2, 3), (587, 1), (14737, 1), (117529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_587
    · exact prime_14737
    · exact prime_117529
  · decide +kernel

theorem prime_8133588804919 : Nat.Prime 8133588804919 := by
  apply nodeValid_prime [2, 3, 23, 82567, 713833] ⟨8133588804919, 3, [(2, 1), (3, 1), (23, 1), (82567, 1), (713833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_82567
    · exact prime_713833
  · decide +kernel

theorem prime_8138979193769 : Nat.Prime 8138979193769 := by
  apply nodeValid_prime [2, 31, 2551, 12864941] ⟨8138979193769, 3, [(2, 3), (31, 1), (2551, 1), (12864941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2551
    · exact prime_12864941
  · decide +kernel

theorem prime_8138979265481 : Nat.Prime 8138979265481 := by
  apply nodeValid_prime [2, 5, 7, 15073, 1928467] ⟨8138979265481, 6, [(2, 3), (5, 1), (7, 1), (15073, 1), (1928467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_15073
    · exact prime_1928467
  · decide +kernel

theorem prime_8138979266723 : Nat.Prime 8138979266723 := by
  apply nodeValid_prime [2, 4069489633361] ⟨8138979266723, 2, [(2, 1), (4069489633361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4069489633361
  · decide +kernel

theorem prime_8144372021287 : Nat.Prime 8144372021287 := by
  apply nodeValid_prime [2, 3, 31, 43786946351] ⟨8144372021287, 3, [(2, 1), (3, 1), (31, 1), (43786946351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43786946351
  · decide +kernel

theorem prime_8144372105917 : Nat.Prime 8144372105917 := by
  apply nodeValid_prime [2, 3, 31, 21893473403] ⟨8144372105917, 2, [(2, 2), (3, 1), (31, 1), (21893473403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_21893473403
  · decide +kernel

theorem prime_8144372106539 : Nat.Prime 8144372106539 := by
  apply nodeValid_prime [2, 19, 51973, 4123787] ⟨8144372106539, 2, [(2, 1), (19, 1), (51973, 1), (4123787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_51973
    · exact prime_4123787
  · decide +kernel

theorem prime_8149767264839 : Nat.Prime 8149767264839 := by
  apply nodeValid_prime [2, 19, 673, 318673937] ⟨8149767264839, 7, [(2, 1), (19, 1), (673, 1), (318673937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_673
    · exact prime_318673937
  · decide +kernel

theorem prime_8149767288917 : Nat.Prime 8149767288917 := by
  apply nodeValid_prime [2, 11, 185221983839] ⟨8149767288917, 2, [(2, 2), (11, 1), (185221983839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_185221983839
  · decide +kernel

theorem prime_8149767289099 : Nat.Prime 8149767289099 := by
  apply nodeValid_prime [2, 3, 929, 1462103927] ⟨8149767289099, 3, [(2, 1), (3, 1), (929, 1), (1462103927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
    · exact prime_1462103927
  · decide +kernel

theorem prime_8155164923813 : Nat.Prime 8155164923813 := by
  apply nodeValid_prime [2, 31, 65767459063] ⟨8155164923813, 2, [(2, 2), (31, 1), (65767459063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_65767459063
  · decide +kernel

theorem prime_8155164933569 : Nat.Prime 8155164933569 := by
  apply nodeValid_prime [2, 23, 5540193569] ⟨8155164933569, 3, [(2, 6), (23, 1), (5540193569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_5540193569
  · decide +kernel

theorem prime_8155164935459 : Nat.Prime 8155164935459 := by
  apply nodeValid_prime [2, 97, 26839, 1566263] ⟨8155164935459, 2, [(2, 1), (97, 1), (26839, 1), (1566263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_26839
    · exact prime_1566263
  · decide +kernel

theorem prime_8160564955877 : Nat.Prime 8160564955877 := by
  apply nodeValid_prime [2, 283, 14543, 495701] ⟨8160564955877, 2, [(2, 2), (283, 1), (14543, 1), (495701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_14543
    · exact prime_495701
  · decide +kernel

theorem prime_8160564956309 : Nat.Prime 8160564956309 := by
  apply nodeValid_prime [2, 17, 120008308181] ⟨8160564956309, 2, [(2, 2), (17, 1), (120008308181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_120008308181
  · decide +kernel

theorem prime_8160565006457 : Nat.Prime 8160565006457 := by
  apply nodeValid_prime [2, 1020070625807] ⟨8160565006457, 3, [(2, 3), (1020070625807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1020070625807
  · decide +kernel

theorem prime_8165967501179 : Nat.Prime 8165967501179 := by
  apply nodeValid_prime [2, 101, 40425581689] ⟨8165967501179, 2, [(2, 1), (101, 1), (40425581689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_40425581689
  · decide +kernel

theorem prime_8165967501443 : Nat.Prime 8165967501443 := by
  apply nodeValid_prime [2, 59, 131, 10391, 50839] ⟨8165967501443, 2, [(2, 1), (59, 1), (131, 1), (10391, 1), (50839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_131
    · exact prime_10391
    · exact prime_50839
  · decide +kernel

theorem prime_8165967501733 : Nat.Prime 8165967501733 := by
  apply nodeValid_prime [2, 3, 204299, 3330889] ⟨8165967501733, 2, [(2, 2), (3, 1), (204299, 1), (3330889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_204299
    · exact prime_3330889
  · decide +kernel

theorem prime_8171372384389 : Nat.Prime 8171372384389 := by
  apply nodeValid_prime [2, 3, 43, 586518259] ⟨8171372384389, 2, [(2, 2), (3, 4), (43, 1), (586518259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_586518259
  · decide +kernel

theorem prime_8171372385019 : Nat.Prime 8171372385019 := by
  apply nodeValid_prime [2, 3, 453965132501] ⟨8171372385019, 2, [(2, 1), (3, 2), (453965132501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_453965132501
  · decide +kernel

theorem prime_8171372418901 : Nat.Prime 8171372418901 := by
  apply nodeValid_prime [2, 3, 5, 61, 446523083] ⟨8171372418901, 6, [(2, 2), (3, 1), (5, 2), (61, 1), (446523083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_446523083
  · decide +kernel

theorem prime_8176779763183 : Nat.Prime 8176779763183 := by
  apply nodeValid_prime [2, 3, 643, 706478293] ⟨8176779763183, 3, [(2, 1), (3, 2), (643, 1), (706478293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_643
    · exact prime_706478293
  · decide +kernel

theorem prime_8176779777293 : Nat.Prime 8176779777293 := by
  apply nodeValid_prime [2, 7, 57173, 5107793] ⟨8176779777293, 2, [(2, 2), (7, 1), (57173, 1), (5107793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_57173
    · exact prime_5107793
  · decide +kernel

theorem prime_8176779777973 : Nat.Prime 8176779777973 := by
  apply nodeValid_prime [2, 3, 13, 31, 5639, 299843] ⟨8176779777973, 2, [(2, 2), (3, 1), (13, 1), (31, 1), (5639, 1), (299843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_5639
    · exact prime_299843
  · decide +kernel

theorem prime_8182189412009 : Nat.Prime 8182189412009 := by
  apply nodeValid_prime [2, 491, 2083042111] ⟨8182189412009, 3, [(2, 3), (491, 1), (2083042111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_2083042111
  · decide +kernel

theorem prime_8182189412603 : Nat.Prime 8182189412603 := by
  apply nodeValid_prime [2, 73, 56042393237] ⟨8182189412603, 2, [(2, 1), (73, 1), (56042393237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_56042393237
  · decide +kernel

theorem prime_8182189525703 : Nat.Prime 8182189525703 := by
  apply nodeValid_prime [2, 239, 38839, 440731] ⟨8182189525703, 5, [(2, 1), (239, 1), (38839, 1), (440731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_38839
    · exact prime_440731
  · decide +kernel

theorem prime_8187601685117 : Nat.Prime 8187601685117 := by
  apply nodeValid_prime [2, 7, 41, 151, 983, 48049] ⟨8187601685117, 2, [(2, 2), (7, 1), (41, 1), (151, 1), (983, 1), (48049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_151
    · exact prime_983
    · exact prime_48049
  · decide +kernel

theorem prime_8187601686151 : Nat.Prime 8187601686151 := by
  apply nodeValid_prime [2, 3, 5, 54584011241] ⟨8187601686151, 3, [(2, 1), (3, 1), (5, 2), (54584011241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_54584011241
  · decide +kernel

theorem prime_8187601714793 : Nat.Prime 8187601714793 := by
  apply nodeValid_prime [2, 4273, 239515613] ⟨8187601714793, 3, [(2, 3), (4273, 1), (239515613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4273
    · exact prime_239515613
  · decide +kernel

end Sude.Lucas.Generated
