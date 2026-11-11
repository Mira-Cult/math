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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0105

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5113 : Nat.Prime 5113 := by
  apply nodeValid_prime [2, 3, 71] ⟨5113, 19, [(2, 3), (3, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_11159 : Nat.Prime 11159 := by
  apply nodeValid_prime [2, 7, 797] ⟨11159, 7, [(2, 1), (7, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_797
  · decide +kernel

theorem prime_11311 : Nat.Prime 11311 := by
  apply nodeValid_prime [2, 3, 5, 13, 29] ⟨11311, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_22343 : Nat.Prime 22343 := by
  apply nodeValid_prime [2, 11171] ⟨22343, 5, [(2, 1), (11171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11171
  · decide +kernel

theorem prime_24469 : Nat.Prime 24469 := by
  apply nodeValid_prime [2, 3, 2039] ⟨24469, 14, [(2, 2), (3, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2039
  · decide +kernel

theorem prime_25693 : Nat.Prime 25693 := by
  apply nodeValid_prime [2, 3, 2141] ⟨25693, 2, [(2, 2), (3, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2141
  · decide +kernel

theorem prime_25943 : Nat.Prime 25943 := by
  apply nodeValid_prime [2, 7, 17, 109] ⟨25943, 5, [(2, 1), (7, 1), (17, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_109
  · decide +kernel

theorem prime_26003 : Nat.Prime 26003 := by
  apply nodeValid_prime [2, 13001] ⟨26003, 2, [(2, 1), (13001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13001
  · decide +kernel

theorem prime_29017 : Nat.Prime 29017 := by
  apply nodeValid_prime [2, 3, 13, 31] ⟨29017, 5, [(2, 3), (3, 2), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_30631 : Nat.Prime 30631 := by
  apply nodeValid_prime [2, 3, 5, 1021] ⟨30631, 3, [(2, 1), (3, 1), (5, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1021
  · decide +kernel

theorem prime_30763 : Nat.Prime 30763 := by
  apply nodeValid_prime [2, 3, 1709] ⟨30763, 2, [(2, 1), (3, 2), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1709
  · decide +kernel

theorem prime_31247 : Nat.Prime 31247 := by
  apply nodeValid_prime [2, 17, 919] ⟨31247, 5, [(2, 1), (17, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_919
  · decide +kernel

theorem prime_31991 : Nat.Prime 31991 := by
  apply nodeValid_prime [2, 5, 7, 457] ⟨31991, 7, [(2, 1), (5, 1), (7, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_457
  · decide +kernel

theorem prime_37871 : Nat.Prime 37871 := by
  apply nodeValid_prime [2, 5, 7, 541] ⟨37871, 7, [(2, 1), (5, 1), (7, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_541
  · decide +kernel

theorem prime_43411 : Nat.Prime 43411 := by
  apply nodeValid_prime [2, 3, 5, 1447] ⟨43411, 3, [(2, 1), (3, 1), (5, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1447
  · decide +kernel

theorem prime_44021 : Nat.Prime 44021 := by
  apply nodeValid_prime [2, 5, 31, 71] ⟨44021, 2, [(2, 2), (5, 1), (31, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_71
  · decide +kernel

theorem prime_44687 : Nat.Prime 44687 := by
  apply nodeValid_prime [2, 22343] ⟨44687, 5, [(2, 1), (22343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22343
  · decide +kernel

theorem prime_45569 : Nat.Prime 45569 := by
  apply nodeValid_prime [2, 89] ⟨45569, 3, [(2, 9), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_89
  · decide +kernel

theorem prime_60217 : Nat.Prime 60217 := by
  apply nodeValid_prime [2, 3, 13, 193] ⟨60217, 5, [(2, 3), (3, 1), (13, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_193
  · decide +kernel

theorem prime_71081 : Nat.Prime 71081 := by
  apply nodeValid_prime [2, 5, 1777] ⟨71081, 3, [(2, 3), (5, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1777
  · decide +kernel

theorem prime_81239 : Nat.Prime 81239 := by
  apply nodeValid_prime [2, 151, 269] ⟨81239, 7, [(2, 1), (151, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_269
  · decide +kernel

theorem prime_84239 : Nat.Prime 84239 := by
  apply nodeValid_prime [2, 7, 11, 547] ⟨84239, 11, [(2, 1), (7, 1), (11, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_547
  · decide +kernel

theorem prime_98213 : Nat.Prime 98213 := by
  apply nodeValid_prime [2, 43, 571] ⟨98213, 2, [(2, 2), (43, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_571
  · decide +kernel

theorem prime_109331 : Nat.Prime 109331 := by
  apply nodeValid_prime [2, 5, 13, 29] ⟨109331, 2, [(2, 1), (5, 1), (13, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_114781 : Nat.Prime 114781 := by
  apply nodeValid_prime [2, 3, 5, 1913] ⟨114781, 6, [(2, 2), (3, 1), (5, 1), (1913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1913
  · decide +kernel

theorem prime_136261 : Nat.Prime 136261 := by
  apply nodeValid_prime [2, 3, 5, 757] ⟨136261, 2, [(2, 2), (3, 2), (5, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_757
  · decide +kernel

theorem prime_156041 : Nat.Prime 156041 := by
  apply nodeValid_prime [2, 5, 47, 83] ⟨156041, 6, [(2, 3), (5, 1), (47, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_83
  · decide +kernel

theorem prime_167429 : Nat.Prime 167429 := by
  apply nodeValid_prime [2, 19, 2203] ⟨167429, 2, [(2, 2), (19, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2203
  · decide +kernel

theorem prime_172433 : Nat.Prime 172433 := by
  apply nodeValid_prime [2, 13, 829] ⟨172433, 3, [(2, 4), (13, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_829
  · decide +kernel

theorem prime_191551 : Nat.Prime 191551 := by
  apply nodeValid_prime [2, 3, 5, 1277] ⟨191551, 3, [(2, 1), (3, 1), (5, 2), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1277
  · decide +kernel

theorem prime_202063 : Nat.Prime 202063 := by
  apply nodeValid_prime [2, 3, 7, 17, 283] ⟨202063, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_283
  · decide +kernel

theorem prime_209333 : Nat.Prime 209333 := by
  apply nodeValid_prime [2, 59, 887] ⟨209333, 2, [(2, 2), (59, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_887
  · decide +kernel

theorem prime_246203 : Nat.Prime 246203 := by
  apply nodeValid_prime [2, 11, 19, 31] ⟨246203, 2, [(2, 1), (11, 1), (19, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_253063 : Nat.Prime 253063 := by
  apply nodeValid_prime [2, 3, 17, 827] ⟨253063, 3, [(2, 1), (3, 2), (17, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_827
  · decide +kernel

theorem prime_256337 : Nat.Prime 256337 := by
  apply nodeValid_prime [2, 37, 433] ⟨256337, 3, [(2, 4), (37, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_433
  · decide +kernel

theorem prime_273569 : Nat.Prime 273569 := by
  apply nodeValid_prime [2, 83, 103] ⟨273569, 3, [(2, 5), (83, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_103
  · decide +kernel

theorem prime_280759 : Nat.Prime 280759 := by
  apply nodeValid_prime [2, 3, 73, 641] ⟨280759, 3, [(2, 1), (3, 1), (73, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_641
  · decide +kernel

theorem prime_302969 : Nat.Prime 302969 := by
  apply nodeValid_prime [2, 37871] ⟨302969, 3, [(2, 3), (37871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37871
  · decide +kernel

theorem prime_312517 : Nat.Prime 312517 := by
  apply nodeValid_prime [2, 3, 8681] ⟨312517, 5, [(2, 2), (3, 2), (8681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8681
  · decide +kernel

theorem prime_312989 : Nat.Prime 312989 := by
  apply nodeValid_prime [2, 13, 463] ⟨312989, 2, [(2, 2), (13, 2), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_463
  · decide +kernel

theorem prime_376231 : Nat.Prime 376231 := by
  apply nodeValid_prime [2, 3, 5, 12541] ⟨376231, 3, [(2, 1), (3, 1), (5, 1), (12541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12541
  · decide +kernel

theorem prime_391151 : Nat.Prime 391151 := by
  apply nodeValid_prime [2, 5, 7823] ⟨391151, 13, [(2, 1), (5, 2), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7823
  · decide +kernel

theorem prime_418667 : Nat.Prime 418667 := by
  apply nodeValid_prime [2, 209333] ⟨418667, 2, [(2, 1), (209333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_209333
  · decide +kernel

theorem prime_427997 : Nat.Prime 427997 := by
  apply nodeValid_prime [2, 67, 1597] ⟨427997, 2, [(2, 2), (67, 1), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_1597
  · decide +kernel

theorem prime_436291 : Nat.Prime 436291 := by
  apply nodeValid_prime [2, 3, 5, 14543] ⟨436291, 2, [(2, 1), (3, 1), (5, 1), (14543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14543
  · decide +kernel

theorem prime_442009 : Nat.Prime 442009 := by
  apply nodeValid_prime [2, 3, 7, 877] ⟨442009, 19, [(2, 3), (3, 2), (7, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_877
  · decide +kernel

theorem prime_503857 : Nat.Prime 503857 := by
  apply nodeValid_prime [2, 3, 3499] ⟨503857, 17, [(2, 4), (3, 2), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3499
  · decide +kernel

theorem prime_547139 : Nat.Prime 547139 := by
  apply nodeValid_prime [2, 273569] ⟨547139, 2, [(2, 1), (273569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_273569
  · decide +kernel

theorem prime_590437 : Nat.Prime 590437 := by
  apply nodeValid_prime [2, 3, 7, 11, 71] ⟨590437, 6, [(2, 2), (3, 3), (7, 1), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_788351 : Nat.Prime 788351 := by
  apply nodeValid_prime [2, 5, 15767] ⟨788351, 7, [(2, 1), (5, 2), (15767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15767
  · decide +kernel

theorem prime_891643 : Nat.Prime 891643 := by
  apply nodeValid_prime [2, 3, 173, 859] ⟨891643, 2, [(2, 1), (3, 1), (173, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_859
  · decide +kernel

theorem prime_1043369 : Nat.Prime 1043369 := by
  apply nodeValid_prime [2, 41, 3181] ⟨1043369, 3, [(2, 3), (41, 1), (3181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_3181
  · decide +kernel

theorem prime_1091509 : Nat.Prime 1091509 := by
  apply nodeValid_prime [2, 3, 11, 8269] ⟨1091509, 6, [(2, 2), (3, 1), (11, 1), (8269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_8269
  · decide +kernel

theorem prime_1110103 : Nat.Prime 1110103 := by
  apply nodeValid_prime [2, 3, 7, 26431] ⟨1110103, 3, [(2, 1), (3, 1), (7, 1), (26431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_26431
  · decide +kernel

theorem prime_1132321 : Nat.Prime 1132321 := by
  apply nodeValid_prime [2, 3, 5, 7, 337] ⟨1132321, 13, [(2, 5), (3, 1), (5, 1), (7, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_337
  · decide +kernel

theorem prime_1151879 : Nat.Prime 1151879 := by
  apply nodeValid_prime [2, 7, 13, 6329] ⟨1151879, 7, [(2, 1), (7, 1), (13, 1), (6329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_6329
  · decide +kernel

theorem prime_1391641 : Nat.Prime 1391641 := by
  apply nodeValid_prime [2, 3, 5, 11597] ⟨1391641, 14, [(2, 3), (3, 1), (5, 1), (11597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11597
  · decide +kernel

theorem prime_1409027 : Nat.Prime 1409027 := by
  apply nodeValid_prime [2, 23, 30631] ⟨1409027, 2, [(2, 1), (23, 1), (30631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_30631
  · decide +kernel

theorem prime_1422011 : Nat.Prime 1422011 := by
  apply nodeValid_prime [2, 5, 43, 3307] ⟨1422011, 2, [(2, 1), (5, 1), (43, 1), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_3307
  · decide +kernel

theorem prime_1439833 : Nat.Prime 1439833 := by
  apply nodeValid_prime [2, 3, 17, 3529] ⟨1439833, 5, [(2, 3), (3, 1), (17, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3529
  · decide +kernel

theorem prime_1576703 : Nat.Prime 1576703 := by
  apply nodeValid_prime [2, 788351] ⟨1576703, 5, [(2, 1), (788351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_788351
  · decide +kernel

theorem prime_1656101 : Nat.Prime 1656101 := by
  apply nodeValid_prime [2, 5, 16561] ⟨1656101, 2, [(2, 2), (5, 2), (16561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16561
  · decide +kernel

theorem prime_1820407 : Nat.Prime 1820407 := by
  apply nodeValid_prime [2, 3, 7, 89, 487] ⟨1820407, 3, [(2, 1), (3, 1), (7, 1), (89, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_487
  · decide +kernel

theorem prime_1848107 : Nat.Prime 1848107 := by
  apply nodeValid_prime [2, 13, 71081] ⟨1848107, 2, [(2, 1), (13, 1), (71081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71081
  · decide +kernel

theorem prime_1900861 : Nat.Prime 1900861 := by
  apply nodeValid_prime [2, 3, 5, 13, 2437] ⟨1900861, 11, [(2, 2), (3, 1), (5, 1), (13, 1), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_2437
  · decide +kernel

theorem prime_2086739 : Nat.Prime 2086739 := by
  apply nodeValid_prime [2, 1043369] ⟨2086739, 2, [(2, 1), (1043369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1043369
  · decide +kernel

theorem prime_2201051 : Nat.Prime 2201051 := by
  apply nodeValid_prime [2, 5, 44021] ⟨2201051, 6, [(2, 1), (5, 2), (44021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_44021
  · decide +kernel

theorem prime_2480053 : Nat.Prime 2480053 := by
  apply nodeValid_prime [2, 3, 233, 887] ⟨2480053, 2, [(2, 2), (3, 1), (233, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_887
  · decide +kernel

theorem prime_2717821 : Nat.Prime 2717821 := by
  apply nodeValid_prime [2, 3, 5, 7, 719] ⟨2717821, 10, [(2, 2), (3, 3), (5, 1), (7, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_719
  · decide +kernel

theorem prime_3153407 : Nat.Prime 3153407 := by
  apply nodeValid_prime [2, 1576703] ⟨3153407, 5, [(2, 1), (1576703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1576703
  · decide +kernel

theorem prime_3474599 : Nat.Prime 3474599 := by
  apply nodeValid_prime [2, 71, 24469] ⟨3474599, 7, [(2, 1), (71, 1), (24469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_24469
  · decide +kernel

theorem prime_3977717 : Nat.Prime 3977717 := by
  apply nodeValid_prime [2, 317, 3137] ⟨3977717, 2, [(2, 2), (317, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_3137
  · decide +kernel

theorem prime_4173479 : Nat.Prime 4173479 := by
  apply nodeValid_prime [2, 2086739] ⟨4173479, 7, [(2, 1), (2086739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2086739
  · decide +kernel

theorem prime_4591903 : Nat.Prime 4591903 := by
  apply nodeValid_prime [2, 3, 7, 109331] ⟨4591903, 6, [(2, 1), (3, 1), (7, 1), (109331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109331
  · decide +kernel

theorem prime_4707733 : Nat.Prime 4707733 := by
  apply nodeValid_prime [2, 3, 23, 37, 461] ⟨4707733, 2, [(2, 2), (3, 1), (23, 1), (37, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
    · exact prime_461
  · decide +kernel

theorem prime_5104373 : Nat.Prime 5104373 := by
  apply nodeValid_prime [2, 7, 13, 37, 379] ⟨5104373, 2, [(2, 2), (7, 1), (13, 1), (37, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_379
  · decide +kernel

theorem prime_5446541 : Nat.Prime 5446541 := by
  apply nodeValid_prime [2, 5, 11, 19, 1303] ⟨5446541, 3, [(2, 2), (5, 1), (11, 1), (19, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_1303
  · decide +kernel

theorem prime_5568257 : Nat.Prime 5568257 := by
  apply nodeValid_prime [2, 21751] ⟨5568257, 3, [(2, 8), (21751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21751
  · decide +kernel

theorem prime_6325691 : Nat.Prime 6325691 := by
  apply nodeValid_prime [2, 5, 7, 23, 3929] ⟨6325691, 2, [(2, 1), (5, 1), (7, 1), (23, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_3929
  · decide +kernel

theorem prime_6846379 : Nat.Prime 6846379 := by
  apply nodeValid_prime [2, 3, 7, 11, 29, 73] ⟨6846379, 10, [(2, 1), (3, 1), (7, 2), (11, 1), (29, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_73
  · decide +kernel

theorem prime_7317253 : Nat.Prime 7317253 := by
  apply nodeValid_prime [2, 3, 439, 463] ⟨7317253, 6, [(2, 2), (3, 2), (439, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_439
    · exact prime_463
  · decide +kernel

theorem prime_8280277 : Nat.Prime 8280277 := by
  apply nodeValid_prime [2, 3, 19, 23, 1579] ⟨8280277, 5, [(2, 2), (3, 1), (19, 1), (23, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_1579
  · decide +kernel

theorem prime_8662471 : Nat.Prime 8662471 := by
  apply nodeValid_prime [2, 3, 5, 199, 1451] ⟨8662471, 11, [(2, 1), (3, 1), (5, 1), (199, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_1451
  · decide +kernel

theorem prime_9077891 : Nat.Prime 9077891 := by
  apply nodeValid_prime [2, 5, 79, 11491] ⟨9077891, 6, [(2, 1), (5, 1), (79, 1), (11491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_11491
  · decide +kernel

theorem prime_10893083 : Nat.Prime 10893083 := by
  apply nodeValid_prime [2, 5446541] ⟨10893083, 2, [(2, 1), (5446541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5446541
  · decide +kernel

theorem prime_11405167 : Nat.Prime 11405167 := by
  apply nodeValid_prime [2, 3, 1900861] ⟨11405167, 3, [(2, 1), (3, 1), (1900861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1900861
  · decide +kernel

theorem prime_14902343 : Nat.Prime 14902343 := by
  apply nodeValid_prime [2, 7, 13, 37, 2213] ⟨14902343, 7, [(2, 1), (7, 1), (13, 1), (37, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_2213
  · decide +kernel

theorem prime_24185137 : Nat.Prime 24185137 := by
  apply nodeValid_prime [2, 3, 503857] ⟨24185137, 5, [(2, 4), (3, 1), (503857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503857
  · decide +kernel

theorem prime_25130377 : Nat.Prime 25130377 := by
  apply nodeValid_prime [2, 3, 41, 8513] ⟨25130377, 5, [(2, 3), (3, 2), (41, 1), (8513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_8513
  · decide +kernel

theorem prime_25915817 : Nat.Prime 25915817 := by
  apply nodeValid_prime [2, 479, 6763] ⟨25915817, 3, [(2, 3), (479, 1), (6763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_6763
  · decide +kernel

theorem prime_27178211 : Nat.Prime 27178211 := by
  apply nodeValid_prime [2, 5, 2717821] ⟨27178211, 2, [(2, 1), (5, 1), (2717821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2717821
  · decide +kernel

theorem prime_46365437 : Nat.Prime 46365437 := by
  apply nodeValid_prime [2, 13, 891643] ⟨46365437, 2, [(2, 2), (13, 1), (891643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_891643
  · decide +kernel

theorem prime_84250937 : Nat.Prime 84250937 := by
  apply nodeValid_prime [2, 7, 11, 233, 587] ⟨84250937, 3, [(2, 3), (7, 1), (11, 1), (233, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_233
    · exact prime_587
  · decide +kernel

theorem prime_93302351 : Nat.Prime 93302351 := by
  apply nodeValid_prime [2, 5, 19, 98213] ⟨93302351, 7, [(2, 1), (5, 2), (19, 1), (98213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_98213
  · decide +kernel

theorem prime_147201731 : Nat.Prime 147201731 := by
  apply nodeValid_prime [2, 5, 13, 1132321] ⟨147201731, 2, [(2, 1), (5, 1), (13, 1), (1132321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1132321
  · decide +kernel

theorem prime_150782263 : Nat.Prime 150782263 := by
  apply nodeValid_prime [2, 3, 25130377] ⟨150782263, 6, [(2, 1), (3, 1), (25130377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25130377
  · decide +kernel

theorem prime_175497229 : Nat.Prime 175497229 := by
  apply nodeValid_prime [2, 3, 277, 17599] ⟨175497229, 2, [(2, 2), (3, 2), (277, 1), (17599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_17599
  · decide +kernel

theorem prime_186604703 : Nat.Prime 186604703 := by
  apply nodeValid_prime [2, 93302351] ⟨186604703, 5, [(2, 1), (93302351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93302351
  · decide +kernel

theorem prime_208950983 : Nat.Prime 208950983 := by
  apply nodeValid_prime [2, 6689, 15619] ⟨208950983, 5, [(2, 1), (6689, 1), (15619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6689
    · exact prime_15619
  · decide +kernel

theorem prime_214431677 : Nat.Prime 214431677 := by
  apply nodeValid_prime [2, 17, 3153407] ⟨214431677, 2, [(2, 2), (17, 1), (3153407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3153407
  · decide +kernel

theorem prime_214848793 : Nat.Prime 214848793 := by
  apply nodeValid_prime [2, 3, 97, 30763] ⟨214848793, 7, [(2, 3), (3, 2), (97, 1), (30763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_30763
  · decide +kernel

theorem prime_226608803 : Nat.Prime 226608803 := by
  apply nodeValid_prime [2, 7, 569, 28447] ⟨226608803, 2, [(2, 1), (7, 1), (569, 1), (28447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_569
    · exact prime_28447
  · decide +kernel

theorem prime_293881793 : Nat.Prime 293881793 := by
  apply nodeValid_prime [2, 4591903] ⟨293881793, 3, [(2, 6), (4591903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4591903
  · decide +kernel

theorem prime_357764123 : Nat.Prime 357764123 := by
  apply nodeValid_prime [2, 4003, 44687] ⟨357764123, 2, [(2, 1), (4003, 1), (44687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4003
    · exact prime_44687
  · decide +kernel

theorem prime_454987229 : Nat.Prime 454987229 := by
  apply nodeValid_prime [2, 79, 1439833] ⟨454987229, 2, [(2, 2), (79, 1), (1439833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1439833
  · decide +kernel

theorem prime_534552673 : Nat.Prime 534552673 := by
  apply nodeValid_prime [2, 3, 5568257] ⟨534552673, 5, [(2, 5), (3, 1), (5568257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5568257
  · decide +kernel

theorem prime_1624386811 : Nat.Prime 1624386811 := by
  apply nodeValid_prime [2, 3, 5, 347, 156041] ⟨1624386811, 3, [(2, 1), (3, 1), (5, 1), (347, 1), (156041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_347
    · exact prime_156041
  · decide +kernel

theorem prime_1993240169 : Nat.Prime 1993240169 := by
  apply nodeValid_prime [2, 23, 2927, 3701] ⟨1993240169, 3, [(2, 3), (23, 1), (2927, 1), (3701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2927
    · exact prime_3701
  · decide +kernel

theorem prime_3031986637 : Nat.Prime 3031986637 := by
  apply nodeValid_prime [2, 3, 7, 19, 59, 10733] ⟨3031986637, 2, [(2, 2), (3, 2), (7, 1), (19, 1), (59, 1), (10733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_59
    · exact prime_10733
  · decide +kernel

theorem prime_3818436539 : Nat.Prime 3818436539 := by
  apply nodeValid_prime [2, 7, 17, 617, 26003] ⟨3818436539, 2, [(2, 1), (7, 1), (17, 1), (617, 1), (26003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_617
    · exact prime_26003
  · decide +kernel

theorem prime_3929075483 : Nat.Prime 3929075483 := by
  apply nodeValid_prime [2, 1063, 1848107] ⟨3929075483, 2, [(2, 1), (1063, 1), (1848107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1063
    · exact prime_1848107
  · decide +kernel

theorem prime_3986480339 : Nat.Prime 3986480339 := by
  apply nodeValid_prime [2, 1993240169] ⟨3986480339, 2, [(2, 1), (1993240169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1993240169
  · decide +kernel

theorem prime_6250988531 : Nat.Prime 6250988531 := by
  apply nodeValid_prime [2, 5, 23, 27178211] ⟨6250988531, 2, [(2, 1), (5, 1), (23, 1), (27178211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_27178211
  · decide +kernel

theorem prime_6846873721 : Nat.Prime 6846873721 := by
  apply nodeValid_prime [2, 3, 5, 41, 1391641] ⟨6846873721, 11, [(2, 3), (3, 1), (5, 1), (41, 1), (1391641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_1391641
  · decide +kernel

theorem prime_7971376139 : Nat.Prime 7971376139 := by
  apply nodeValid_prime [2, 11, 12487, 29017] ⟨7971376139, 2, [(2, 1), (11, 1), (12487, 1), (29017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12487
    · exact prime_29017
  · decide +kernel

theorem prime_46064243893 : Nat.Prime 46064243893 := by
  apply nodeValid_prime [2, 3, 45569, 84239] ⟨46064243893, 2, [(2, 2), (3, 1), (45569, 1), (84239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45569
    · exact prime_84239
  · decide +kernel

theorem prime_53458111547 : Nat.Prime 53458111547 := by
  apply nodeValid_prime [2, 7, 3818436539] ⟨53458111547, 2, [(2, 1), (7, 1), (3818436539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3818436539
  · decide +kernel

theorem prime_64064989097 : Nat.Prime 64064989097 := by
  apply nodeValid_prime [2, 181, 331, 349, 383] ⟨64064989097, 3, [(2, 3), (181, 1), (331, 1), (349, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_331
    · exact prime_349
    · exact prime_383
  · decide +kernel

theorem prime_138420515881 : Nat.Prime 138420515881 := by
  apply nodeValid_prime [2, 3, 5, 983, 391151] ⟨138420515881, 11, [(2, 3), (3, 2), (5, 1), (983, 1), (391151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_983
    · exact prime_391151
  · decide +kernel

theorem prime_1047584127613 : Nat.Prime 1047584127613 := by
  apply nodeValid_prime [2, 3, 11, 5581, 1422011] ⟨1047584127613, 6, [(2, 2), (3, 1), (11, 1), (5581, 1), (1422011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5581
    · exact prime_1422011
  · decide +kernel

theorem prime_2091730454633 : Nat.Prime 2091730454633 := by
  apply nodeValid_prime [2, 7, 13, 347, 8280277] ⟨2091730454633, 3, [(2, 3), (7, 1), (13, 1), (347, 1), (8280277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_347
    · exact prime_8280277
  · decide +kernel

theorem prime_4145781941071 : Nat.Prime 4145781941071 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 19, 331, 25943] ⟨4145781941071, 12, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 2), (19, 1), (331, 1), (25943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_331
    · exact prime_25943
  · decide +kernel

theorem prime_4145781941827 : Nat.Prime 4145781941827 := by
  apply nodeValid_prime [2, 3, 7, 29, 83, 109, 376231] ⟨4145781941827, 2, [(2, 1), (3, 1), (7, 1), (29, 1), (83, 1), (109, 1), (376231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_83
    · exact prime_109
    · exact prime_376231
  · decide +kernel

theorem prime_4145781950371 : Nat.Prime 4145781950371 := by
  apply nodeValid_prime [2, 3, 5, 46064243893] ⟨4145781950371, 15, [(2, 1), (3, 2), (5, 1), (46064243893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46064243893
  · decide +kernel

theorem prime_4149197762603 : Nat.Prime 4149197762603 := by
  apply nodeValid_prime [2, 97, 293, 7691, 9491] ⟨4149197762603, 2, [(2, 1), (97, 1), (293, 1), (7691, 1), (9491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_293
    · exact prime_7691
    · exact prime_9491
  · decide +kernel

theorem prime_4149197846249 : Nat.Prime 4149197846249 := by
  apply nodeValid_prime [2, 7, 13, 17, 53, 6325691] ⟨4149197846249, 3, [(2, 3), (7, 1), (13, 1), (17, 1), (53, 1), (6325691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_53
    · exact prime_6325691
  · decide +kernel

theorem prime_4149197847827 : Nat.Prime 4149197847827 := by
  apply nodeValid_prime [2, 3881, 534552673] ⟨4149197847827, 2, [(2, 1), (3881, 1), (534552673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3881
    · exact prime_534552673
  · decide +kernel

theorem prime_4152615428249 : Nat.Prime 4152615428249 := by
  apply nodeValid_prime [2, 7, 41, 1657, 1091509] ⟨4152615428249, 3, [(2, 3), (7, 1), (41, 1), (1657, 1), (1091509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_1657
    · exact prime_1091509
  · decide +kernel

theorem prime_4152615432599 : Nat.Prime 4152615432599 := by
  apply nodeValid_prime [2, 11831, 175497229] ⟨4152615432599, 7, [(2, 1), (11831, 1), (175497229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11831
    · exact prime_175497229
  · decide +kernel

theorem prime_4152615476431 : Nat.Prime 4152615476431 := by
  apply nodeValid_prime [2, 3, 5, 138420515881] ⟨4152615476431, 6, [(2, 1), (3, 1), (5, 1), (138420515881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_138420515881
  · decide +kernel

theorem prime_4156035051793 : Nat.Prime 4156035051793 := by
  apply nodeValid_prime [2, 3, 13, 31, 214848793] ⟨4156035051793, 10, [(2, 4), (3, 1), (13, 1), (31, 1), (214848793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_214848793
  · decide +kernel

theorem prime_4156035051871 : Nat.Prime 4156035051871 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 208950983] ⟨4156035051871, 21, [(2, 1), (3, 2), (5, 1), (13, 1), (17, 1), (208950983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_208950983
  · decide +kernel

theorem prime_4156035107447 : Nat.Prime 4156035107447 := by
  apply nodeValid_prime [2, 67, 601, 857, 60217] ⟨4156035107447, 5, [(2, 1), (67, 1), (601, 1), (857, 1), (60217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_601
    · exact prime_857
    · exact prime_60217
  · decide +kernel

theorem prime_4159456601809 : Nat.Prime 4159456601809 := by
  apply nodeValid_prime [2, 3, 3583, 24185137] ⟨4159456601809, 31, [(2, 4), (3, 1), (3583, 1), (24185137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3583
    · exact prime_24185137
  · decide +kernel

theorem prime_4159456601921 : Nat.Prime 4159456601921 := by
  apply nodeValid_prime [2, 5, 17, 167, 773, 5923] ⟨4159456601921, 3, [(2, 6), (5, 1), (17, 1), (167, 1), (773, 1), (5923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_167
    · exact prime_773
    · exact prime_5923
  · decide +kernel

theorem prime_4159456647197 : Nat.Prime 4159456647197 := by
  apply nodeValid_prime [2, 293, 2143, 1656101] ⟨4159456647197, 2, [(2, 2), (293, 1), (2143, 1), (1656101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_2143
    · exact prime_1656101
  · decide +kernel

theorem prime_4162880093773 : Nat.Prime 4162880093773 := by
  apply nodeValid_prime [2, 3, 246203, 1409027] ⟨4162880093773, 6, [(2, 2), (3, 1), (246203, 1), (1409027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_246203
    · exact prime_1409027
  · decide +kernel

theorem prime_4162880102993 : Nat.Prime 4162880102993 := by
  apply nodeValid_prime [2, 13, 17, 79, 14902343] ⟨4162880102993, 3, [(2, 4), (13, 1), (17, 1), (79, 1), (14902343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_79
    · exact prime_14902343
  · decide +kernel

theorem prime_4162880103197 : Nat.Prime 4162880103197 := by
  apply nodeValid_prime [2, 17, 202063, 302969] ⟨4162880103197, 2, [(2, 2), (17, 1), (202063, 1), (302969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_202063
    · exact prime_302969
  · decide +kernel

theorem prime_4166305437947 : Nat.Prime 4166305437947 := by
  apply nodeValid_prime [2, 179, 251, 46365437] ⟨4166305437947, 2, [(2, 1), (179, 1), (251, 1), (46365437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_251
    · exact prime_46365437
  · decide +kernel

theorem prime_4166305438121 : Nat.Prime 4166305438121 := by
  apply nodeValid_prime [2, 5, 7, 739, 3643, 5527] ⟨4166305438121, 3, [(2, 3), (5, 1), (7, 1), (739, 1), (3643, 1), (5527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_739
    · exact prime_3643
    · exact prime_5527
  · decide +kernel

theorem prime_4166305454041 : Nat.Prime 4166305454041 := by
  apply nodeValid_prime [2, 3, 5, 227, 887, 172433] ⟨4166305454041, 7, [(2, 3), (3, 1), (5, 1), (227, 1), (887, 1), (172433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_227
    · exact prime_887
    · exact prime_172433
  · decide +kernel

theorem prime_4169732700667 : Nat.Prime 4169732700667 := by
  apply nodeValid_prime [2, 3, 13, 53458111547] ⟨4169732700667, 3, [(2, 1), (3, 1), (13, 1), (53458111547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53458111547
  · decide +kernel

theorem prime_4169732701003 : Nat.Prime 4169732701003 := by
  apply nodeValid_prime [2, 3, 11, 419, 150782263] ⟨4169732701003, 3, [(2, 1), (3, 1), (11, 1), (419, 1), (150782263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_419
    · exact prime_150782263
  · decide +kernel

theorem prime_4169732717797 : Nat.Prime 4169732717797 := by
  apply nodeValid_prime [2, 3, 167, 7411, 280759] ⟨4169732717797, 5, [(2, 2), (3, 1), (167, 1), (7411, 1), (280759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_7411
    · exact prime_280759
  · decide +kernel

theorem prime_4173161815597 : Nat.Prime 4173161815597 := by
  apply nodeValid_prime [2, 3, 103, 809, 4173479] ⟨4173161815597, 2, [(2, 2), (3, 1), (103, 1), (809, 1), (4173479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_809
    · exact prime_4173479
  · decide +kernel

theorem prime_4173161816119 : Nat.Prime 4173161816119 := by
  apply nodeValid_prime [2, 3, 136261, 5104373] ⟨4173161816119, 3, [(2, 1), (3, 1), (136261, 1), (5104373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_136261
    · exact prime_5104373
  · decide +kernel

theorem prime_4173161883467 : Nat.Prime 4173161883467 := by
  apply nodeValid_prime [2, 191551, 10893083] ⟨4173161883467, 2, [(2, 1), (191551, 1), (10893083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191551
    · exact prime_10893083
  · decide +kernel

theorem prime_4176592969811 : Nat.Prime 4176592969811 := by
  apply nodeValid_prime [2, 5, 61, 6846873721] ⟨4176592969811, 2, [(2, 1), (5, 1), (61, 1), (6846873721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_6846873721
  · decide +kernel

theorem prime_4176593067709 : Nat.Prime 4176593067709 := by
  apply nodeValid_prime [2, 3, 59, 227, 8662471] ⟨4176593067709, 6, [(2, 2), (3, 2), (59, 1), (227, 1), (8662471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_227
    · exact prime_8662471
  · decide +kernel

theorem prime_4176593067721 : Nat.Prime 4176593067721 := by
  apply nodeValid_prime [2, 3, 5, 17, 79, 25915817] ⟨4176593067721, 22, [(2, 3), (3, 1), (5, 1), (17, 1), (79, 1), (25915817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_79
    · exact prime_25915817
  · decide +kernel

theorem prime_4180025980139 : Nat.Prime 4180025980139 := by
  apply nodeValid_prime [2, 23, 401, 226608803] ⟨4180025980139, 2, [(2, 1), (23, 1), (401, 1), (226608803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_401
    · exact prime_226608803
  · decide +kernel

theorem prime_4180025987377 : Nat.Prime 4180025987377 := by
  apply nodeValid_prime [2, 3, 71, 353, 3474599] ⟨4180025987377, 10, [(2, 4), (3, 1), (71, 1), (353, 1), (3474599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_353
    · exact prime_3474599
  · decide +kernel

theorem prime_4180025988319 : Nat.Prime 4180025988319 := by
  apply nodeValid_prime [2, 3, 8269, 84250937] ⟨4180025988319, 6, [(2, 1), (3, 1), (8269, 1), (84250937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8269
    · exact prime_84250937
  · decide +kernel

theorem prime_4183460876269 : Nat.Prime 4183460876269 := by
  apply nodeValid_prime [2, 3, 23, 443, 11405167] ⟨4183460876269, 7, [(2, 2), (3, 2), (23, 1), (443, 1), (11405167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_443
    · exact prime_11405167
  · decide +kernel

theorem prime_4183460878027 : Nat.Prime 4183460878027 := by
  apply nodeValid_prime [2, 3, 509, 5413, 253063] ⟨4183460878027, 2, [(2, 1), (3, 1), (509, 1), (5413, 1), (253063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_509
    · exact prime_5413
    · exact prime_253063
  · decide +kernel

theorem prime_4183460909267 : Nat.Prime 4183460909267 := by
  apply nodeValid_prime [2, 2091730454633] ⟨4183460909267, 2, [(2, 1), (2091730454633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2091730454633
  · decide +kernel

theorem prime_4186897667279 : Nat.Prime 4186897667279 := by
  apply nodeValid_prime [2, 59, 7537, 4707733] ⟨4186897667279, 13, [(2, 1), (59, 1), (7537, 1), (4707733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_7537
    · exact prime_4707733
  · decide +kernel

theorem prime_4186897668197 : Nat.Prime 4186897668197 := by
  apply nodeValid_prime [2, 23, 181, 1297, 193859] ⟨4186897668197, 2, [(2, 2), (23, 1), (181, 1), (1297, 1), (193859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_181
    · exact prime_1297
    · exact prime_193859
  · decide +kernel

theorem prime_4186897754849 : Nat.Prime 4186897754849 := by
  apply nodeValid_prime [2, 312517, 418667] ⟨4186897754849, 3, [(2, 5), (312517, 1), (418667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_312517
    · exact prime_418667
  · decide +kernel

theorem prime_4190336329519 : Nat.Prime 4190336329519 := by
  apply nodeValid_prime [2, 3, 23, 2239, 167429] ⟨4190336329519, 3, [(2, 1), (3, 5), (23, 1), (2239, 1), (167429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2239
    · exact prime_167429
  · decide +kernel

theorem prime_4190336329819 : Nat.Prime 4190336329819 := by
  apply nodeValid_prime [2, 3, 107, 719, 9077891] ⟨4190336329819, 2, [(2, 1), (3, 1), (107, 1), (719, 1), (9077891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_719
    · exact prime_9077891
  · decide +kernel

theorem prime_4190336510453 : Nat.Prime 4190336510453 := by
  apply nodeValid_prime [2, 1047584127613] ⟨4190336510453, 2, [(2, 2), (1047584127613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1047584127613
  · decide +kernel

theorem prime_4193777189507 : Nat.Prime 4193777189507 := by
  apply nodeValid_prime [2, 1151879, 1820407] ⟨4193777189507, 2, [(2, 1), (1151879, 1), (1820407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1151879
    · exact prime_1820407
  · decide +kernel

theorem prime_4193777316191 : Nat.Prime 4193777316191 := by
  apply nodeValid_prime [2, 5, 7, 11, 37, 147201731] ⟨4193777316191, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (37, 1), (147201731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_37
    · exact prime_147201731
  · decide +kernel

theorem prime_4193777316629 : Nat.Prime 4193777316629 := by
  apply nodeValid_prime [2, 263, 3986480339] ⟨4193777316629, 2, [(2, 2), (263, 1), (3986480339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_3986480339
  · decide +kernel

theorem prime_4197219766931 : Nat.Prime 4197219766931 := by
  apply nodeValid_prime [2, 5, 31, 31033, 436291] ⟨4197219766931, 6, [(2, 1), (5, 1), (31, 1), (31033, 1), (436291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_31033
    · exact prime_436291
  · decide +kernel

theorem prime_4197219767627 : Nat.Prime 4197219767627 := by
  apply nodeValid_prime [2, 37, 193, 293881793] ⟨4197219767627, 2, [(2, 1), (37, 1), (193, 1), (293881793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_193
    · exact prime_293881793
  · decide +kernel

theorem prime_4197219792251 : Nat.Prime 4197219792251 := by
  apply nodeValid_prime [2, 5, 433, 4447, 8719] ⟨4197219792251, 2, [(2, 1), (5, 3), (433, 1), (4447, 1), (8719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_433
    · exact prime_4447
    · exact prime_8719
  · decide +kernel

theorem prime_4200664292833 : Nat.Prime 4200664292833 := by
  apply nodeValid_prime [2, 3, 7, 6250988531] ⟨4200664292833, 5, [(2, 5), (3, 1), (7, 1), (6250988531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6250988531
  · decide +kernel

theorem prime_4200664293247 : Nat.Prime 4200664293247 := by
  apply nodeValid_prime [2, 3, 431, 1624386811] ⟨4200664293247, 3, [(2, 1), (3, 1), (431, 1), (1624386811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
    · exact prime_1624386811
  · decide +kernel

theorem prime_4200664299241 : Nat.Prime 4200664299241 := by
  apply nodeValid_prime [2, 3, 5, 5113, 6846379] ⟨4200664299241, 13, [(2, 3), (3, 1), (5, 1), (5113, 1), (6846379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5113
    · exact prime_6846379
  · decide +kernel

theorem prime_4204110711893 : Nat.Prime 4204110711893 := by
  apply nodeValid_prime [2, 7, 13, 523, 1979, 11159] ⟨4204110711893, 2, [(2, 2), (7, 1), (13, 1), (523, 1), (1979, 1), (11159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_523
    · exact prime_1979
    · exact prime_11159
  · decide +kernel

theorem prime_4204110766811 : Nat.Prime 4204110766811 := by
  apply nodeValid_prime [2, 5, 107, 3929075483] ⟨4204110766811, 2, [(2, 1), (5, 1), (107, 1), (3929075483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_3929075483
  · decide +kernel

theorem prime_4207559035553 : Nat.Prime 4207559035553 := by
  apply nodeValid_prime [2, 61, 101, 683, 31247] ⟨4207559035553, 3, [(2, 5), (61, 1), (101, 1), (683, 1), (31247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_101
    · exact prime_683
    · exact prime_31247
  · decide +kernel

theorem prime_4207559095291 : Nat.Prime 4207559095291 := by
  apply nodeValid_prime [2, 3, 5, 256337, 547139] ⟨4207559095291, 3, [(2, 1), (3, 1), (5, 1), (256337, 1), (547139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_256337
    · exact prime_547139
  · decide +kernel

theorem prime_4207559096557 : Nat.Prime 4207559096557 := by
  apply nodeValid_prime [2, 3, 17, 101, 227, 2969] ⟨4207559096557, 2, [(2, 2), (3, 2), (17, 1), (101, 2), (227, 1), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_101
    · exact prime_227
    · exact prime_2969
  · decide +kernel

theorem prime_4211009215051 : Nat.Prime 4211009215051 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 1110103] ⟨4211009215051, 3, [(2, 1), (3, 1), (5, 2), (11, 3), (19, 1), (1110103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_1110103
  · decide +kernel

theorem prime_4211009218021 : Nat.Prime 4211009218021 := by
  apply nodeValid_prime [2, 3, 5, 11, 167, 1487, 25693] ⟨4211009218021, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (167, 1), (1487, 1), (25693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_167
    · exact prime_1487
    · exact prime_25693
  · decide +kernel

theorem prime_4211009272927 : Nat.Prime 4211009272927 := by
  apply nodeValid_prime [2, 3, 1091, 214431677] ⟨4211009272927, 5, [(2, 1), (3, 2), (1091, 1), (214431677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
    · exact prime_214431677
  · decide +kernel

theorem prime_4214461368317 : Nat.Prime 4214461368317 := by
  apply nodeValid_prime [2, 409, 4363, 590437] ⟨4214461368317, 2, [(2, 2), (409, 1), (4363, 1), (590437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_4363
    · exact prime_590437
  · decide +kernel

theorem prime_4214461368941 : Nat.Prime 4214461368941 := by
  apply nodeValid_prime [2, 5, 19, 31, 357764123] ⟨4214461368941, 2, [(2, 2), (5, 1), (19, 1), (31, 1), (357764123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_31
    · exact prime_357764123
  · decide +kernel

theorem prime_4214461425431 : Nat.Prime 4214461425431 := by
  apply nodeValid_prime [2, 5, 139, 3031986637] ⟨4214461425431, 11, [(2, 1), (5, 1), (139, 1), (3031986637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_3031986637
  · decide +kernel

theorem prime_4217915418763 : Nat.Prime 4217915418763 := by
  apply nodeValid_prime [2, 3, 31, 5701, 3977717] ⟨4217915418763, 2, [(2, 1), (3, 1), (31, 1), (5701, 1), (3977717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_5701
    · exact prime_3977717
  · decide +kernel

theorem prime_4217915419009 : Nat.Prime 4217915419009 := by
  apply nodeValid_prime [2, 3, 43, 103, 2480053] ⟨4217915419009, 7, [(2, 7), (3, 1), (43, 1), (103, 1), (2480053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_103
    · exact prime_2480053
  · decide +kernel

theorem prime_4217915507339 : Nat.Prime 4217915507339 := by
  apply nodeValid_prime [2, 13, 29, 61, 293, 312989] ⟨4217915507339, 2, [(2, 1), (13, 1), (29, 1), (61, 1), (293, 1), (312989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_61
    · exact prime_293
    · exact prime_312989
  · decide +kernel

theorem prime_4221371510663 : Nat.Prime 4221371510663 := by
  apply nodeValid_prime [2, 4639, 454987229] ⟨4221371510663, 5, [(2, 1), (4639, 1), (454987229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4639
    · exact prime_454987229
  · decide +kernel

theorem prime_4221371591267 : Nat.Prime 4221371591267 := by
  apply nodeValid_prime [2, 11311, 186604703] ⟨4221371591267, 2, [(2, 1), (11311, 1), (186604703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11311
    · exact prime_186604703
  · decide +kernel

theorem prime_4221371593781 : Nat.Prime 4221371593781 := by
  apply nodeValid_prime [2, 5, 11, 43411, 442009] ⟨4221371593781, 2, [(2, 2), (5, 1), (11, 1), (43411, 1), (442009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43411
    · exact prime_442009
  · decide +kernel

theorem prime_4224829352461 : Nat.Prime 4224829352461 := by
  apply nodeValid_prime [2, 3, 5, 31991, 2201051] ⟨4224829352461, 6, [(2, 2), (3, 1), (5, 1), (31991, 1), (2201051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31991
    · exact prime_2201051
  · decide +kernel

theorem prime_4224829353671 : Nat.Prime 4224829353671 := by
  apply nodeValid_prime [2, 5, 53, 7971376139] ⟨4224829353671, 11, [(2, 1), (5, 1), (53, 1), (7971376139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_7971376139
  · decide +kernel

theorem prime_4224829434503 : Nat.Prime 4224829434503 := by
  apply nodeValid_prime [2, 43, 114781, 427997] ⟨4224829434503, 5, [(2, 1), (43, 1), (114781, 1), (427997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_114781
    · exact prime_427997
  · decide +kernel

theorem prime_4228289280403 : Nat.Prime 4228289280403 := by
  apply nodeValid_prime [2, 3, 11, 64064989097] ⟨4228289280403, 5, [(2, 1), (3, 1), (11, 1), (64064989097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_64064989097
  · decide +kernel

theorem prime_4228289280557 : Nat.Prime 4228289280557 := by
  apply nodeValid_prime [2, 11, 23, 571, 7317253] ⟨4228289280557, 3, [(2, 2), (11, 1), (23, 1), (571, 1), (7317253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_571
    · exact prime_7317253
  · decide +kernel

theorem prime_4228289289671 : Nat.Prime 4228289289671 := by
  apply nodeValid_prime [2, 5, 37, 163, 863, 81239] ⟨4228289289671, 17, [(2, 1), (5, 1), (37, 1), (163, 1), (863, 1), (81239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_163
    · exact prime_863
    · exact prime_81239
  · decide +kernel

end Sude.Lucas.Generated
