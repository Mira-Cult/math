import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0088

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5879 : Nat.Prime 5879 := by
  apply nodeValid_prime [2, 2939] ⟨5879, 11, [(2, 1), (2939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2939
  · decide +kernel

theorem prime_9923 : Nat.Prime 9923 := by
  apply nodeValid_prime [2, 11, 41] ⟨9923, 2, [(2, 1), (11, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_11959 : Nat.Prime 11959 := by
  apply nodeValid_prime [2, 3, 1993] ⟨11959, 3, [(2, 1), (3, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1993
  · decide +kernel

theorem prime_12487 : Nat.Prime 12487 := by
  apply nodeValid_prime [2, 3, 2081] ⟨12487, 3, [(2, 1), (3, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2081
  · decide +kernel

theorem prime_13477 : Nat.Prime 13477 := by
  apply nodeValid_prime [2, 3, 1123] ⟨13477, 2, [(2, 2), (3, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1123
  · decide +kernel

theorem prime_15287 : Nat.Prime 15287 := by
  apply nodeValid_prime [2, 7643] ⟨15287, 5, [(2, 1), (7643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7643
  · decide +kernel

theorem prime_15791 : Nat.Prime 15791 := by
  apply nodeValid_prime [2, 5, 1579] ⟨15791, 29, [(2, 1), (5, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1579
  · decide +kernel

theorem prime_24971 : Nat.Prime 24971 := by
  apply nodeValid_prime [2, 5, 11, 227] ⟨24971, 2, [(2, 1), (5, 1), (11, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_227
  · decide +kernel

theorem prime_26597 : Nat.Prime 26597 := by
  apply nodeValid_prime [2, 61, 109] ⟨26597, 2, [(2, 2), (61, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_109
  · decide +kernel

theorem prime_36109 : Nat.Prime 36109 := by
  apply nodeValid_prime [2, 3, 17, 59] ⟨36109, 2, [(2, 2), (3, 2), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_42227 : Nat.Prime 42227 := by
  apply nodeValid_prime [2, 43, 491] ⟨42227, 2, [(2, 1), (43, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_491
  · decide +kernel

theorem prime_47563 : Nat.Prime 47563 := by
  apply nodeValid_prime [2, 3, 7927] ⟨47563, 2, [(2, 1), (3, 1), (7927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7927
  · decide +kernel

theorem prime_47837 : Nat.Prime 47837 := by
  apply nodeValid_prime [2, 11959] ⟨47837, 2, [(2, 2), (11959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11959
  · decide +kernel

theorem prime_49943 : Nat.Prime 49943 := by
  apply nodeValid_prime [2, 24971] ⟨49943, 5, [(2, 1), (24971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24971
  · decide +kernel

theorem prime_63667 : Nat.Prime 63667 := by
  apply nodeValid_prime [2, 3, 131] ⟨63667, 2, [(2, 1), (3, 5), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_73453 : Nat.Prime 73453 := by
  apply nodeValid_prime [2, 3, 6121] ⟨73453, 2, [(2, 2), (3, 1), (6121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6121
  · decide +kernel

theorem prime_76129 : Nat.Prime 76129 := by
  apply nodeValid_prime [2, 3, 13, 61] ⟨76129, 17, [(2, 5), (3, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_77101 : Nat.Prime 77101 := by
  apply nodeValid_prime [2, 3, 5, 257] ⟨77101, 7, [(2, 2), (3, 1), (5, 2), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
  · decide +kernel

theorem prime_83969 : Nat.Prime 83969 := by
  apply nodeValid_prime [2, 41] ⟨83969, 3, [(2, 11), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41
  · decide +kernel

theorem prime_106979 : Nat.Prime 106979 := by
  apply nodeValid_prime [2, 89, 601] ⟨106979, 2, [(2, 1), (89, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_601
  · decide +kernel

theorem prime_109469 : Nat.Prime 109469 := by
  apply nodeValid_prime [2, 27367] ⟨109469, 2, [(2, 2), (27367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27367
  · decide +kernel

theorem prime_115153 : Nat.Prime 115153 := by
  apply nodeValid_prime [2, 3, 2399] ⟨115153, 5, [(2, 4), (3, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2399
  · decide +kernel

theorem prime_115201 : Nat.Prime 115201 := by
  apply nodeValid_prime [2, 3, 5] ⟨115201, 23, [(2, 9), (3, 2), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_119159 : Nat.Prime 119159 := by
  apply nodeValid_prime [2, 13, 4583] ⟨119159, 17, [(2, 1), (13, 1), (4583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_4583
  · decide +kernel

theorem prime_129719 : Nat.Prime 129719 := by
  apply nodeValid_prime [2, 79, 821] ⟨129719, 7, [(2, 1), (79, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_821
  · decide +kernel

theorem prime_131023 : Nat.Prime 131023 := by
  apply nodeValid_prime [2, 3, 29, 251] ⟨131023, 6, [(2, 1), (3, 2), (29, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_251
  · decide +kernel

theorem prime_143257 : Nat.Prime 143257 := by
  apply nodeValid_prime [2, 3, 47, 127] ⟨143257, 5, [(2, 3), (3, 1), (47, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_127
  · decide +kernel

theorem prime_177239 : Nat.Prime 177239 := by
  apply nodeValid_prime [2, 23, 3853] ⟨177239, 17, [(2, 1), (23, 1), (3853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3853
  · decide +kernel

theorem prime_198461 : Nat.Prime 198461 := by
  apply nodeValid_prime [2, 5, 9923] ⟨198461, 2, [(2, 2), (5, 1), (9923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9923
  · decide +kernel

theorem prime_209647 : Nat.Prime 209647 := by
  apply nodeValid_prime [2, 3, 19, 613] ⟨209647, 3, [(2, 1), (3, 2), (19, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_613
  · decide +kernel

theorem prime_223403 : Nat.Prime 223403 := by
  apply nodeValid_prime [2, 19, 5879] ⟨223403, 2, [(2, 1), (19, 1), (5879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5879
  · decide +kernel

theorem prime_264959 : Nat.Prime 264959 := by
  apply nodeValid_prime [2, 137, 967] ⟨264959, 7, [(2, 1), (137, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_967
  · decide +kernel

theorem prime_279203 : Nat.Prime 279203 := by
  apply nodeValid_prime [2, 7, 11, 37] ⟨279203, 2, [(2, 1), (7, 3), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_285433 : Nat.Prime 285433 := by
  apply nodeValid_prime [2, 3, 7, 1699] ⟨285433, 5, [(2, 3), (3, 1), (7, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1699
  · decide +kernel

theorem prime_296363 : Nat.Prime 296363 := by
  apply nodeValid_prime [2, 11, 19, 709] ⟨296363, 5, [(2, 1), (11, 1), (19, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_709
  · decide +kernel

theorem prime_304517 : Nat.Prime 304517 := by
  apply nodeValid_prime [2, 76129] ⟨304517, 2, [(2, 2), (76129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76129
  · decide +kernel

theorem prime_335381 : Nat.Prime 335381 := by
  apply nodeValid_prime [2, 5, 41, 409] ⟨335381, 2, [(2, 2), (5, 1), (41, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_409
  · decide +kernel

theorem prime_469717 : Nat.Prime 469717 := by
  apply nodeValid_prime [2, 3, 13, 3011] ⟨469717, 2, [(2, 2), (3, 1), (13, 1), (3011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3011
  · decide +kernel

theorem prime_516493 : Nat.Prime 516493 := by
  apply nodeValid_prime [2, 3, 14347] ⟨516493, 2, [(2, 2), (3, 2), (14347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14347
  · decide +kernel

theorem prime_527209 : Nat.Prime 527209 := by
  apply nodeValid_prime [2, 3, 11, 1997] ⟨527209, 13, [(2, 3), (3, 1), (11, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1997
  · decide +kernel

theorem prime_557857 : Nat.Prime 557857 := by
  apply nodeValid_prime [2, 3, 13, 149] ⟨557857, 10, [(2, 5), (3, 2), (13, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_149
  · decide +kernel

theorem prime_653113 : Nat.Prime 653113 := by
  apply nodeValid_prime [2, 3, 47, 193] ⟨653113, 5, [(2, 3), (3, 2), (47, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_193
  · decide +kernel

theorem prime_953551 : Nat.Prime 953551 := by
  apply nodeValid_prime [2, 3, 5, 13, 163] ⟨953551, 3, [(2, 1), (3, 2), (5, 2), (13, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_163
  · decide +kernel

theorem prime_984199 : Nat.Prime 984199 := by
  apply nodeValid_prime [2, 3, 17, 9649] ⟨984199, 6, [(2, 1), (3, 1), (17, 1), (9649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9649
  · decide +kernel

theorem prime_1157449 : Nat.Prime 1157449 := by
  apply nodeValid_prime [2, 3, 29, 1663] ⟨1157449, 14, [(2, 3), (3, 1), (29, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1663
  · decide +kernel

theorem prime_1169929 : Nat.Prime 1169929 := by
  apply nodeValid_prime [2, 3, 16249] ⟨1169929, 7, [(2, 3), (3, 2), (16249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16249
  · decide +kernel

theorem prime_1313629 : Nat.Prime 1313629 := by
  apply nodeValid_prime [2, 3, 109469] ⟨1313629, 6, [(2, 2), (3, 1), (109469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109469
  · decide +kernel

theorem prime_1762627 : Nat.Prime 1762627 := by
  apply nodeValid_prime [2, 3, 263, 1117] ⟨1762627, 2, [(2, 1), (3, 1), (263, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_1117
  · decide +kernel

theorem prime_1772387 : Nat.Prime 1772387 := by
  apply nodeValid_prime [2, 7, 11, 17, 677] ⟨1772387, 2, [(2, 1), (7, 1), (11, 1), (17, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_677
  · decide +kernel

theorem prime_1989133 : Nat.Prime 1989133 := by
  apply nodeValid_prime [2, 3, 23, 7207] ⟨1989133, 2, [(2, 2), (3, 1), (23, 1), (7207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_7207
  · decide +kernel

theorem prime_3450431 : Nat.Prime 3450431 := by
  apply nodeValid_prime [2, 5, 389, 887] ⟨3450431, 29, [(2, 1), (5, 1), (389, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_389
    · exact prime_887
  · decide +kernel

theorem prime_3969151 : Nat.Prime 3969151 := by
  apply nodeValid_prime [2, 3, 5, 47, 563] ⟨3969151, 7, [(2, 1), (3, 1), (5, 2), (47, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_563
  · decide +kernel

theorem prime_4163741 : Nat.Prime 4163741 := by
  apply nodeValid_prime [2, 5, 7, 29741] ⟨4163741, 10, [(2, 2), (5, 1), (7, 1), (29741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29741
  · decide +kernel

theorem prime_4593377 : Nat.Prime 4593377 := by
  apply nodeValid_prime [2, 23, 79] ⟨4593377, 3, [(2, 5), (23, 1), (79, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_5537263 : Nat.Prime 5537263 := by
  apply nodeValid_prime [2, 3, 83, 11119] ⟨5537263, 6, [(2, 1), (3, 1), (83, 1), (11119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_11119
  · decide +kernel

theorem prime_5537897 : Nat.Prime 5537897 := by
  apply nodeValid_prime [2, 7, 13, 7607] ⟨5537897, 3, [(2, 3), (7, 1), (13, 1), (7607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_7607
  · decide +kernel

theorem prime_5688803 : Nat.Prime 5688803 := by
  apply nodeValid_prime [2, 7, 58049] ⟨5688803, 2, [(2, 1), (7, 2), (58049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_58049
  · decide +kernel

theorem prime_5919091 : Nat.Prime 5919091 := by
  apply nodeValid_prime [2, 3, 5, 191, 1033] ⟨5919091, 2, [(2, 1), (3, 1), (5, 1), (191, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
    · exact prime_1033
  · decide +kernel

theorem prime_6027059 : Nat.Prime 6027059 := by
  apply nodeValid_prime [2, 23, 131023] ⟨6027059, 2, [(2, 1), (23, 1), (131023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_131023
  · decide +kernel

theorem prime_6289411 : Nat.Prime 6289411 := by
  apply nodeValid_prime [2, 3, 5, 209647] ⟨6289411, 3, [(2, 1), (3, 1), (5, 1), (209647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_209647
  · decide +kernel

theorem prime_6475901 : Nat.Prime 6475901 := by
  apply nodeValid_prime [2, 5, 31, 2089] ⟨6475901, 3, [(2, 2), (5, 2), (31, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_2089
  · decide +kernel

theorem prime_8327483 : Nat.Prime 8327483 := by
  apply nodeValid_prime [2, 4163741] ⟨8327483, 2, [(2, 1), (4163741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4163741
  · decide +kernel

theorem prime_8873087 : Nat.Prime 8873087 := by
  apply nodeValid_prime [2, 1427, 3109] ⟨8873087, 5, [(2, 1), (1427, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1427
    · exact prime_3109
  · decide +kernel

theorem prime_9572081 : Nat.Prime 9572081 := by
  apply nodeValid_prime [2, 5, 7, 17093] ⟨9572081, 11, [(2, 4), (5, 1), (7, 1), (17093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17093
  · decide +kernel

theorem prime_9734503 : Nat.Prime 9734503 := by
  apply nodeValid_prime [2, 3, 61, 26597] ⟨9734503, 5, [(2, 1), (3, 1), (61, 1), (26597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_26597
  · decide +kernel

theorem prime_11546827 : Nat.Prime 11546827 := by
  apply nodeValid_prime [2, 3, 619, 3109] ⟨11546827, 3, [(2, 1), (3, 1), (619, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_619
    · exact prime_3109
  · decide +kernel

theorem prime_12952969 : Nat.Prime 12952969 := by
  apply nodeValid_prime [2, 3, 7, 77101] ⟨12952969, 11, [(2, 3), (3, 1), (7, 1), (77101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_77101
  · decide +kernel

theorem prime_13889389 : Nat.Prime 13889389 := by
  apply nodeValid_prime [2, 3, 1157449] ⟨13889389, 2, [(2, 2), (3, 1), (1157449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1157449
  · decide +kernel

theorem prime_14344543 : Nat.Prime 14344543 := by
  apply nodeValid_prime [2, 3, 43, 431] ⟨14344543, 3, [(2, 1), (3, 2), (43, 2), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_431
  · decide +kernel

theorem prime_15763549 : Nat.Prime 15763549 := by
  apply nodeValid_prime [2, 3, 1313629] ⟨15763549, 2, [(2, 2), (3, 1), (1313629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1313629
  · decide +kernel

theorem prime_19144163 : Nat.Prime 19144163 := by
  apply nodeValid_prime [2, 9572081] ⟨19144163, 2, [(2, 1), (9572081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9572081
  · decide +kernel

theorem prime_20967413 : Nat.Prime 20967413 := by
  apply nodeValid_prime [2, 19, 263, 1049] ⟨20967413, 2, [(2, 2), (19, 1), (263, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_263
    · exact prime_1049
  · decide +kernel

theorem prime_21870461 : Nat.Prime 21870461 := by
  apply nodeValid_prime [2, 5, 631, 1733] ⟨21870461, 3, [(2, 2), (5, 1), (631, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_631
    · exact prime_1733
  · decide +kernel

theorem prime_24168797 : Nat.Prime 24168797 := by
  apply nodeValid_prime [2, 1051, 5749] ⟨24168797, 2, [(2, 2), (1051, 1), (5749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1051
    · exact prime_5749
  · decide +kernel

theorem prime_25084799 : Nat.Prime 25084799 := by
  apply nodeValid_prime [2, 197, 63667] ⟨25084799, 11, [(2, 1), (197, 1), (63667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_63667
  · decide +kernel

theorem prime_25364719 : Nat.Prime 25364719 := by
  apply nodeValid_prime [2, 3, 469717] ⟨25364719, 6, [(2, 1), (3, 3), (469717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_469717
  · decide +kernel

theorem prime_49873519 : Nat.Prime 49873519 := by
  apply nodeValid_prime [2, 3, 19, 145829] ⟨49873519, 3, [(2, 1), (3, 2), (19, 1), (145829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_145829
  · decide +kernel

theorem prime_51563879 : Nat.Prime 51563879 := by
  apply nodeValid_prime [2, 241, 106979] ⟨51563879, 11, [(2, 1), (241, 1), (106979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_106979
  · decide +kernel

theorem prime_52674793 : Nat.Prime 52674793 := by
  apply nodeValid_prime [2, 3, 53, 41411] ⟨52674793, 11, [(2, 3), (3, 1), (53, 1), (41411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_41411
  · decide +kernel

theorem prime_83912489 : Nat.Prime 83912489 := by
  apply nodeValid_prime [2, 11, 953551] ⟨83912489, 3, [(2, 3), (11, 1), (953551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_953551
  · decide +kernel

theorem prime_91500119 : Nat.Prime 91500119 := by
  apply nodeValid_prime [2, 23, 1989133] ⟨91500119, 7, [(2, 1), (23, 1), (1989133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1989133
  · decide +kernel

theorem prime_112198687 : Nat.Prime 112198687 := by
  apply nodeValid_prime [2, 3, 19, 984199] ⟨112198687, 3, [(2, 1), (3, 1), (19, 1), (984199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_984199
  · decide +kernel

theorem prime_116814037 : Nat.Prime 116814037 := by
  apply nodeValid_prime [2, 3, 9734503] ⟨116814037, 5, [(2, 2), (3, 1), (9734503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9734503
  · decide +kernel

theorem prime_124223219 : Nat.Prime 124223219 := by
  apply nodeValid_prime [2, 7, 8873087] ⟨124223219, 2, [(2, 1), (7, 1), (8873087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8873087
  · decide +kernel

theorem prime_131736769 : Nat.Prime 131736769 := by
  apply nodeValid_prime [2, 3, 277, 2477] ⟨131736769, 7, [(2, 6), (3, 1), (277, 1), (2477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_2477
  · decide +kernel

theorem prime_143985323 : Nat.Prime 143985323 := by
  apply nodeValid_prime [2, 13, 5537897] ⟨143985323, 2, [(2, 1), (13, 1), (5537897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5537897
  · decide +kernel

theorem prime_179911909 : Nat.Prime 179911909 := by
  apply nodeValid_prime [2, 3, 11, 37, 4093] ⟨179911909, 2, [(2, 2), (3, 3), (11, 1), (37, 1), (4093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_4093
  · decide +kernel

theorem prime_183000239 : Nat.Prime 183000239 := by
  apply nodeValid_prime [2, 91500119] ⟨183000239, 7, [(2, 1), (91500119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_91500119
  · decide +kernel

theorem prime_287970647 : Nat.Prime 287970647 := by
  apply nodeValid_prime [2, 143985323] ⟨287970647, 5, [(2, 1), (143985323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_143985323
  · decide +kernel

theorem prime_303217793 : Nat.Prime 303217793 := by
  apply nodeValid_prime [2, 173, 13693] ⟨303217793, 3, [(2, 7), (173, 1), (13693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_13693
  · decide +kernel

theorem prime_323795051 : Nat.Prime 323795051 := by
  apply nodeValid_prime [2, 5, 6475901] ⟨323795051, 2, [(2, 1), (5, 2), (6475901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6475901
  · decide +kernel

theorem prime_362683133 : Nat.Prime 362683133 := by
  apply nodeValid_prime [2, 7, 12952969] ⟨362683133, 2, [(2, 2), (7, 1), (12952969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12952969
  · decide +kernel

theorem prime_371139541 : Nat.Prime 371139541 := by
  apply nodeValid_prime [2, 3, 5, 19, 379, 859] ⟨371139541, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (379, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_379
    · exact prime_859
  · decide +kernel

theorem prime_468048821 : Nat.Prime 468048821 := by
  apply nodeValid_prime [2, 5, 1153, 20297] ⟨468048821, 2, [(2, 2), (5, 1), (1153, 1), (20297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1153
    · exact prime_20297
  · decide +kernel

theorem prime_490882591 : Nat.Prime 490882591 := by
  apply nodeValid_prime [2, 3, 5, 11, 109, 4549] ⟨490882591, 6, [(2, 1), (3, 2), (5, 1), (11, 1), (109, 1), (4549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_109
    · exact prime_4549
  · decide +kernel

theorem prime_552964801 : Nat.Prime 552964801 := by
  apply nodeValid_prime [2, 3, 5, 115201] ⟨552964801, 41, [(2, 6), (3, 1), (5, 2), (115201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_115201
  · decide +kernel

theorem prime_831077519 : Nat.Prime 831077519 := by
  apply nodeValid_prime [2, 19, 21870461] ⟨831077519, 29, [(2, 1), (19, 1), (21870461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_21870461
  · decide +kernel

theorem prime_933002069 : Nat.Prime 933002069 := by
  apply nodeValid_prime [2, 19, 41, 67, 109] ⟨933002069, 2, [(2, 2), (19, 1), (41, 2), (67, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_67
    · exact prime_109
  · decide +kernel

theorem prime_1182913337 : Nat.Prime 1182913337 := by
  apply nodeValid_prime [2, 11, 281, 47837] ⟨1182913337, 3, [(2, 3), (11, 1), (281, 1), (47837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_281
    · exact prime_47837
  · decide +kernel

theorem prime_1280400893 : Nat.Prime 1280400893 := by
  apply nodeValid_prime [2, 23, 1459, 9539] ⟨1280400893, 2, [(2, 2), (23, 1), (1459, 1), (9539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1459
    · exact prime_9539
  · decide +kernel

theorem prime_1421406887 : Nat.Prime 1421406887 := by
  apply nodeValid_prime [2, 113, 6289411] ⟨1421406887, 5, [(2, 1), (113, 1), (6289411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_6289411
  · decide +kernel

theorem prime_1793263697 : Nat.Prime 1793263697 := by
  apply nodeValid_prime [2, 7, 31, 516493] ⟨1793263697, 3, [(2, 4), (7, 1), (31, 1), (516493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_516493
  · decide +kernel

theorem prime_2065614193 : Nat.Prime 2065614193 := by
  apply nodeValid_prime [2, 3, 14344543] ⟨2065614193, 5, [(2, 4), (3, 2), (14344543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14344543
  · decide +kernel

theorem prime_5529648011 : Nat.Prime 5529648011 := by
  apply nodeValid_prime [2, 5, 552964801] ⟨5529648011, 6, [(2, 1), (5, 1), (552964801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_552964801
  · decide +kernel

theorem prime_6104483239 : Nat.Prime 6104483239 := by
  apply nodeValid_prime [2, 3, 7, 29, 617, 8123] ⟨6104483239, 15, [(2, 1), (3, 1), (7, 1), (29, 1), (617, 1), (8123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_617
    · exact prime_8123
  · decide +kernel

theorem prime_7429682881 : Nat.Prime 7429682881 := by
  apply nodeValid_prime [2, 3, 5, 37, 61, 127] ⟨7429682881, 7, [(2, 6), (3, 4), (5, 1), (37, 1), (61, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_61
    · exact prime_127
  · decide +kernel

theorem prime_8388072023 : Nat.Prime 8388072023 := by
  apply nodeValid_prime [2, 11, 1439, 264959] ⟨8388072023, 5, [(2, 1), (11, 1), (1439, 1), (264959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1439
    · exact prime_264959
  · decide +kernel

theorem prime_8456476157 : Nat.Prime 8456476157 := by
  apply nodeValid_prime [2, 41, 51563879] ⟨8456476157, 2, [(2, 2), (41, 1), (51563879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_51563879
  · decide +kernel

theorem prime_11346014819 : Nat.Prime 11346014819 := by
  apply nodeValid_prime [2, 31, 183000239] ⟨11346014819, 2, [(2, 1), (31, 1), (183000239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_183000239
  · decide +kernel

theorem prime_11588454461 : Nat.Prime 11588454461 := by
  apply nodeValid_prime [2, 5, 11, 52674793] ⟨11588454461, 3, [(2, 2), (5, 1), (11, 1), (52674793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_52674793
  · decide +kernel

theorem prime_12334819303 : Nat.Prime 12334819303 := by
  apply nodeValid_prime [2, 3, 13, 17, 863, 3593] ⟨12334819303, 3, [(2, 1), (3, 2), (13, 1), (17, 1), (863, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_863
    · exact prime_3593
  · decide +kernel

theorem prime_12393685159 : Nat.Prime 12393685159 := by
  apply nodeValid_prime [2, 3, 2065614193] ⟨12393685159, 7, [(2, 1), (3, 1), (2065614193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2065614193
  · decide +kernel

theorem prime_19151431297 : Nat.Prime 19151431297 := by
  apply nodeValid_prime [2, 3, 49873519] ⟨19151431297, 5, [(2, 7), (3, 1), (49873519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49873519
  · decide +kernel

theorem prime_22733937529 : Nat.Prime 22733937529 := by
  apply nodeValid_prime [2, 3, 37, 709, 36109] ⟨22733937529, 22, [(2, 3), (3, 1), (37, 1), (709, 1), (36109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_709
    · exact prime_36109
  · decide +kernel

theorem prime_50328432139 : Nat.Prime 50328432139 := by
  apply nodeValid_prime [2, 3, 8388072023] ⟨50328432139, 2, [(2, 1), (3, 1), (8388072023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8388072023
  · decide +kernel

theorem prime_118504008619 : Nat.Prime 118504008619 := by
  apply nodeValid_prime [2, 3, 79, 821, 304517] ⟨118504008619, 2, [(2, 1), (3, 1), (79, 1), (821, 1), (304517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_821
    · exact prime_304517
  · decide +kernel

theorem prime_166239154573 : Nat.Prime 166239154573 := by
  apply nodeValid_prime [2, 3, 19, 1307, 557857] ⟨166239154573, 2, [(2, 2), (3, 1), (19, 1), (1307, 1), (557857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1307
    · exact prime_557857
  · decide +kernel

theorem prime_187112862569 : Nat.Prime 187112862569 := by
  apply nodeValid_prime [2, 233, 3833, 26189] ⟨187112862569, 3, [(2, 3), (233, 1), (3833, 1), (26189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_3833
    · exact prime_26189
  · decide +kernel

theorem prime_221231079119 : Nat.Prime 221231079119 := by
  apply nodeValid_prime [2, 7, 89, 25364719] ⟨221231079119, 7, [(2, 1), (7, 2), (89, 1), (25364719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_25364719
  · decide +kernel

theorem prime_262208332669 : Nat.Prime 262208332669 := by
  apply nodeValid_prime [2, 3, 67, 71, 4593377] ⟨262208332669, 2, [(2, 2), (3, 1), (67, 1), (71, 1), (4593377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_71
    · exact prime_4593377
  · decide +kernel

theorem prime_442041441487 : Nat.Prime 442041441487 := by
  apply nodeValid_prime [2, 3, 601, 2903, 42227] ⟨442041441487, 3, [(2, 1), (3, 1), (601, 1), (2903, 1), (42227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_601
    · exact prime_2903
    · exact prime_42227
  · decide +kernel

theorem prime_659284189813 : Nat.Prime 659284189813 := by
  apply nodeValid_prime [2, 3, 6104483239] ⟨659284189813, 2, [(2, 2), (3, 3), (6104483239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6104483239
  · decide +kernel

theorem prime_1318568376683 : Nat.Prime 1318568376683 := by
  apply nodeValid_prime [2, 29, 22733937529] ⟨1318568376683, 2, [(2, 1), (29, 1), (22733937529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_22733937529
  · decide +kernel

theorem prime_2602102745651 : Nat.Prime 2602102745651 := by
  apply nodeValid_prime [2, 5, 271, 2287, 83969] ⟨2602102745651, 2, [(2, 1), (5, 2), (271, 1), (2287, 1), (83969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
    · exact prime_2287
    · exact prime_83969
  · decide +kernel

theorem prime_2602102746167 : Nat.Prime 2602102746167 := by
  apply nodeValid_prime [2, 7, 11, 19, 4481, 198461] ⟨2602102746167, 5, [(2, 1), (7, 1), (11, 1), (19, 1), (4481, 1), (198461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_4481
    · exact prime_198461
  · decide +kernel

theorem prime_2602102766293 : Nat.Prime 2602102766293 := by
  apply nodeValid_prime [2, 3, 251, 287970647] ⟨2602102766293, 2, [(2, 2), (3, 2), (251, 1), (287970647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_287970647
  · decide +kernel

theorem prime_2604594656357 : Nat.Prime 2604594656357 := by
  apply nodeValid_prime [2, 7, 11, 8456476157] ⟨2604594656357, 2, [(2, 2), (7, 1), (11, 1), (8456476157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_8456476157
  · decide +kernel

theorem prime_2604594656393 : Nat.Prime 2604594656393 := by
  apply nodeValid_prime [2, 17, 19151431297] ⟨2604594656393, 3, [(2, 3), (17, 1), (19151431297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19151431297
  · decide +kernel

theorem prime_2604594672737 : Nat.Prime 2604594672737 := by
  apply nodeValid_prime [2, 7, 19, 53, 11546827] ⟨2604594672737, 3, [(2, 5), (7, 1), (19, 1), (53, 1), (11546827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_53
    · exact prime_11546827
  · decide +kernel

theorem prime_2607088132391 : Nat.Prime 2607088132391 := by
  apply nodeValid_prime [2, 5, 7, 23, 67, 24168797] ⟨2607088132391, 13, [(2, 1), (5, 1), (7, 1), (23, 1), (67, 1), (24168797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_67
    · exact prime_24168797
  · decide +kernel

theorem prime_2607088132421 : Nat.Prime 2607088132421 := by
  apply nodeValid_prime [2, 5, 6217, 20967413] ⟨2607088132421, 2, [(2, 2), (5, 1), (6217, 1), (20967413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6217
    · exact prime_20967413
  · decide +kernel

theorem prime_2607088189619 : Nat.Prime 2607088189619 := by
  apply nodeValid_prime [2, 11, 118504008619] ⟨2607088189619, 6, [(2, 1), (11, 1), (118504008619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_118504008619
  · decide +kernel

theorem prime_2609583325873 : Nat.Prime 2609583325873 := by
  apply nodeValid_prime [2, 3, 101, 1021, 527209] ⟨2609583325873, 11, [(2, 4), (3, 1), (101, 1), (1021, 1), (527209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1021
    · exact prime_527209
  · decide +kernel

theorem prime_2609583408371 : Nat.Prime 2609583408371 := by
  apply nodeValid_prime [2, 5, 23, 11346014819] ⟨2609583408371, 2, [(2, 1), (5, 1), (23, 1), (11346014819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_11346014819
  · decide +kernel

theorem prime_2609583409661 : Nat.Prime 2609583409661 := by
  apply nodeValid_prime [2, 5, 157, 831077519] ⟨2609583409661, 2, [(2, 2), (5, 1), (157, 1), (831077519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_831077519
  · decide +kernel

theorem prime_2612080089559 : Nat.Prime 2612080089559 := by
  apply nodeValid_prime [2, 3, 17, 23, 371139541] ⟨2612080089559, 12, [(2, 1), (3, 2), (17, 1), (23, 1), (371139541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_371139541
  · decide +kernel

theorem prime_2612080119871 : Nat.Prime 2612080119871 := by
  apply nodeValid_prime [2, 3, 5, 13, 89, 25084799] ⟨2612080119871, 3, [(2, 1), (3, 2), (5, 1), (13, 1), (89, 1), (25084799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_89
    · exact prime_25084799
  · decide +kernel

theorem prime_2612080120339 : Nat.Prime 2612080120339 := by
  apply nodeValid_prime [2, 3, 13, 563, 1297, 15287] ⟨2612080120339, 2, [(2, 1), (3, 2), (13, 1), (563, 1), (1297, 1), (15287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_563
    · exact prime_1297
    · exact prime_15287
  · decide +kernel

theorem prime_2614578470227 : Nat.Prime 2614578470227 := by
  apply nodeValid_prime [2, 3, 1793263697] ⟨2614578470227, 5, [(2, 1), (3, 6), (1793263697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1793263697
  · decide +kernel

theorem prime_2614578623507 : Nat.Prime 2614578623507 := by
  apply nodeValid_prime [2, 1021, 1280400893] ⟨2614578623507, 2, [(2, 1), (1021, 1), (1280400893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1021
    · exact prime_1280400893
  · decide +kernel

theorem prime_2614578624509 : Nat.Prime 2614578624509 := by
  apply nodeValid_prime [2, 397, 5897, 279203] ⟨2614578624509, 2, [(2, 2), (397, 1), (5897, 1), (279203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_5897
    · exact prime_279203
  · decide +kernel

theorem prime_2617078466789 : Nat.Prime 2617078466789 := by
  apply nodeValid_prime [2, 17, 53, 73, 101, 149, 661] ⟨2617078466789, 3, [(2, 2), (17, 1), (53, 1), (73, 1), (101, 1), (149, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_53
    · exact prime_73
    · exact prime_101
    · exact prime_149
    · exact prime_661
  · decide +kernel

theorem prime_2617078470913 : Nat.Prime 2617078470913 := by
  apply nodeValid_prime [2, 3, 881, 143257] ⟨2617078470913, 5, [(2, 8), (3, 4), (881, 1), (143257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_881
    · exact prime_143257
  · decide +kernel

theorem prime_2617078471229 : Nat.Prime 2617078471229 := by
  apply nodeValid_prime [2, 13, 50328432139] ⟨2617078471229, 2, [(2, 2), (13, 1), (50328432139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_50328432139
  · decide +kernel

theorem prime_2619580075283 : Nat.Prime 2619580075283 := by
  apply nodeValid_prime [2, 127, 15791, 653113] ⟨2619580075283, 2, [(2, 1), (127, 1), (15791, 1), (653113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_15791
    · exact prime_653113
  · decide +kernel

theorem prime_2619580075967 : Nat.Prime 2619580075967 := by
  apply nodeValid_prime [2, 7, 187112862569] ⟨2619580075967, 5, [(2, 1), (7, 1), (187112862569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_187112862569
  · decide +kernel

theorem prime_2619580081603 : Nat.Prime 2619580081603 := by
  apply nodeValid_prime [2, 3, 11, 43, 83912489] ⟨2619580081603, 2, [(2, 1), (3, 1), (11, 2), (43, 1), (83912489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_83912489
  · decide +kernel

theorem prime_2622083315191 : Nat.Prime 2622083315191 := by
  apply nodeValid_prime [2, 3, 5, 19, 41, 112198687] ⟨2622083315191, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (112198687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_112198687
  · decide +kernel

theorem prime_2622083325791 : Nat.Prime 2622083325791 := by
  apply nodeValid_prime [2, 5, 31, 73453, 115153] ⟨2622083325791, 13, [(2, 1), (5, 1), (31, 1), (73453, 1), (115153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_73453
    · exact prime_115153
  · decide +kernel

theorem prime_2622083326691 : Nat.Prime 2622083326691 := by
  apply nodeValid_prime [2, 5, 262208332669] ⟨2622083326691, 6, [(2, 1), (5, 1), (262208332669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_262208332669
  · decide +kernel

theorem prime_2624588168651 : Nat.Prime 2624588168651 := by
  apply nodeValid_prime [2, 5, 7, 1873, 81707] ⟨2624588168651, 7, [(2, 1), (5, 2), (7, 3), (1873, 1), (81707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1873
    · exact prime_81707
  · decide +kernel

theorem prime_2624588170649 : Nat.Prime 2624588170649 := by
  apply nodeValid_prime [2, 17137, 19144163] ⟨2624588170649, 3, [(2, 3), (17137, 1), (19144163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17137
    · exact prime_19144163
  · decide +kernel

theorem prime_2624588171033 : Nat.Prime 2624588171033 := by
  apply nodeValid_prime [2, 19, 139, 124223219] ⟨2624588171033, 3, [(2, 3), (19, 1), (139, 1), (124223219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_139
    · exact prime_124223219
  · decide +kernel

theorem prime_2627094592393 : Nat.Prime 2627094592393 := by
  apply nodeValid_prime [2, 3, 211, 2927, 177239] ⟨2627094592393, 5, [(2, 3), (3, 1), (211, 1), (2927, 1), (177239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_2927
    · exact prime_177239
  · decide +kernel

theorem prime_2627094593017 : Nat.Prime 2627094593017 := by
  apply nodeValid_prime [2, 3, 37, 71, 13889389] ⟨2627094593017, 5, [(2, 3), (3, 2), (37, 1), (71, 1), (13889389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_13889389
  · decide +kernel

theorem prime_2627094647399 : Nat.Prime 2627094647399 := by
  apply nodeValid_prime [2, 13, 59, 131736769] ⟨2627094647399, 41, [(2, 1), (13, 2), (59, 1), (131736769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_59
    · exact prime_131736769
  · decide +kernel

theorem prime_2629602616141 : Nat.Prime 2629602616141 := by
  apply nodeValid_prime [2, 3, 5, 12487, 1169929] ⟨2629602616141, 6, [(2, 2), (3, 2), (5, 1), (12487, 1), (1169929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12487
    · exact prime_1169929
  · decide +kernel

theorem prime_2629602616843 : Nat.Prime 2629602616843 := by
  apply nodeValid_prime [2, 3, 53, 331, 8327483] ⟨2629602616843, 3, [(2, 1), (3, 2), (53, 1), (331, 1), (8327483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_331
    · exact prime_8327483
  · decide +kernel

theorem prime_2629602740951 : Nat.Prime 2629602740951 := by
  apply nodeValid_prime [2, 5, 37, 1421406887] ⟨2629602740951, 7, [(2, 1), (5, 2), (37, 1), (1421406887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1421406887
  · decide +kernel

theorem prime_2632112452943 : Nat.Prime 2632112452943 := by
  apply nodeValid_prime [2, 7, 383, 490882591] ⟨2632112452943, 5, [(2, 1), (7, 1), (383, 1), (490882591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_383
    · exact prime_490882591
  · decide +kernel

theorem prime_2632112453237 : Nat.Prime 2632112453237 := by
  apply nodeValid_prime [2, 7, 17, 5529648011] ⟨2632112453237, 2, [(2, 2), (7, 1), (17, 1), (5529648011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_5529648011
  · decide +kernel

theorem prime_2632112455613 : Nat.Prime 2632112455613 := by
  apply nodeValid_prime [2, 37, 137, 4409, 29443] ⟨2632112455613, 2, [(2, 2), (37, 1), (137, 1), (4409, 1), (29443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_137
    · exact prime_4409
    · exact prime_29443
  · decide +kernel

theorem prime_2634623790499 : Nat.Prime 2634623790499 := by
  apply nodeValid_prime [2, 3, 7, 179, 116814037] ⟨2634623790499, 7, [(2, 1), (3, 2), (7, 1), (179, 1), (116814037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_179
    · exact prime_116814037
  · decide +kernel

theorem prime_2634623800741 : Nat.Prime 2634623800741 := by
  apply nodeValid_prime [2, 3, 5, 31, 151, 1193, 2621] ⟨2634623800741, 2, [(2, 2), (3, 2), (5, 1), (31, 1), (151, 1), (1193, 1), (2621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_151
    · exact prime_1193
    · exact prime_2621
  · decide +kernel

theorem prime_2634623801003 : Nat.Prime 2634623801003 := by
  apply nodeValid_prime [2, 89, 49943, 296363] ⟨2634623801003, 2, [(2, 1), (89, 1), (49943, 1), (296363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_49943
    · exact prime_296363
  · decide +kernel

theorem prime_2637136753367 : Nat.Prime 2637136753367 := by
  apply nodeValid_prime [2, 1318568376683] ⟨2637136753367, 5, [(2, 1), (1318568376683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1318568376683
  · decide +kernel

theorem prime_2637136759253 : Nat.Prime 2637136759253 := by
  apply nodeValid_prime [2, 659284189813] ⟨2637136759253, 2, [(2, 2), (659284189813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_659284189813
  · decide +kernel

theorem prime_2637136759781 : Nat.Prime 2637136759781 := by
  apply nodeValid_prime [2, 5, 239, 313, 1762627] ⟨2637136759781, 2, [(2, 2), (5, 1), (239, 1), (313, 1), (1762627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_313
    · exact prime_1762627
  · decide +kernel

theorem prime_2639651330843 : Nat.Prime 2639651330843 := by
  apply nodeValid_prime [2, 107, 12334819303] ⟨2639651330843, 2, [(2, 1), (107, 1), (12334819303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_12334819303
  · decide +kernel

theorem prime_2639651331437 : Nat.Prime 2639651331437 := by
  apply nodeValid_prime [2, 7, 19, 89, 4733, 11779] ⟨2639651331437, 5, [(2, 2), (7, 1), (19, 1), (89, 1), (4733, 1), (11779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_89
    · exact prime_4733
    · exact prime_11779
  · decide +kernel

theorem prime_2639651332151 : Nat.Prime 2639651332151 := by
  apply nodeValid_prime [2, 5, 7, 151, 1447, 4931] ⟨2639651332151, 7, [(2, 1), (5, 2), (7, 2), (151, 1), (1447, 1), (4931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_151
    · exact prime_1447
    · exact prime_4931
  · decide +kernel

theorem prime_2642167538251 : Nat.Prime 2642167538251 := by
  apply nodeValid_prime [2, 3, 5, 1021, 3450431] ⟨2642167538251, 3, [(2, 1), (3, 1), (5, 3), (1021, 1), (3450431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1021
    · exact prime_3450431
  · decide +kernel

theorem prime_2642167616161 : Nat.Prime 2642167616161 := by
  apply nodeValid_prime [2, 3, 5, 17, 323795051] ⟨2642167616161, 7, [(2, 5), (3, 1), (5, 1), (17, 1), (323795051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_323795051
  · decide +kernel

theorem prime_2642167617109 : Nat.Prime 2642167617109 := by
  apply nodeValid_prime [2, 3, 19, 11588454461] ⟨2642167617109, 2, [(2, 2), (3, 1), (19, 1), (11588454461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11588454461
  · decide +kernel

theorem prime_2644685373347 : Nat.Prime 2644685373347 := by
  apply nodeValid_prime [2, 223403, 5919091] ⟨2644685373347, 2, [(2, 1), (223403, 1), (5919091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223403
    · exact prime_5919091
  · decide +kernel

theorem prime_2644685405009 : Nat.Prime 2644685405009 := by
  apply nodeValid_prime [2, 29851, 5537263] ⟨2644685405009, 3, [(2, 4), (29851, 1), (5537263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29851
    · exact prime_5537263
  · decide +kernel

theorem prime_2644685405837 : Nat.Prime 2644685405837 := by
  apply nodeValid_prime [2, 1823, 362683133] ⟨2644685405837, 2, [(2, 2), (1823, 1), (362683133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1823
    · exact prime_362683133
  · decide +kernel

theorem prime_2647204832809 : Nat.Prime 2647204832809 := by
  apply nodeValid_prime [2, 3, 23, 281, 5688803] ⟨2647204832809, 7, [(2, 3), (3, 2), (23, 1), (281, 1), (5688803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_281
    · exact prime_5688803
  · decide +kernel

theorem prime_2647204853981 : Nat.Prime 2647204853981 := by
  apply nodeValid_prime [2, 5, 21961, 6027059] ⟨2647204853981, 2, [(2, 2), (5, 1), (21961, 1), (6027059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_21961
    · exact prime_6027059
  · decide +kernel

theorem prime_2647204854031 : Nat.Prime 2647204854031 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 3307, 47563] ⟨2647204854031, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (17, 1), (3307, 1), (47563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_3307
    · exact prime_47563
  · decide +kernel

theorem prime_2649725874881 : Nat.Prime 2649725874881 := by
  apply nodeValid_prime [2, 5, 7, 1182913337] ⟨2649725874881, 3, [(2, 6), (5, 1), (7, 1), (1182913337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1182913337
  · decide +kernel

theorem prime_2649725875961 : Nat.Prime 2649725875961 := by
  apply nodeValid_prime [2, 5, 71, 933002069] ⟨2649725875961, 3, [(2, 3), (5, 1), (71, 1), (933002069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_933002069
  · decide +kernel

theorem prime_2649725916941 : Nat.Prime 2649725916941 := by
  apply nodeValid_prime [2, 5, 173, 2683, 285433] ⟨2649725916941, 2, [(2, 2), (5, 1), (173, 1), (2683, 1), (285433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_2683
    · exact prime_285433
  · decide +kernel

theorem prime_2652248624027 : Nat.Prime 2652248624027 := by
  apply nodeValid_prime [2, 107, 12393685159] ⟨2652248624027, 2, [(2, 1), (107, 1), (12393685159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_12393685159
  · decide +kernel

theorem prime_2652248646349 : Nat.Prime 2652248646349 := by
  apply nodeValid_prime [2, 3, 7, 2003, 15763549] ⟨2652248646349, 10, [(2, 2), (3, 1), (7, 1), (2003, 1), (15763549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2003
    · exact prime_15763549
  · decide +kernel

theorem prime_2652248648923 : Nat.Prime 2652248648923 := by
  apply nodeValid_prime [2, 3, 442041441487] ⟨2652248648923, 2, [(2, 1), (3, 1), (442041441487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_442041441487
  · decide +kernel

theorem prime_2654772912433 : Nat.Prime 2654772912433 := by
  apply nodeValid_prime [2, 3, 17, 19, 479, 119159] ⟨2654772912433, 5, [(2, 4), (3, 2), (17, 1), (19, 1), (479, 1), (119159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_479
    · exact prime_119159
  · decide +kernel

theorem prime_2654772912713 : Nat.Prime 2654772912713 := by
  apply nodeValid_prime [2, 709, 468048821] ⟨2654772912713, 3, [(2, 3), (709, 1), (468048821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_709
    · exact prime_468048821
  · decide +kernel

theorem prime_2654772949429 : Nat.Prime 2654772949429 := by
  apply nodeValid_prime [2, 3, 221231079119] ⟨2654772949429, 6, [(2, 2), (3, 1), (221231079119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_221231079119
  · decide +kernel

theorem prime_2657298895819 : Nat.Prime 2657298895819 := by
  apply nodeValid_prime [2, 3, 7, 17, 19, 103, 157, 12113] ⟨2657298895819, 7, [(2, 1), (3, 1), (7, 1), (17, 1), (19, 1), (103, 1), (157, 1), (12113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
    · exact prime_103
    · exact prime_157
    · exact prime_12113
  · decide +kernel

theorem prime_2657298895931 : Nat.Prime 2657298895931 := by
  apply nodeValid_prime [2, 5, 7, 211, 179911909] ⟨2657298895931, 2, [(2, 1), (5, 1), (7, 1), (211, 1), (179911909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_211
    · exact prime_179911909
  · decide +kernel

theorem prime_2657298903761 : Nat.Prime 2657298903761 := by
  apply nodeValid_prime [2, 5, 19, 13477, 129719] ⟨2657298903761, 3, [(2, 4), (5, 1), (19, 1), (13477, 1), (129719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_13477
    · exact prime_129719
  · decide +kernel

theorem prime_2659826471399 : Nat.Prime 2659826471399 := by
  apply nodeValid_prime [2, 179, 7429682881] ⟨2659826471399, 11, [(2, 1), (179, 1), (7429682881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_7429682881
  · decide +kernel

theorem prime_2659826473169 : Nat.Prime 2659826473169 := by
  apply nodeValid_prime [2, 166239154573] ⟨2659826473169, 3, [(2, 4), (166239154573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_166239154573
  · decide +kernel

theorem prime_2659826480197 : Nat.Prime 2659826480197 := by
  apply nodeValid_prime [2, 3, 17, 43, 303217793] ⟨2659826480197, 5, [(2, 2), (3, 1), (17, 1), (43, 1), (303217793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_303217793
  · decide +kernel

theorem prime_2662355663063 : Nat.Prime 2662355663063 := by
  apply nodeValid_prime [2, 335381, 3969151] ⟨2662355663063, 5, [(2, 1), (335381, 1), (3969151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_335381
    · exact prime_3969151
  · decide +kernel

theorem prime_2662355684311 : Nat.Prime 2662355684311 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 311, 1772387] ⟨2662355684311, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (311, 1), (1772387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_311
    · exact prime_1772387
  · decide +kernel

end Sude.Lucas.Generated
