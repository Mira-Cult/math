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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4133 : Nat.Prime 4133 := by
  apply nodeValid_prime [2, 1033] ⟨4133, 2, [(2, 2), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1033
  · decide +kernel

theorem prime_5813 : Nat.Prime 5813 := by
  apply nodeValid_prime [2, 1453] ⟨5813, 2, [(2, 2), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1453
  · decide +kernel

theorem prime_7043 : Nat.Prime 7043 := by
  apply nodeValid_prime [2, 7, 503] ⟨7043, 2, [(2, 1), (7, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_503
  · decide +kernel

theorem prime_8297 : Nat.Prime 8297 := by
  apply nodeValid_prime [2, 17, 61] ⟨8297, 3, [(2, 3), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_9151 : Nat.Prime 9151 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨9151, 3, [(2, 1), (3, 1), (5, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_9257 : Nat.Prime 9257 := by
  apply nodeValid_prime [2, 13, 89] ⟨9257, 3, [(2, 3), (13, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_89
  · decide +kernel

theorem prime_10313 : Nat.Prime 10313 := by
  apply nodeValid_prime [2, 1289] ⟨10313, 3, [(2, 3), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1289
  · decide +kernel

theorem prime_12959 : Nat.Prime 12959 := by
  apply nodeValid_prime [2, 11, 19, 31] ⟨12959, 7, [(2, 1), (11, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_14087 : Nat.Prime 14087 := by
  apply nodeValid_prime [2, 7043] ⟨14087, 5, [(2, 1), (7043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7043
  · decide +kernel

theorem prime_15217 : Nat.Prime 15217 := by
  apply nodeValid_prime [2, 3, 317] ⟨15217, 10, [(2, 4), (3, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
  · decide +kernel

theorem prime_17579 : Nat.Prime 17579 := by
  apply nodeValid_prime [2, 11, 17, 47] ⟨17579, 2, [(2, 1), (11, 1), (17, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_19483 : Nat.Prime 19483 := by
  apply nodeValid_prime [2, 3, 17, 191] ⟨19483, 2, [(2, 1), (3, 1), (17, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_191
  · decide +kernel

theorem prime_26161 : Nat.Prime 26161 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨26161, 13, [(2, 4), (3, 1), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_28661 : Nat.Prime 28661 := by
  apply nodeValid_prime [2, 5, 1433] ⟨28661, 2, [(2, 2), (5, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1433
  · decide +kernel

theorem prime_31793 : Nat.Prime 31793 := by
  apply nodeValid_prime [2, 1987] ⟨31793, 3, [(2, 4), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1987
  · decide +kernel

theorem prime_34499 : Nat.Prime 34499 := by
  apply nodeValid_prime [2, 47, 367] ⟨34499, 2, [(2, 1), (47, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_367
  · decide +kernel

theorem prime_35159 : Nat.Prime 35159 := by
  apply nodeValid_prime [2, 17579] ⟨35159, 11, [(2, 1), (17579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17579
  · decide +kernel

theorem prime_43607 : Nat.Prime 43607 := by
  apply nodeValid_prime [2, 21803] ⟨43607, 5, [(2, 1), (21803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21803
  · decide +kernel

theorem prime_52301 : Nat.Prime 52301 := by
  apply nodeValid_prime [2, 5, 523] ⟨52301, 2, [(2, 2), (5, 2), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_523
  · decide +kernel

theorem prime_63587 : Nat.Prime 63587 := by
  apply nodeValid_prime [2, 31793] ⟨63587, 2, [(2, 1), (31793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31793
  · decide +kernel

theorem prime_65761 : Nat.Prime 65761 := by
  apply nodeValid_prime [2, 3, 5, 137] ⟨65761, 7, [(2, 5), (3, 1), (5, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_65851 : Nat.Prime 65851 := by
  apply nodeValid_prime [2, 3, 5, 439] ⟨65851, 3, [(2, 1), (3, 1), (5, 2), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_68371 : Nat.Prime 68371 := by
  apply nodeValid_prime [2, 3, 5, 43, 53] ⟨68371, 7, [(2, 1), (3, 1), (5, 1), (43, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_53
  · decide +kernel

theorem prime_70061 : Nat.Prime 70061 := by
  apply nodeValid_prime [2, 5, 31, 113] ⟨70061, 2, [(2, 2), (5, 1), (31, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_113
  · decide +kernel

theorem prime_78853 : Nat.Prime 78853 := by
  apply nodeValid_prime [2, 3, 6571] ⟨78853, 5, [(2, 2), (3, 1), (6571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6571
  · decide +kernel

theorem prime_89833 : Nat.Prime 89833 := by
  apply nodeValid_prime [2, 3, 19, 197] ⟨89833, 5, [(2, 3), (3, 1), (19, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_197
  · decide +kernel

theorem prime_94573 : Nat.Prime 94573 := by
  apply nodeValid_prime [2, 3, 37, 71] ⟨94573, 2, [(2, 2), (3, 2), (37, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
  · decide +kernel

theorem prime_100621 : Nat.Prime 100621 := by
  apply nodeValid_prime [2, 3, 5, 13, 43] ⟨100621, 18, [(2, 2), (3, 2), (5, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_101287 : Nat.Prime 101287 := by
  apply nodeValid_prime [2, 3, 17, 331] ⟨101287, 3, [(2, 1), (3, 2), (17, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_331
  · decide +kernel

theorem prime_105829 : Nat.Prime 105829 := by
  apply nodeValid_prime [2, 3, 8819] ⟨105829, 2, [(2, 2), (3, 1), (8819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8819
  · decide +kernel

theorem prime_107119 : Nat.Prime 107119 := by
  apply nodeValid_prime [2, 3, 11, 541] ⟨107119, 3, [(2, 1), (3, 2), (11, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_541
  · decide +kernel

theorem prime_142111 : Nat.Prime 142111 := by
  apply nodeValid_prime [2, 3, 5, 1579] ⟨142111, 6, [(2, 1), (3, 2), (5, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1579
  · decide +kernel

theorem prime_156967 : Nat.Prime 156967 := by
  apply nodeValid_prime [2, 3, 26161] ⟨156967, 5, [(2, 1), (3, 1), (26161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26161
  · decide +kernel

theorem prime_192373 : Nat.Prime 192373 := by
  apply nodeValid_prime [2, 3, 17, 23, 41] ⟨192373, 6, [(2, 2), (3, 1), (17, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_202877 : Nat.Prime 202877 := by
  apply nodeValid_prime [2, 67, 757] ⟨202877, 2, [(2, 2), (67, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_757
  · decide +kernel

theorem prime_205433 : Nat.Prime 205433 := by
  apply nodeValid_prime [2, 25679] ⟨205433, 3, [(2, 3), (25679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25679
  · decide +kernel

theorem prime_276461 : Nat.Prime 276461 := by
  apply nodeValid_prime [2, 5, 23, 601] ⟨276461, 2, [(2, 2), (5, 1), (23, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_601
  · decide +kernel

theorem prime_281273 : Nat.Prime 281273 := by
  apply nodeValid_prime [2, 35159] ⟨281273, 3, [(2, 3), (35159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35159
  · decide +kernel

theorem prime_376199 : Nat.Prime 376199 := by
  apply nodeValid_prime [2, 79, 2381] ⟨376199, 13, [(2, 1), (79, 1), (2381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_2381
  · decide +kernel

theorem prime_408497 : Nat.Prime 408497 := by
  apply nodeValid_prime [2, 11, 211] ⟨408497, 3, [(2, 4), (11, 2), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_211
  · decide +kernel

theorem prime_453833 : Nat.Prime 453833 := by
  apply nodeValid_prime [2, 17, 47, 71] ⟨453833, 3, [(2, 3), (17, 1), (47, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_71
  · decide +kernel

theorem prime_566047 : Nat.Prime 566047 := by
  apply nodeValid_prime [2, 3, 13, 41, 59] ⟨566047, 3, [(2, 1), (3, 2), (13, 1), (41, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_59
  · decide +kernel

theorem prime_615401 : Nat.Prime 615401 := by
  apply nodeValid_prime [2, 5, 17, 181] ⟨615401, 3, [(2, 3), (5, 2), (17, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_181
  · decide +kernel

theorem prime_760153 : Nat.Prime 760153 := by
  apply nodeValid_prime [2, 3, 19, 1667] ⟨760153, 5, [(2, 3), (3, 1), (19, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1667
  · decide +kernel

theorem prime_806257 : Nat.Prime 806257 := by
  apply nodeValid_prime [2, 3, 11, 509] ⟨806257, 15, [(2, 4), (3, 2), (11, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_509
  · decide +kernel

theorem prime_864419 : Nat.Prime 864419 := by
  apply nodeValid_prime [2, 79, 5471] ⟨864419, 2, [(2, 1), (79, 1), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_5471
  · decide +kernel

theorem prime_947411 : Nat.Prime 947411 := by
  apply nodeValid_prime [2, 5, 17, 5573] ⟨947411, 10, [(2, 1), (5, 1), (17, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_5573
  · decide +kernel

theorem prime_974387 : Nat.Prime 974387 := by
  apply nodeValid_prime [2, 7, 79, 881] ⟨974387, 6, [(2, 1), (7, 1), (79, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_881
  · decide +kernel

theorem prime_1090333 : Nat.Prime 1090333 := by
  apply nodeValid_prime [2, 3, 31, 977] ⟨1090333, 2, [(2, 2), (3, 2), (31, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_977
  · decide +kernel

theorem prime_1153531 : Nat.Prime 1153531 := by
  apply nodeValid_prime [2, 3, 5, 7, 1831] ⟨1153531, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1831
  · decide +kernel

theorem prime_1185319 : Nat.Prime 1185319 := by
  apply nodeValid_prime [2, 3, 65851] ⟨1185319, 3, [(2, 1), (3, 2), (65851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_65851
  · decide +kernel

theorem prime_1205773 : Nat.Prime 1205773 := by
  apply nodeValid_prime [2, 3, 89, 1129] ⟨1205773, 2, [(2, 2), (3, 1), (89, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_1129
  · decide +kernel

theorem prime_1263109 : Nat.Prime 1263109 := by
  apply nodeValid_prime [2, 3, 7, 11, 1367] ⟨1263109, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1367
  · decide +kernel

theorem prime_1437313 : Nat.Prime 1437313 := by
  apply nodeValid_prime [2, 3, 19, 197] ⟨1437313, 7, [(2, 7), (3, 1), (19, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_197
  · decide +kernel

theorem prime_1632121 : Nat.Prime 1632121 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 67] ⟨1632121, 19, [(2, 3), (3, 1), (5, 1), (7, 1), (29, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_67
  · decide +kernel

theorem prime_1722667 : Nat.Prime 1722667 := by
  apply nodeValid_prime [2, 3, 11, 43, 607] ⟨1722667, 3, [(2, 1), (3, 1), (11, 1), (43, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_607
  · decide +kernel

theorem prime_1948301 : Nat.Prime 1948301 := by
  apply nodeValid_prime [2, 5, 19483] ⟨1948301, 2, [(2, 2), (5, 2), (19483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19483
  · decide +kernel

theorem prime_2047523 : Nat.Prime 2047523 := by
  apply nodeValid_prime [2, 79, 12959] ⟨2047523, 2, [(2, 1), (79, 1), (12959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_12959
  · decide +kernel

theorem prime_2182259 : Nat.Prime 2182259 := by
  apply nodeValid_prime [2, 13, 83933] ⟨2182259, 2, [(2, 1), (13, 1), (83933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_83933
  · decide +kernel

theorem prime_2510449 : Nat.Prime 2510449 := by
  apply nodeValid_prime [2, 3, 52301] ⟨2510449, 11, [(2, 4), (3, 1), (52301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52301
  · decide +kernel

theorem prime_2999333 : Nat.Prime 2999333 := by
  apply nodeValid_prime [2, 7, 107119] ⟨2999333, 2, [(2, 2), (7, 1), (107119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107119
  · decide +kernel

theorem prime_3040613 : Nat.Prime 3040613 := by
  apply nodeValid_prime [2, 760153] ⟨3040613, 2, [(2, 2), (760153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_760153
  · decide +kernel

theorem prime_3330889 : Nat.Prime 3330889 := by
  apply nodeValid_prime [2, 3, 11, 31, 37] ⟨3330889, 17, [(2, 3), (3, 1), (11, 2), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_3862013 : Nat.Prime 3862013 := by
  apply nodeValid_prime [2, 7, 11, 12539] ⟨3862013, 2, [(2, 2), (7, 1), (11, 1), (12539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_12539
  · decide +kernel

theorem prime_4193141 : Nat.Prime 4193141 := by
  apply nodeValid_prime [2, 5, 7, 61, 491] ⟨4193141, 2, [(2, 2), (5, 1), (7, 1), (61, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_491
  · decide +kernel

theorem prime_4364519 : Nat.Prime 4364519 := by
  apply nodeValid_prime [2, 2182259] ⟨4364519, 11, [(2, 1), (2182259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2182259
  · decide +kernel

theorem prime_4829809 : Nat.Prime 4829809 := by
  apply nodeValid_prime [2, 3, 100621] ⟨4829809, 7, [(2, 4), (3, 1), (100621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_100621
  · decide +kernel

theorem prime_5089573 : Nat.Prime 5089573 := by
  apply nodeValid_prime [2, 3, 37, 3821] ⟨5089573, 2, [(2, 2), (3, 2), (37, 1), (3821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_3821
  · decide +kernel

theorem prime_5945353 : Nat.Prime 5945353 := by
  apply nodeValid_prime [2, 3, 7, 43, 823] ⟨5945353, 5, [(2, 3), (3, 1), (7, 1), (43, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_823
  · decide +kernel

theorem prime_6081227 : Nat.Prime 6081227 := by
  apply nodeValid_prime [2, 3040613] ⟨6081227, 2, [(2, 1), (3040613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3040613
  · decide +kernel

theorem prime_6104353 : Nat.Prime 6104353 := by
  apply nodeValid_prime [2, 3, 63587] ⟨6104353, 5, [(2, 5), (3, 1), (63587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63587
  · decide +kernel

theorem prime_6750553 : Nat.Prime 6750553 := by
  apply nodeValid_prime [2, 3, 281273] ⟨6750553, 5, [(2, 3), (3, 1), (281273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281273
  · decide +kernel

theorem prime_7222573 : Nat.Prime 7222573 := by
  apply nodeValid_prime [2, 3, 7, 28661] ⟨7222573, 2, [(2, 2), (3, 2), (7, 1), (28661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_28661
  · decide +kernel

theorem prime_8733941 : Nat.Prime 8733941 := by
  apply nodeValid_prime [2, 5, 31, 14087] ⟨8733941, 2, [(2, 2), (5, 1), (31, 1), (14087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_14087
  · decide +kernel

theorem prime_9637777 : Nat.Prime 9637777 := by
  apply nodeValid_prime [2, 3, 17, 31, 127] ⟨9637777, 5, [(2, 4), (3, 2), (17, 1), (31, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_127
  · decide +kernel

theorem prime_10711549 : Nat.Prime 10711549 := by
  apply nodeValid_prime [2, 3, 99181] ⟨10711549, 2, [(2, 2), (3, 3), (99181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_99181
  · decide +kernel

theorem prime_23781413 : Nat.Prime 23781413 := by
  apply nodeValid_prime [2, 5945353] ⟨23781413, 2, [(2, 2), (5945353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5945353
  · decide +kernel

theorem prime_24082783 : Nat.Prime 24082783 := by
  apply nodeValid_prime [2, 3, 37, 83, 1307] ⟨24082783, 3, [(2, 1), (3, 1), (37, 1), (83, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_83
    · exact prime_1307
  · decide +kernel

theorem prime_24570277 : Nat.Prime 24570277 := by
  apply nodeValid_prime [2, 3, 2047523] ⟨24570277, 6, [(2, 2), (3, 1), (2047523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2047523
  · decide +kernel

theorem prime_26380979 : Nat.Prime 26380979 := by
  apply nodeValid_prime [2, 13, 103, 9851] ⟨26380979, 2, [(2, 1), (13, 1), (103, 1), (9851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_103
    · exact prime_9851
  · decide +kernel

theorem prime_28311901 : Nat.Prime 28311901 := by
  apply nodeValid_prime [2, 3, 5, 19, 4967] ⟨28311901, 2, [(2, 2), (3, 1), (5, 2), (19, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_4967
  · decide +kernel

theorem prime_35274251 : Nat.Prime 35274251 := by
  apply nodeValid_prime [2, 5, 11, 101, 127] ⟨35274251, 6, [(2, 1), (5, 3), (11, 1), (101, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_101
    · exact prime_127
  · decide +kernel

theorem prime_40137121 : Nat.Prime 40137121 := by
  apply nodeValid_prime [2, 3, 5, 19, 163] ⟨40137121, 7, [(2, 5), (3, 4), (5, 1), (19, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_163
  · decide +kernel

theorem prime_55610897 : Nat.Prime 55610897 := by
  apply nodeValid_prime [2, 11, 107, 2953] ⟨55610897, 3, [(2, 4), (11, 1), (107, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_107
    · exact prime_2953
  · decide +kernel

theorem prime_62053657 : Nat.Prime 62053657 := by
  apply nodeValid_prime [2, 3, 7, 431, 857] ⟨62053657, 5, [(2, 3), (3, 1), (7, 1), (431, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_431
    · exact prime_857
  · decide +kernel

theorem prime_73279559 : Nat.Prime 73279559 := by
  apply nodeValid_prime [2, 11, 3330889] ⟨73279559, 11, [(2, 1), (11, 1), (3330889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3330889
  · decide +kernel

theorem prime_84694111 : Nat.Prime 84694111 := by
  apply nodeValid_prime [2, 3, 5, 37, 41, 1861] ⟨84694111, 6, [(2, 1), (3, 1), (5, 1), (37, 1), (41, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_41
    · exact prime_1861
  · decide +kernel

theorem prime_96331133 : Nat.Prime 96331133 := by
  apply nodeValid_prime [2, 24082783] ⟨96331133, 2, [(2, 2), (24082783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24082783
  · decide +kernel

theorem prime_108679399 : Nat.Prime 108679399 := by
  apply nodeValid_prime [2, 3, 1259, 14387] ⟨108679399, 3, [(2, 1), (3, 1), (1259, 1), (14387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1259
    · exact prime_14387
  · decide +kernel

theorem prime_118372169 : Nat.Prime 118372169 := by
  apply nodeValid_prime [2, 23, 487, 1321] ⟨118372169, 3, [(2, 3), (23, 1), (487, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_487
    · exact prime_1321
  · decide +kernel

theorem prime_174556337 : Nat.Prime 174556337 := by
  apply nodeValid_prime [2, 29, 376199] ⟨174556337, 3, [(2, 4), (29, 1), (376199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_376199
  · decide +kernel

theorem prime_199643107 : Nat.Prime 199643107 := by
  apply nodeValid_prime [2, 3, 13, 599, 4273] ⟨199643107, 2, [(2, 1), (3, 1), (13, 1), (599, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_599
    · exact prime_4273
  · decide +kernel

theorem prime_221950643 : Nat.Prime 221950643 := by
  apply nodeValid_prime [2, 37, 2999333] ⟨221950643, 2, [(2, 1), (37, 1), (2999333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2999333
  · decide +kernel

theorem prime_231542083 : Nat.Prime 231542083 := by
  apply nodeValid_prime [2, 3, 127, 101287] ⟨231542083, 2, [(2, 1), (3, 2), (127, 1), (101287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_101287
  · decide +kernel

theorem prime_668429483 : Nat.Prime 668429483 := by
  apply nodeValid_prime [2, 7, 974387] ⟨668429483, 2, [(2, 1), (7, 3), (974387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_974387
  · decide +kernel

theorem prime_678580739 : Nat.Prime 678580739 := by
  apply nodeValid_prime [2, 11, 17, 439, 4133] ⟨678580739, 2, [(2, 1), (11, 1), (17, 1), (439, 1), (4133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_439
    · exact prime_4133
  · decide +kernel

theorem prime_844191329 : Nat.Prime 844191329 := by
  apply nodeValid_prime [2, 26380979] ⟨844191329, 3, [(2, 5), (26380979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26380979
  · decide +kernel

theorem prime_890995069 : Nat.Prime 890995069 := by
  apply nodeValid_prime [2, 3, 23, 331, 3251] ⟨890995069, 7, [(2, 2), (3, 2), (23, 1), (331, 1), (3251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_331
    · exact prime_3251
  · decide +kernel

theorem prime_1074029443 : Nat.Prime 1074029443 := by
  apply nodeValid_prime [2, 3, 29, 607, 10169] ⟨1074029443, 2, [(2, 1), (3, 1), (29, 1), (607, 1), (10169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_607
    · exact prime_10169
  · decide +kernel

theorem prime_2626168841 : Nat.Prime 2626168841 := by
  apply nodeValid_prime [2, 5, 17, 3862013] ⟨2626168841, 11, [(2, 3), (5, 1), (17, 1), (3862013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_3862013
  · decide +kernel

theorem prime_2840825173 : Nat.Prime 2840825173 := by
  apply nodeValid_prime [2, 3, 13109, 18059] ⟨2840825173, 2, [(2, 2), (3, 1), (13109, 1), (18059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13109
    · exact prime_18059
  · decide +kernel

theorem prime_4267524361 : Nat.Prime 4267524361 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 78853] ⟨4267524361, 46, [(2, 3), (3, 1), (5, 1), (11, 1), (41, 1), (78853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_78853
  · decide +kernel

theorem prime_6753530633 : Nat.Prime 6753530633 := by
  apply nodeValid_prime [2, 844191329] ⟨6753530633, 3, [(2, 3), (844191329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_844191329
  · decide +kernel

theorem prime_7154556067 : Nat.Prime 7154556067 := by
  apply nodeValid_prime [2, 3, 7, 151, 163, 769] ⟨7154556067, 7, [(2, 1), (3, 3), (7, 1), (151, 1), (163, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
    · exact prime_163
    · exact prime_769
  · decide +kernel

theorem prime_10465724167 : Nat.Prime 10465724167 := by
  apply nodeValid_prime [2, 3, 19417, 89833] ⟨10465724167, 3, [(2, 1), (3, 1), (19417, 1), (89833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19417
    · exact prime_89833
  · decide +kernel

theorem prime_12938281831 : Nat.Prime 12938281831 := by
  apply nodeValid_prime [2, 3, 5, 31, 1303, 3559] ⟨12938281831, 3, [(2, 1), (3, 2), (5, 1), (31, 1), (1303, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1303
    · exact prime_3559
  · decide +kernel

theorem prime_14120514307 : Nat.Prime 14120514307 := by
  apply nodeValid_prime [2, 3, 11197, 70061] ⟨14120514307, 3, [(2, 1), (3, 2), (11197, 1), (70061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11197
    · exact prime_70061
  · decide +kernel

theorem prime_16018825189 : Nat.Prime 16018825189 := by
  apply nodeValid_prime [2, 3, 1409, 947411] ⟨16018825189, 2, [(2, 2), (3, 1), (1409, 1), (947411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1409
    · exact prime_947411
  · decide +kernel

theorem prime_19670980723 : Nat.Prime 19670980723 := by
  apply nodeValid_prime [2, 3, 2719, 1205773] ⟨19670980723, 3, [(2, 1), (3, 1), (2719, 1), (1205773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2719
    · exact prime_1205773
  · decide +kernel

theorem prime_22293778183 : Nat.Prime 22293778183 := by
  apply nodeValid_prime [2, 3, 13, 47, 6081227] ⟨22293778183, 3, [(2, 1), (3, 1), (13, 1), (47, 1), (6081227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
    · exact prime_6081227
  · decide +kernel

theorem prime_24099474211 : Nat.Prime 24099474211 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 6750553] ⟨24099474211, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (6750553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_6750553
  · decide +kernel

theorem prime_34392409721 : Nat.Prime 34392409721 := by
  apply nodeValid_prime [2, 5, 197, 4364519] ⟨34392409721, 3, [(2, 3), (5, 1), (197, 1), (4364519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
    · exact prime_4364519
  · decide +kernel

theorem prime_34392411503 : Nat.Prime 34392411503 := by
  apply nodeValid_prime [2, 71, 1543, 156967] ⟨34392411503, 5, [(2, 1), (71, 1), (1543, 1), (156967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1543
    · exact prime_156967
  · decide +kernel

theorem prime_48341707649 : Nat.Prime 48341707649 := by
  apply nodeValid_prime [2, 13, 23, 1263109] ⟨48341707649, 3, [(2, 7), (13, 1), (23, 1), (1263109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_1263109
  · decide +kernel

theorem prime_56398658893 : Nat.Prime 56398658893 := by
  apply nodeValid_prime [2, 3, 19, 23, 566047] ⟨56398658893, 2, [(2, 2), (3, 1), (19, 2), (23, 1), (566047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_566047
  · decide +kernel

theorem prime_171709345609 : Nat.Prime 171709345609 := by
  apply nodeValid_prime [2, 3, 7154556067] ⟨171709345609, 19, [(2, 3), (3, 1), (7154556067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7154556067
  · decide +kernel

theorem prime_339393303989 : Nat.Prime 339393303989 := by
  apply nodeValid_prime [2, 79, 1074029443] ⟨339393303989, 2, [(2, 2), (79, 1), (1074029443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1074029443
  · decide +kernel

theorem prime_342913744913 : Nat.Prime 342913744913 := by
  apply nodeValid_prime [2, 757, 28311901] ⟨342913744913, 3, [(2, 4), (757, 1), (28311901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_757
    · exact prime_28311901
  · decide +kernel

theorem prime_667821596401 : Nat.Prime 667821596401 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 205433] ⟨667821596401, 39, [(2, 4), (3, 3), (5, 2), (7, 1), (43, 1), (205433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_205433
  · decide +kernel

theorem prime_667821613163 : Nat.Prime 667821613163 := by
  apply nodeValid_prime [2, 11, 211, 317, 453833] ⟨667821613163, 5, [(2, 1), (11, 1), (211, 1), (317, 1), (453833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_211
    · exact prime_317
    · exact prime_453833
  · decide +kernel

theorem prime_667821613817 : Nat.Prime 667821613817 := by
  apply nodeValid_prime [2, 7, 8297, 1437313] ⟨667821613817, 3, [(2, 3), (7, 1), (8297, 1), (1437313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8297
    · exact prime_1437313
  · decide +kernel

theorem prime_668813344583 : Nat.Prime 668813344583 := by
  apply nodeValid_prime [2, 17, 19670980723] ⟨668813344583, 5, [(2, 1), (17, 1), (19670980723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19670980723
  · decide +kernel

theorem prime_668813345491 : Nat.Prime 668813345491 := by
  apply nodeValid_prime [2, 3, 5, 22293778183] ⟨668813345491, 2, [(2, 1), (3, 1), (5, 1), (22293778183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22293778183
  · decide +kernel

theorem prime_668813414543 : Nat.Prime 668813414543 := by
  apply nodeValid_prime [2, 7, 13, 15217, 34499] ⟨668813414543, 5, [(2, 1), (7, 2), (13, 1), (15217, 1), (34499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_15217
    · exact prime_34499
  · decide +kernel

theorem prime_669806225947 : Nat.Prime 669806225947 := by
  apply nodeValid_prime [2, 3, 11, 13, 9637777] ⟨669806225947, 3, [(2, 1), (3, 5), (11, 1), (13, 1), (9637777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_9637777
  · decide +kernel

theorem prime_669806346689 : Nat.Prime 669806346689 := by
  apply nodeValid_prime [2, 10465724167] ⟨669806346689, 3, [(2, 6), (10465724167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10465724167
  · decide +kernel

theorem prime_669806347451 : Nat.Prime 669806347451 := by
  apply nodeValid_prime [2, 5, 241, 733, 75833] ⟨669806347451, 2, [(2, 1), (5, 2), (241, 1), (733, 1), (75833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_241
    · exact prime_733
    · exact prime_75833
  · decide +kernel

theorem prime_670800032171 : Nat.Prime 670800032171 := by
  apply nodeValid_prime [2, 5, 23, 47, 62053657] ⟨670800032171, 6, [(2, 1), (5, 1), (23, 1), (47, 1), (62053657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_47
    · exact prime_62053657
  · decide +kernel

theorem prime_670800034049 : Nat.Prime 670800034049 := by
  apply nodeValid_prime [2, 53, 257, 192373] ⟨670800034049, 3, [(2, 8), (53, 1), (257, 1), (192373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_257
    · exact prime_192373
  · decide +kernel

theorem prime_670800034301 : Nat.Prime 670800034301 := by
  apply nodeValid_prime [2, 5, 11, 313, 1948301] ⟨670800034301, 2, [(2, 2), (5, 2), (11, 1), (313, 1), (1948301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_313
    · exact prime_1948301
  · decide +kernel

theorem prime_671794840879 : Nat.Prime 671794840879 := by
  apply nodeValid_prime [2, 3, 7, 821, 2129, 9151] ⟨671794840879, 6, [(2, 1), (3, 1), (7, 1), (821, 1), (2129, 1), (9151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_821
    · exact prime_2129
    · exact prime_9151
  · decide +kernel

theorem prime_671794930921 : Nat.Prime 671794930921 := by
  apply nodeValid_prime [2, 3, 5, 619, 977, 9257] ⟨671794930921, 17, [(2, 3), (3, 1), (5, 1), (619, 1), (977, 1), (9257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_619
    · exact prime_977
    · exact prime_9257
  · decide +kernel

theorem prime_671794931611 : Nat.Prime 671794931611 := by
  apply nodeValid_prime [2, 3, 5, 11, 678580739] ⟨671794931611, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (678580739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_678580739
  · decide +kernel

theorem prime_672790654871 : Nat.Prime 672790654871 := by
  apply nodeValid_prime [2, 5, 13219, 5089573] ⟨672790654871, 11, [(2, 1), (5, 1), (13219, 1), (5089573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13219
    · exact prime_5089573
  · decide +kernel

theorem prime_672790655213 : Nat.Prime 672790655213 := by
  apply nodeValid_prime [2, 13, 12938281831] ⟨672790655213, 2, [(2, 2), (13, 1), (12938281831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_12938281831
  · decide +kernel

theorem prime_672790657939 : Nat.Prime 672790657939 := by
  apply nodeValid_prime [2, 3, 7, 16018825189] ⟨672790657939, 2, [(2, 1), (3, 1), (7, 1), (16018825189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_16018825189
  · decide +kernel

theorem prime_673787460821 : Nat.Prime 673787460821 := by
  apply nodeValid_prime [2, 5, 193, 174556337] ⟨673787460821, 3, [(2, 2), (5, 1), (193, 1), (174556337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
    · exact prime_174556337
  · decide +kernel

theorem prime_673787461531 : Nat.Prime 673787461531 := by
  apply nodeValid_prime [2, 3, 5, 97, 231542083] ⟨673787461531, 2, [(2, 1), (3, 1), (5, 1), (97, 1), (231542083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_231542083
  · decide +kernel

theorem prime_673787473637 : Nat.Prime 673787473637 := by
  apply nodeValid_prime [2, 142111, 1185319] ⟨673787473637, 2, [(2, 2), (142111, 1), (1185319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_142111
    · exact prime_1185319
  · decide +kernel

theorem prime_674785277909 : Nat.Prime 674785277909 := by
  apply nodeValid_prime [2, 7, 24099474211] ⟨674785277909, 2, [(2, 2), (7, 1), (24099474211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_24099474211
  · decide +kernel

theorem prime_674785278253 : Nat.Prime 674785278253 := by
  apply nodeValid_prime [2, 3, 467, 40137121] ⟨674785278253, 2, [(2, 2), (3, 2), (467, 1), (40137121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_40137121
  · decide +kernel

theorem prime_674785287041 : Nat.Prime 674785287041 := by
  apply nodeValid_prime [2, 5, 967, 1090333] ⟨674785287041, 3, [(2, 7), (5, 1), (967, 1), (1090333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_967
    · exact prime_1090333
  · decide +kernel

theorem prime_675784093099 : Nat.Prime 675784093099 := by
  apply nodeValid_prime [2, 3, 29, 53, 73279559] ⟨675784093099, 3, [(2, 1), (3, 1), (29, 1), (53, 1), (73279559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_53
    · exact prime_73279559
  · decide +kernel

theorem prime_675784099621 : Nat.Prime 675784099621 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 4597, 6863] ⟨675784099621, 10, [(2, 2), (3, 2), (5, 1), (7, 1), (17, 1), (4597, 1), (6863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_4597
    · exact prime_6863
  · decide +kernel

theorem prime_675784100659 : Nat.Prime 675784100659 := by
  apply nodeValid_prime [2, 3, 31, 103, 35274251] ⟨675784100659, 2, [(2, 1), (3, 1), (31, 1), (103, 1), (35274251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_103
    · exact prime_35274251
  · decide +kernel

theorem prime_676783905601 : Nat.Prime 676783905601 := by
  apply nodeValid_prime [2, 3, 5, 11, 23, 181, 3079] ⟨676783905601, 21, [(2, 6), (3, 1), (5, 2), (11, 1), (23, 1), (181, 1), (3079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_181
    · exact prime_3079
  · decide +kernel

theorem prime_676783906717 : Nat.Prime 676783906717 := by
  apply nodeValid_prime [2, 3, 56398658893] ⟨676783906717, 2, [(2, 2), (3, 1), (56398658893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56398658893
  · decide +kernel

theorem prime_676783907087 : Nat.Prime 676783907087 := by
  apply nodeValid_prime [2, 7, 48341707649] ⟨676783907087, 5, [(2, 1), (7, 1), (48341707649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_48341707649
  · decide +kernel

theorem prime_677784684427 : Nat.Prime 677784684427 := by
  apply nodeValid_prime [2, 3, 109, 661, 691, 2269] ⟨677784684427, 2, [(2, 1), (3, 1), (109, 1), (661, 1), (691, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_661
    · exact prime_691
    · exact prime_2269
  · decide +kernel

theorem prime_677784686737 : Nat.Prime 677784686737 := by
  apply nodeValid_prime [2, 3, 14120514307] ⟨677784686737, 5, [(2, 4), (3, 1), (14120514307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14120514307
  · decide +kernel

theorem prime_677784732049 : Nat.Prime 677784732049 := by
  apply nodeValid_prime [2, 3, 29, 41, 227, 5813] ⟨677784732049, 7, [(2, 4), (3, 3), (29, 1), (41, 1), (227, 1), (5813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_41
    · exact prime_227
    · exact prime_5813
  · decide +kernel

theorem prime_678786563801 : Nat.Prime 678786563801 := by
  apply nodeValid_prime [2, 5, 17, 199643107] ⟨678786563801, 3, [(2, 3), (5, 2), (17, 1), (199643107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_199643107
  · decide +kernel

theorem prime_678786607979 : Nat.Prime 678786607979 := by
  apply nodeValid_prime [2, 339393303989] ⟨678786607979, 2, [(2, 1), (339393303989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_339393303989
  · decide +kernel

theorem prime_678786608783 : Nat.Prime 678786608783 := by
  apply nodeValid_prime [2, 17, 359, 55610897] ⟨678786608783, 5, [(2, 1), (17, 1), (359, 1), (55610897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_359
    · exact prime_55610897
  · decide +kernel

theorem prime_679789399979 : Nat.Prime 679789399979 := by
  apply nodeValid_prime [2, 13, 94573, 276461] ⟨679789399979, 2, [(2, 1), (13, 1), (94573, 1), (276461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_94573
    · exact prime_276461
  · decide +kernel

theorem prime_679789422017 : Nat.Prime 679789422017 := by
  apply nodeValid_prime [2, 4231, 2510449] ⟨679789422017, 3, [(2, 6), (4231, 1), (2510449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4231
    · exact prime_2510449
  · decide +kernel

theorem prime_679789422449 : Nat.Prime 679789422449 := by
  apply nodeValid_prime [2, 43, 167, 487, 12149] ⟨679789422449, 3, [(2, 4), (43, 1), (167, 1), (487, 1), (12149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_167
    · exact prime_487
    · exact prime_12149
  · decide +kernel

theorem prime_680793232643 : Nat.Prime 680793232643 := by
  apply nodeValid_prime [2, 491, 601, 1153531] ⟨680793232643, 2, [(2, 1), (491, 1), (601, 1), (1153531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_601
    · exact prime_1153531
  · decide +kernel

theorem prime_680793233069 : Nat.Prime 680793233069 := by
  apply nodeValid_prime [2, 13, 1499, 8733941] ⟨680793233069, 3, [(2, 2), (13, 1), (1499, 1), (8733941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1499
    · exact prime_8733941
  · decide +kernel

theorem prime_680793235117 : Nat.Prime 680793235117 := by
  apply nodeValid_prime [2, 3, 2309, 24570277] ⟨680793235117, 2, [(2, 2), (3, 1), (2309, 1), (24570277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2309
    · exact prime_24570277
  · decide +kernel

theorem prime_681798041051 : Nat.Prime 681798041051 := by
  apply nodeValid_prime [2, 5, 7, 79, 233, 105829] ⟨681798041051, 6, [(2, 1), (5, 2), (7, 1), (79, 1), (233, 1), (105829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
    · exact prime_233
    · exact prime_105829
  · decide +kernel

theorem prime_681798041521 : Nat.Prime 681798041521 := by
  apply nodeValid_prime [2, 3, 5, 2840825173] ⟨681798041521, 31, [(2, 4), (3, 1), (5, 1), (2840825173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2840825173
  · decide +kernel

theorem prime_681798072661 : Nat.Prime 681798072661 := by
  apply nodeValid_prime [2, 3, 5, 17, 668429483] ⟨681798072661, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (668429483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_668429483
  · decide +kernel

theorem prime_682803897761 : Nat.Prime 682803897761 := by
  apply nodeValid_prime [2, 5, 4267524361] ⟨682803897761, 3, [(2, 5), (5, 1), (4267524361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4267524361
  · decide +kernel

theorem prime_682803898661 : Nat.Prime 682803898661 := by
  apply nodeValid_prime [2, 5, 13, 2626168841] ⟨682803898661, 2, [(2, 2), (5, 1), (13, 1), (2626168841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2626168841
  · decide +kernel

theorem prime_682803922883 : Nat.Prime 682803922883 := by
  apply nodeValid_prime [2, 29, 139, 84694111] ⟨682803922883, 2, [(2, 1), (29, 1), (139, 1), (84694111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_139
    · exact prime_84694111
  · decide +kernel

theorem prime_683810749403 : Nat.Prime 683810749403 := by
  apply nodeValid_prime [2, 11, 1307, 23781413] ⟨683810749403, 2, [(2, 1), (11, 1), (1307, 1), (23781413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1307
    · exact prime_23781413
  · decide +kernel

theorem prime_683810749411 : Nat.Prime 683810749411 := by
  apply nodeValid_prime [2, 3, 5, 17, 1663, 806257] ⟨683810749411, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (1663, 1), (806257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1663
    · exact prime_806257
  · decide +kernel

theorem prime_683810778509 : Nat.Prime 683810778509 := by
  apply nodeValid_prime [2, 11, 13, 108679399] ⟨683810778509, 2, [(2, 2), (11, 2), (13, 1), (108679399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_108679399
  · decide +kernel

theorem prime_684818617073 : Nat.Prime 684818617073 := by
  apply nodeValid_prime [2, 113, 1867, 202877] ⟨684818617073, 3, [(2, 4), (113, 1), (1867, 1), (202877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_1867
    · exact prime_202877
  · decide +kernel

theorem prime_684818618111 : Nat.Prime 684818618111 := by
  apply nodeValid_prime [2, 5, 11, 1289, 4829809] ⟨684818618111, 23, [(2, 1), (5, 1), (11, 1), (1289, 1), (4829809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1289
    · exact prime_4829809
  · decide +kernel

theorem prime_684818631097 : Nat.Prime 684818631097 := by
  apply nodeValid_prime [2, 3, 17, 61, 631, 43607] ⟨684818631097, 5, [(2, 3), (3, 1), (17, 1), (61, 1), (631, 1), (43607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_631
    · exact prime_43607
  · decide +kernel

theorem prime_685827486871 : Nat.Prime 685827486871 := by
  apply nodeValid_prime [2, 3, 5, 103, 221950643] ⟨685827486871, 12, [(2, 1), (3, 1), (5, 1), (103, 1), (221950643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_221950643
  · decide +kernel

theorem prime_685827489827 : Nat.Prime 685827489827 := by
  apply nodeValid_prime [2, 342913744913] ⟨685827489827, 2, [(2, 1), (342913744913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_342913744913
  · decide +kernel

theorem prime_685827490441 : Nat.Prime 685827490441 := by
  apply nodeValid_prime [2, 3, 5, 37, 251, 615401] ⟨685827490441, 17, [(2, 3), (3, 1), (5, 1), (37, 1), (251, 1), (615401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_251
    · exact prime_615401
  · decide +kernel

theorem prime_686837353819 : Nat.Prime 686837353819 := by
  apply nodeValid_prime [2, 3, 7, 11, 277, 653, 8219] ⟨686837353819, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (277, 1), (653, 1), (8219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_277
    · exact prime_653
    · exact prime_8219
  · decide +kernel

theorem prime_686837382149 : Nat.Prime 686837382149 := by
  apply nodeValid_prime [2, 23, 1223, 6104353] ⟨686837382149, 2, [(2, 2), (23, 1), (1223, 1), (6104353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1223
    · exact prime_6104353
  · decide +kernel

theorem prime_686837382437 : Nat.Prime 686837382437 := by
  apply nodeValid_prime [2, 171709345609] ⟨686837382437, 2, [(2, 2), (171709345609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_171709345609
  · decide +kernel

theorem prime_687848193269 : Nat.Prime 687848193269 := by
  apply nodeValid_prime [2, 193, 890995069] ⟨687848193269, 2, [(2, 2), (193, 1), (890995069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_890995069
  · decide +kernel

theorem prime_687848194421 : Nat.Prime 687848194421 := by
  apply nodeValid_prime [2, 5, 34392409721] ⟨687848194421, 2, [(2, 2), (5, 1), (34392409721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_34392409721
  · decide +kernel

theorem prime_687848230061 : Nat.Prime 687848230061 := by
  apply nodeValid_prime [2, 5, 34392411503] ⟨687848230061, 2, [(2, 2), (5, 1), (34392411503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_34392411503
  · decide +kernel

theorem prime_688860113947 : Nat.Prime 688860113947 := by
  apply nodeValid_prime [2, 3, 67, 71, 353, 68371] ⟨688860113947, 3, [(2, 1), (3, 1), (67, 1), (71, 1), (353, 1), (68371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_71
    · exact prime_353
    · exact prime_68371
  · decide +kernel

theorem prime_688860122449 : Nat.Prime 688860122449 := by
  apply nodeValid_prime [2, 3, 1987, 7222573] ⟨688860122449, 13, [(2, 4), (3, 1), (1987, 1), (7222573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1987
    · exact prime_7222573
  · decide +kernel

theorem prime_688860124567 : Nat.Prime 688860124567 := by
  apply nodeValid_prime [2, 3, 17, 6753530633] ⟨688860124567, 5, [(2, 1), (3, 1), (17, 1), (6753530633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_6753530633
  · decide +kernel

theorem prime_689873000933 : Nat.Prime 689873000933 := by
  apply nodeValid_prime [2, 31, 47, 118372169] ⟨689873000933, 2, [(2, 2), (31, 1), (47, 1), (118372169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_47
    · exact prime_118372169
  · decide +kernel

theorem prime_689873001577 : Nat.Prime 689873001577 := by
  apply nodeValid_prime [2, 3, 11, 6397, 408497] ⟨689873001577, 10, [(2, 3), (3, 1), (11, 1), (6397, 1), (408497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6397
    · exact prime_408497
  · decide +kernel

theorem prime_689873008157 : Nat.Prime 689873008157 := by
  apply nodeValid_prime [2, 53, 1889, 1722667] ⟨689873008157, 2, [(2, 2), (53, 1), (1889, 1), (1722667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1889
    · exact prime_1722667
  · decide +kernel

theorem prime_690886885751 : Nat.Prime 690886885751 := by
  apply nodeValid_prime [2, 5, 23, 139, 864419] ⟨690886885751, 17, [(2, 1), (5, 3), (23, 1), (139, 1), (864419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_139
    · exact prime_864419
  · decide +kernel

theorem prime_690886885877 : Nat.Prime 690886885877 := by
  apply nodeValid_prime [2, 11, 163, 96331133] ⟨690886885877, 2, [(2, 2), (11, 1), (163, 1), (96331133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_163
    · exact prime_96331133
  · decide +kernel

theorem prime_690886907309 : Nat.Prime 690886907309 := by
  apply nodeValid_prime [2, 13, 281, 719, 65761] ⟨690886907309, 2, [(2, 2), (13, 1), (281, 1), (719, 1), (65761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_281
    · exact prime_719
    · exact prime_65761
  · decide +kernel

theorem prime_691901791289 : Nat.Prime 691901791289 := by
  apply nodeValid_prime [2, 19, 2789, 1632121] ⟨691901791289, 3, [(2, 3), (19, 1), (2789, 1), (1632121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2789
    · exact prime_1632121
  · decide +kernel

theorem prime_691901796107 : Nat.Prime 691901796107 := by
  apply nodeValid_prime [2, 32297, 10711549] ⟨691901796107, 2, [(2, 1), (32297, 1), (10711549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32297
    · exact prime_10711549
  · decide +kernel

theorem prime_691901810129 : Nat.Prime 691901810129 := by
  apply nodeValid_prime [2, 10313, 4193141] ⟨691901810129, 3, [(2, 4), (10313, 1), (4193141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10313
    · exact prime_4193141
  · decide +kernel

end Sude.Lucas.Generated
