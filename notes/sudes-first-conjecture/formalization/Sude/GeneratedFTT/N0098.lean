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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0084
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0094

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_8963 : Nat.Prime 8963 := by
  apply nodeValid_prime [2, 4481] ⟨8963, 2, [(2, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4481
  · decide +kernel

theorem prime_11117 : Nat.Prime 11117 := by
  apply nodeValid_prime [2, 7, 397] ⟨11117, 3, [(2, 2), (7, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_397
  · decide +kernel

theorem prime_14869 : Nat.Prime 14869 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨14869, 2, [(2, 2), (3, 2), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_15767 : Nat.Prime 15767 := by
  apply nodeValid_prime [2, 7883] ⟨15767, 5, [(2, 1), (7883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7883
  · decide +kernel

theorem prime_19141 : Nat.Prime 19141 := by
  apply nodeValid_prime [2, 3, 5, 11, 29] ⟨19141, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_20201 : Nat.Prime 20201 := by
  apply nodeValid_prime [2, 5, 101] ⟨20201, 6, [(2, 3), (5, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_26669 : Nat.Prime 26669 := by
  apply nodeValid_prime [2, 59, 113] ⟨26669, 2, [(2, 2), (59, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_113
  · decide +kernel

theorem prime_50417 : Nat.Prime 50417 := by
  apply nodeValid_prime [2, 23, 137] ⟨50417, 3, [(2, 4), (23, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_137
  · decide +kernel

theorem prime_50671 : Nat.Prime 50671 := by
  apply nodeValid_prime [2, 3, 5, 563] ⟨50671, 11, [(2, 1), (3, 2), (5, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_563
  · decide +kernel

theorem prime_53231 : Nat.Prime 53231 := by
  apply nodeValid_prime [2, 5, 5323] ⟨53231, 23, [(2, 1), (5, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5323
  · decide +kernel

theorem prime_54403 : Nat.Prime 54403 := by
  apply nodeValid_prime [2, 3, 9067] ⟨54403, 2, [(2, 1), (3, 1), (9067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9067
  · decide +kernel

theorem prime_73699 : Nat.Prime 73699 := by
  apply nodeValid_prime [2, 3, 71, 173] ⟨73699, 2, [(2, 1), (3, 1), (71, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_173
  · decide +kernel

theorem prime_88937 : Nat.Prime 88937 := by
  apply nodeValid_prime [2, 11117] ⟨88937, 3, [(2, 3), (11117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11117
  · decide +kernel

theorem prime_92317 : Nat.Prime 92317 := by
  apply nodeValid_prime [2, 3, 7, 157] ⟨92317, 6, [(2, 2), (3, 1), (7, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
  · decide +kernel

theorem prime_103567 : Nat.Prime 103567 := by
  apply nodeValid_prime [2, 3, 41, 421] ⟨103567, 7, [(2, 1), (3, 1), (41, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_421
  · decide +kernel

theorem prime_122611 : Nat.Prime 122611 := by
  apply nodeValid_prime [2, 3, 5, 61, 67] ⟨122611, 12, [(2, 1), (3, 1), (5, 1), (61, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_67
  · decide +kernel

theorem prime_125303 : Nat.Prime 125303 := by
  apply nodeValid_prime [2, 31, 43, 47] ⟨125303, 5, [(2, 1), (31, 1), (43, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_47
  · decide +kernel

theorem prime_133183 : Nat.Prime 133183 := by
  apply nodeValid_prime [2, 3, 7, 151] ⟨133183, 5, [(2, 1), (3, 2), (7, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
  · decide +kernel

theorem prime_136429 : Nat.Prime 136429 := by
  apply nodeValid_prime [2, 3, 11369] ⟨136429, 2, [(2, 2), (3, 1), (11369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11369
  · decide +kernel

theorem prime_143827 : Nat.Prime 143827 := by
  apply nodeValid_prime [2, 3, 23971] ⟨143827, 2, [(2, 1), (3, 1), (23971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23971
  · decide +kernel

theorem prime_165877 : Nat.Prime 165877 := by
  apply nodeValid_prime [2, 3, 23, 601] ⟨165877, 2, [(2, 2), (3, 1), (23, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_601
  · decide +kernel

theorem prime_167953 : Nat.Prime 167953 := by
  apply nodeValid_prime [2, 3, 3499] ⟨167953, 5, [(2, 4), (3, 1), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3499
  · decide +kernel

theorem prime_210761 : Nat.Prime 210761 := by
  apply nodeValid_prime [2, 5, 11, 479] ⟨210761, 3, [(2, 3), (5, 1), (11, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_479
  · decide +kernel

theorem prime_216211 : Nat.Prime 216211 := by
  apply nodeValid_prime [2, 3, 5, 7207] ⟨216211, 10, [(2, 1), (3, 1), (5, 1), (7207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7207
  · decide +kernel

theorem prime_239873 : Nat.Prime 239873 := by
  apply nodeValid_prime [2, 937] ⟨239873, 3, [(2, 8), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_937
  · decide +kernel

theorem prime_248827 : Nat.Prime 248827 := by
  apply nodeValid_prime [2, 3, 113, 367] ⟨248827, 2, [(2, 1), (3, 1), (113, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_367
  · decide +kernel

theorem prime_290107 : Nat.Prime 290107 := by
  apply nodeValid_prime [2, 3, 71, 227] ⟨290107, 2, [(2, 1), (3, 2), (71, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_227
  · decide +kernel

theorem prime_311371 : Nat.Prime 311371 := by
  apply nodeValid_prime [2, 3, 5, 97, 107] ⟨311371, 2, [(2, 1), (3, 1), (5, 1), (97, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_107
  · decide +kernel

theorem prime_321193 : Nat.Prime 321193 := by
  apply nodeValid_prime [2, 3, 1487] ⟨321193, 5, [(2, 3), (3, 3), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1487
  · decide +kernel

theorem prime_346261 : Nat.Prime 346261 := by
  apply nodeValid_prime [2, 3, 5, 29, 199] ⟨346261, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_199
  · decide +kernel

theorem prime_353021 : Nat.Prime 353021 := by
  apply nodeValid_prime [2, 5, 19, 929] ⟨353021, 2, [(2, 2), (5, 1), (19, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_929
  · decide +kernel

theorem prime_366461 : Nat.Prime 366461 := by
  apply nodeValid_prime [2, 5, 73, 251] ⟨366461, 2, [(2, 2), (5, 1), (73, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_251
  · decide +kernel

theorem prime_402541 : Nat.Prime 402541 := by
  apply nodeValid_prime [2, 3, 5, 6709] ⟨402541, 2, [(2, 2), (3, 1), (5, 1), (6709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6709
  · decide +kernel

theorem prime_412343 : Nat.Prime 412343 := by
  apply nodeValid_prime [2, 7, 29453] ⟨412343, 5, [(2, 1), (7, 1), (29453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29453
  · decide +kernel

theorem prime_536461 : Nat.Prime 536461 := by
  apply nodeValid_prime [2, 3, 5, 8941] ⟨536461, 2, [(2, 2), (3, 1), (5, 1), (8941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8941
  · decide +kernel

theorem prime_566413 : Nat.Prime 566413 := by
  apply nodeValid_prime [2, 3, 7, 11, 613] ⟨566413, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_613
  · decide +kernel

theorem prime_674123 : Nat.Prime 674123 := by
  apply nodeValid_prime [2, 41, 8221] ⟨674123, 2, [(2, 1), (41, 1), (8221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_8221
  · decide +kernel

theorem prime_739633 : Nat.Prime 739633 := by
  apply nodeValid_prime [2, 3, 19, 811] ⟨739633, 15, [(2, 4), (3, 1), (19, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_811
  · decide +kernel

theorem prime_752527 : Nat.Prime 752527 := by
  apply nodeValid_prime [2, 3, 97, 431] ⟨752527, 3, [(2, 1), (3, 2), (97, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_431
  · decide +kernel

theorem prime_970603 : Nat.Prime 970603 := by
  apply nodeValid_prime [2, 3, 83, 1949] ⟨970603, 2, [(2, 1), (3, 1), (83, 1), (1949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_1949
  · decide +kernel

theorem prime_972833 : Nat.Prime 972833 := by
  apply nodeValid_prime [2, 7, 43, 101] ⟨972833, 3, [(2, 5), (7, 1), (43, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_101
  · decide +kernel

theorem prime_1160429 : Nat.Prime 1160429 := by
  apply nodeValid_prime [2, 290107] ⟨1160429, 2, [(2, 2), (290107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_290107
  · decide +kernel

theorem prime_1184429 : Nat.Prime 1184429 := by
  apply nodeValid_prime [2, 7, 6043] ⟨1184429, 10, [(2, 2), (7, 2), (6043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6043
  · decide +kernel

theorem prime_1263307 : Nat.Prime 1263307 := by
  apply nodeValid_prime [2, 3, 11, 19141] ⟨1263307, 2, [(2, 1), (3, 1), (11, 1), (19141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19141
  · decide +kernel

theorem prime_1345453 : Nat.Prime 1345453 := by
  apply nodeValid_prime [2, 3, 112121] ⟨1345453, 6, [(2, 2), (3, 1), (112121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_112121
  · decide +kernel

theorem prime_1438271 : Nat.Prime 1438271 := by
  apply nodeValid_prime [2, 5, 143827] ⟨1438271, 14, [(2, 1), (5, 1), (143827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_143827
  · decide +kernel

theorem prime_1443223 : Nat.Prime 1443223 := by
  apply nodeValid_prime [2, 3, 11, 37, 197] ⟨1443223, 5, [(2, 1), (3, 2), (11, 1), (37, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_197
  · decide +kernel

theorem prime_1603339 : Nat.Prime 1603339 := by
  apply nodeValid_prime [2, 3, 11, 17, 1429] ⟨1603339, 2, [(2, 1), (3, 1), (11, 1), (17, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_1429
  · decide +kernel

theorem prime_2398051 : Nat.Prime 2398051 := by
  apply nodeValid_prime [2, 3, 5, 73] ⟨2398051, 15, [(2, 1), (3, 2), (5, 2), (73, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_2460791 : Nat.Prime 2460791 := by
  apply nodeValid_prime [2, 5, 53, 4643] ⟨2460791, 7, [(2, 1), (5, 1), (53, 1), (4643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_4643
  · decide +kernel

theorem prime_2477051 : Nat.Prime 2477051 := by
  apply nodeValid_prime [2, 5, 107, 463] ⟨2477051, 2, [(2, 1), (5, 2), (107, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_463
  · decide +kernel

theorem prime_3350261 : Nat.Prime 3350261 := by
  apply nodeValid_prime [2, 5, 127, 1319] ⟨3350261, 2, [(2, 2), (5, 1), (127, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_1319
  · decide +kernel

theorem prime_3497243 : Nat.Prime 3497243 := by
  apply nodeValid_prime [2, 7, 23, 10861] ⟨3497243, 2, [(2, 1), (7, 1), (23, 1), (10861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_10861
  · decide +kernel

theorem prime_3692681 : Nat.Prime 3692681 := by
  apply nodeValid_prime [2, 5, 92317] ⟨3692681, 3, [(2, 3), (5, 1), (92317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_92317
  · decide +kernel

theorem prime_3946727 : Nat.Prime 3946727 := by
  apply nodeValid_prime [2, 7, 29, 9721] ⟨3946727, 5, [(2, 1), (7, 1), (29, 1), (9721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_9721
  · decide +kernel

theorem prime_3964651 : Nat.Prime 3964651 := by
  apply nodeValid_prime [2, 3, 5, 26431] ⟨3964651, 2, [(2, 1), (3, 1), (5, 2), (26431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_26431
  · decide +kernel

theorem prime_4849261 : Nat.Prime 4849261 := by
  apply nodeValid_prime [2, 3, 5, 13, 6217] ⟨4849261, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (6217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_6217
  · decide +kernel

theorem prime_4921583 : Nat.Prime 4921583 := by
  apply nodeValid_prime [2, 2460791] ⟨4921583, 5, [(2, 1), (2460791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2460791
  · decide +kernel

theorem prime_6320563 : Nat.Prime 6320563 := by
  apply nodeValid_prime [2, 3, 37, 71, 401] ⟨6320563, 2, [(2, 1), (3, 1), (37, 1), (71, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_401
  · decide +kernel

theorem prime_6596299 : Nat.Prime 6596299 := by
  apply nodeValid_prime [2, 3, 366461] ⟨6596299, 3, [(2, 1), (3, 2), (366461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_366461
  · decide +kernel

theorem prime_6877219 : Nat.Prime 6877219 := by
  apply nodeValid_prime [2, 3, 499, 2297] ⟨6877219, 13, [(2, 1), (3, 1), (499, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_499
    · exact prime_2297
  · decide +kernel

theorem prime_7245739 : Nat.Prime 7245739 := by
  apply nodeValid_prime [2, 3, 402541] ⟨7245739, 7, [(2, 1), (3, 2), (402541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_402541
  · decide +kernel

theorem prime_7778237 : Nat.Prime 7778237 := by
  apply nodeValid_prime [2, 97, 20047] ⟨7778237, 2, [(2, 2), (97, 1), (20047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_20047
  · decide +kernel

theorem prime_8268389 : Nat.Prime 8268389 := by
  apply nodeValid_prime [2, 41, 50417] ⟨8268389, 2, [(2, 2), (41, 1), (50417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_50417
  · decide +kernel

theorem prime_9267149 : Nat.Prime 9267149 := by
  apply nodeValid_prime [2, 11, 41, 467] ⟨9267149, 2, [(2, 2), (11, 2), (41, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_467
  · decide +kernel

theorem prime_11834129 : Nat.Prime 11834129 := by
  apply nodeValid_prime [2, 739633] ⟨11834129, 3, [(2, 4), (739633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_739633
  · decide +kernel

theorem prime_20223691 : Nat.Prime 20223691 := by
  apply nodeValid_prime [2, 3, 5, 674123] ⟨20223691, 2, [(2, 1), (3, 1), (5, 1), (674123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_674123
  · decide +kernel

theorem prime_22193419 : Nat.Prime 22193419 := by
  apply nodeValid_prime [2, 3, 13, 43, 509] ⟨22193419, 2, [(2, 1), (3, 1), (13, 2), (43, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_509
  · decide +kernel

theorem prime_24505673 : Nat.Prime 24505673 := by
  apply nodeValid_prime [2, 23, 133183] ⟨24505673, 3, [(2, 3), (23, 1), (133183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_133183
  · decide +kernel

theorem prime_25282253 : Nat.Prime 25282253 := by
  apply nodeValid_prime [2, 6320563] ⟨25282253, 2, [(2, 2), (6320563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6320563
  · decide +kernel

theorem prime_26112169 : Nat.Prime 26112169 := by
  apply nodeValid_prime [2, 3, 31, 11699] ⟨26112169, 7, [(2, 3), (3, 2), (31, 1), (11699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_11699
  · decide +kernel

theorem prime_26965291 : Nat.Prime 26965291 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 1993] ⟨26965291, 10, [(2, 1), (3, 1), (5, 1), (11, 1), (41, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_1993
  · decide +kernel

theorem prime_34635431 : Nat.Prime 34635431 := by
  apply nodeValid_prime [2, 5, 1289, 2687] ⟨34635431, 17, [(2, 1), (5, 1), (1289, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1289
    · exact prime_2687
  · decide +kernel

theorem prime_39646511 : Nat.Prime 39646511 := by
  apply nodeValid_prime [2, 5, 3964651] ⟨39646511, 7, [(2, 1), (5, 1), (3964651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3964651
  · decide +kernel

theorem prime_49541021 : Nat.Prime 49541021 := by
  apply nodeValid_prime [2, 5, 2477051] ⟨49541021, 2, [(2, 2), (5, 1), (2477051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2477051
  · decide +kernel

theorem prime_51058877 : Nat.Prime 51058877 := by
  apply nodeValid_prime [2, 11, 1160429] ⟨51058877, 2, [(2, 2), (11, 1), (1160429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1160429
  · decide +kernel

theorem prime_52721587 : Nat.Prime 52721587 := by
  apply nodeValid_prime [2, 3, 179, 16363] ⟨52721587, 3, [(2, 1), (3, 2), (179, 1), (16363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_16363
  · decide +kernel

theorem prime_63263251 : Nat.Prime 63263251 := by
  apply nodeValid_prime [2, 3, 5, 31, 907] ⟨63263251, 2, [(2, 1), (3, 2), (5, 3), (31, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_907
  · decide +kernel

theorem prime_63649823 : Nat.Prime 63649823 := by
  apply nodeValid_prime [2, 151, 210761] ⟨63649823, 5, [(2, 1), (151, 1), (210761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_210761
  · decide +kernel

theorem prime_74679953 : Nat.Prime 74679953 := by
  apply nodeValid_prime [2, 347, 13451] ⟨74679953, 3, [(2, 4), (347, 1), (13451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_13451
  · decide +kernel

theorem prime_84602009 : Nat.Prime 84602009 := by
  apply nodeValid_prime [2, 2927, 3613] ⟨84602009, 3, [(2, 3), (2927, 1), (3613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2927
    · exact prime_3613
  · decide +kernel

theorem prime_95424101 : Nat.Prime 95424101 := by
  apply nodeValid_prime [2, 5, 47, 79, 257] ⟨95424101, 2, [(2, 2), (5, 2), (47, 1), (79, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_79
    · exact prime_257
  · decide +kernel

theorem prime_128119597 : Nat.Prime 128119597 := by
  apply nodeValid_prime [2, 3, 11, 970603] ⟨128119597, 2, [(2, 2), (3, 1), (11, 1), (970603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_970603
  · decide +kernel

theorem prime_165956443 : Nat.Prime 165956443 := by
  apply nodeValid_prime [2, 3, 311, 88937] ⟨165956443, 2, [(2, 1), (3, 1), (311, 1), (88937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_88937
  · decide +kernel

theorem prime_237879067 : Nat.Prime 237879067 := by
  apply nodeValid_prime [2, 3, 39646511] ⟨237879067, 2, [(2, 1), (3, 1), (39646511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39646511
  · decide +kernel

theorem prime_268020881 : Nat.Prime 268020881 := by
  apply nodeValid_prime [2, 5, 3350261] ⟨268020881, 3, [(2, 4), (5, 1), (3350261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3350261
  · decide +kernel

theorem prime_399481543 : Nat.Prime 399481543 := by
  apply nodeValid_prime [2, 3, 22193419] ⟨399481543, 5, [(2, 1), (3, 2), (22193419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22193419
  · decide +kernel

theorem prime_637147499 : Nat.Prime 637147499 := by
  apply nodeValid_prime [2, 13, 24505673] ⟨637147499, 2, [(2, 1), (13, 1), (24505673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_24505673
  · decide +kernel

theorem prime_1216215127 : Nat.Prime 1216215127 := by
  apply nodeValid_prime [2, 3, 7, 31, 311371] ⟨1216215127, 3, [(2, 1), (3, 2), (7, 1), (31, 1), (311371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_311371
  · decide +kernel

theorem prime_1427274403 : Nat.Prime 1427274403 := by
  apply nodeValid_prime [2, 3, 237879067] ⟨1427274403, 2, [(2, 1), (3, 1), (237879067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_237879067
  · decide +kernel

theorem prime_2503219153 : Nat.Prime 2503219153 := by
  apply nodeValid_prime [2, 3, 7, 229, 32533] ⟨2503219153, 5, [(2, 4), (3, 1), (7, 1), (229, 1), (32533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_229
    · exact prime_32533
  · decide +kernel

theorem prime_2544245329 : Nat.Prime 2544245329 := by
  apply nodeValid_prime [2, 3, 43, 149, 8273] ⟨2544245329, 14, [(2, 4), (3, 1), (43, 1), (149, 1), (8273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_149
    · exact prime_8273
  · decide +kernel

theorem prime_2650844897 : Nat.Prime 2650844897 := by
  apply nodeValid_prime [2, 7, 11834129] ⟨2650844897, 3, [(2, 5), (7, 1), (11834129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11834129
  · decide +kernel

theorem prime_3390497687 : Nat.Prime 3390497687 := by
  apply nodeValid_prime [2, 257, 6596299] ⟨3390497687, 5, [(2, 1), (257, 1), (6596299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_6596299
  · decide +kernel

theorem prime_6055996841 : Nat.Prime 6055996841 := by
  apply nodeValid_prime [2, 5, 41, 3692681] ⟨6055996841, 3, [(2, 3), (5, 1), (41, 1), (3692681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_3692681
  · decide +kernel

theorem prime_8702475499 : Nat.Prime 8702475499 := by
  apply nodeValid_prime [2, 3, 29, 67, 248827] ⟨8702475499, 3, [(2, 1), (3, 2), (29, 1), (67, 1), (248827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_67
    · exact prime_248827
  · decide +kernel

theorem prime_10733259377 : Nat.Prime 10733259377 := by
  apply nodeValid_prime [2, 7, 991, 96703] ⟨10733259377, 3, [(2, 4), (7, 1), (991, 1), (96703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_991
    · exact prime_96703
  · decide +kernel

theorem prime_13439907743 : Nat.Prime 13439907743 := by
  apply nodeValid_prime [2, 43, 379, 412343] ⟨13439907743, 5, [(2, 1), (43, 1), (379, 1), (412343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_379
    · exact prime_412343
  · decide +kernel

theorem prime_17923188721 : Nat.Prime 17923188721 := by
  apply nodeValid_prime [2, 3, 5, 74679953] ⟨17923188721, 23, [(2, 4), (3, 1), (5, 1), (74679953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_74679953
  · decide +kernel

theorem prime_18500032709 : Nat.Prime 18500032709 := by
  apply nodeValid_prime [2, 19, 37, 346261] ⟨18500032709, 2, [(2, 2), (19, 2), (37, 1), (346261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_346261
  · decide +kernel

theorem prime_51147318137 : Nat.Prime 51147318137 := by
  apply nodeValid_prime [2, 67, 95424101] ⟨51147318137, 3, [(2, 3), (67, 1), (95424101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_95424101
  · decide +kernel

theorem prime_139366109683 : Nat.Prime 139366109683 := by
  apply nodeValid_prime [2, 3, 149, 1193, 14519] ⟨139366109683, 3, [(2, 1), (3, 3), (149, 1), (1193, 1), (14519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_1193
    · exact prime_14519
  · decide +kernel

theorem prime_193198668787 : Nat.Prime 193198668787 := by
  apply nodeValid_prime [2, 3, 10733259377] ⟨193198668787, 11, [(2, 1), (3, 2), (10733259377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10733259377
  · decide +kernel

theorem prime_219800258063 : Nat.Prime 219800258063 := by
  apply nodeValid_prime [2, 7, 11, 1427274403] ⟨219800258063, 5, [(2, 1), (7, 1), (11, 1), (1427274403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1427274403
  · decide +kernel

theorem prime_257831556683 : Nat.Prime 257831556683 := by
  apply nodeValid_prime [2, 7, 131, 179, 509, 1543] ⟨257831556683, 2, [(2, 1), (7, 1), (131, 1), (179, 1), (509, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_179
    · exact prime_509
    · exact prime_1543
  · decide +kernel

theorem prime_517532777033 : Nat.Prime 517532777033 := by
  apply nodeValid_prime [2, 8317, 7778237] ⟨517532777033, 3, [(2, 3), (8317, 1), (7778237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8317
    · exact prime_7778237
  · decide +kernel

theorem prime_1565268868451 : Nat.Prime 1565268868451 := by
  apply nodeValid_prime [2, 5, 7, 251, 433, 41149] ⟨1565268868451, 2, [(2, 1), (5, 2), (7, 1), (251, 1), (433, 1), (41149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_251
    · exact prime_433
    · exact prime_41149
  · decide +kernel

theorem prime_3063271375649 : Nat.Prime 3063271375649 := by
  apply nodeValid_prime [2, 11, 8702475499] ⟨3063271375649, 3, [(2, 5), (11, 1), (8702475499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8702475499
  · decide +kernel

theorem prime_3063271376117 : Nat.Prime 3063271376117 := by
  apply nodeValid_prime [2, 7, 43, 2544245329] ⟨3063271376117, 2, [(2, 2), (7, 1), (43, 1), (2544245329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_2544245329
  · decide +kernel

theorem prime_3063271388123 : Nat.Prime 3063271388123 := by
  apply nodeValid_prime [2, 11, 293, 839, 566413] ⟨3063271388123, 2, [(2, 1), (11, 1), (293, 1), (839, 1), (566413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_293
    · exact prime_839
    · exact prime_566413
  · decide +kernel

theorem prime_3066054413027 : Nat.Prime 3066054413027 := by
  apply nodeValid_prime [2, 11, 139366109683] ⟨3066054413027, 2, [(2, 1), (11, 1), (139366109683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_139366109683
  · decide +kernel

theorem prime_3066054417577 : Nat.Prime 3066054417577 := by
  apply nodeValid_prime [2, 3, 197, 673, 321193] ⟨3066054417577, 5, [(2, 3), (3, 2), (197, 1), (673, 1), (321193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_673
    · exact prime_321193
  · decide +kernel

theorem prime_3066054418109 : Nat.Prime 3066054418109 := by
  apply nodeValid_prime [2, 11, 83, 863, 972833] ⟨3066054418109, 2, [(2, 2), (11, 1), (83, 1), (863, 1), (972833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83
    · exact prime_863
    · exact prime_972833
  · decide +kernel

theorem prime_3068839087451 : Nat.Prime 3068839087451 := by
  apply nodeValid_prime [2, 5, 229, 268020881] ⟨3068839087451, 2, [(2, 1), (5, 2), (229, 1), (268020881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_268020881
  · decide +kernel

theorem prime_3068839088221 : Nat.Prime 3068839088221 := by
  apply nodeValid_prime [2, 3, 5, 51147318137] ⟨3068839088221, 6, [(2, 2), (3, 1), (5, 1), (51147318137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_51147318137
  · decide +kernel

theorem prime_3068839149991 : Nat.Prime 3068839149991 := by
  apply nodeValid_prime [2, 3, 5, 23, 31, 8963, 16007] ⟨3068839149991, 6, [(2, 1), (3, 1), (5, 1), (23, 1), (31, 1), (8963, 1), (16007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_31
    · exact prime_8963
    · exact prime_16007
  · decide +kernel

theorem prime_3071625549353 : Nat.Prime 3071625549353 := by
  apply nodeValid_prime [2, 101, 2371, 1603339] ⟨3071625549353, 3, [(2, 3), (101, 1), (2371, 1), (1603339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_2371
    · exact prime_1603339
  · decide +kernel

theorem prime_3071625552689 : Nat.Prime 3071625552689 := by
  apply nodeValid_prime [2, 7, 11, 31, 71, 269, 4211] ⟨3071625552689, 3, [(2, 4), (7, 1), (11, 1), (31, 1), (71, 1), (269, 1), (4211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_71
    · exact prime_269
    · exact prime_4211
  · decide +kernel

theorem prime_3071625590753 : Nat.Prime 3071625590753 := by
  apply nodeValid_prime [2, 1061, 6607, 13693] ⟨3071625590753, 3, [(2, 5), (1061, 1), (6607, 1), (13693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1061
    · exact prime_6607
    · exact prime_13693
  · decide +kernel

theorem prime_3074413736689 : Nat.Prime 3074413736689 := by
  apply nodeValid_prime [2, 3, 7, 17, 5197, 103567] ⟨3074413736689, 38, [(2, 4), (3, 1), (7, 1), (17, 1), (5197, 1), (103567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_5197
    · exact prime_103567
  · decide +kernel

theorem prime_3074413749347 : Nat.Prime 3074413749347 := by
  apply nodeValid_prime [2, 165877, 9267149] ⟨3074413749347, 2, [(2, 1), (165877, 1), (9267149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_165877
    · exact prime_9267149
  · decide +kernel

theorem prime_3074413750547 : Nat.Prime 3074413750547 := by
  apply nodeValid_prime [2, 24151, 63649823] ⟨3074413750547, 2, [(2, 1), (24151, 1), (63649823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_24151
    · exact prime_63649823
  · decide +kernel

theorem prime_3077203602001 : Nat.Prime 3077203602001 := by
  apply nodeValid_prime [2, 3, 5, 11, 73, 638689] ⟨3077203602001, 17, [(2, 4), (3, 1), (5, 3), (11, 1), (73, 1), (638689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_73
    · exact prime_638689
  · decide +kernel

theorem prime_3077203612883 : Nat.Prime 3077203612883 := by
  apply nodeValid_prime [2, 7, 219800258063] ⟨3077203612883, 2, [(2, 1), (7, 1), (219800258063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_219800258063
  · decide +kernel

theorem prime_3079995111881 : Nat.Prime 3079995111881 := by
  apply nodeValid_prime [2, 5, 601, 128119597] ⟨3079995111881, 6, [(2, 3), (5, 1), (601, 1), (128119597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_601
    · exact prime_128119597
  · decide +kernel

theorem prime_3079995112541 : Nat.Prime 3079995112541 := by
  apply nodeValid_prime [2, 5, 23, 127, 52721587] ⟨3079995112541, 2, [(2, 2), (5, 1), (23, 1), (127, 1), (52721587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_127
    · exact prime_52721587
  · decide +kernel

theorem prime_3079995182491 : Nat.Prime 3079995182491 := by
  apply nodeValid_prime [2, 3, 5, 136429, 752527] ⟨3079995182491, 2, [(2, 1), (3, 1), (5, 1), (136429, 1), (752527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_136429
    · exact prime_752527
  · decide +kernel

theorem prime_3082788459701 : Nat.Prime 3082788459701 := by
  apply nodeValid_prime [2, 5, 73, 107, 3946727] ⟨3082788459701, 2, [(2, 2), (5, 2), (73, 1), (107, 1), (3946727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_107
    · exact prime_3946727
  · decide +kernel

theorem prime_3082788460013 : Nat.Prime 3082788460013 := by
  apply nodeValid_prime [2, 43, 17923188721] ⟨3082788460013, 2, [(2, 2), (43, 1), (17923188721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_17923188721
  · decide +kernel

theorem prime_3082788484843 : Nat.Prime 3082788484843 := by
  apply nodeValid_prime [2, 3, 11, 19, 97, 2003, 12653] ⟨3082788484843, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (97, 1), (2003, 1), (12653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_97
    · exact prime_2003
    · exact prime_12653
  · decide +kernel

theorem prime_3085583460109 : Nat.Prime 3085583460109 := by
  apply nodeValid_prime [2, 3, 97, 2650844897] ⟨3085583460109, 6, [(2, 2), (3, 1), (97, 1), (2650844897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_2650844897
  · decide +kernel

theorem prime_3085583461673 : Nat.Prime 3085583461673 := by
  apply nodeValid_prime [2, 53231, 7245739] ⟨3085583461673, 3, [(2, 3), (53231, 1), (7245739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53231
    · exact prime_7245739
  · decide +kernel

theorem prime_3085583504449 : Nat.Prime 3085583504449 := by
  apply nodeValid_prime [2, 3, 239, 311, 216211] ⟨3085583504449, 14, [(2, 6), (3, 1), (239, 1), (311, 1), (216211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_311
    · exact prime_216211
  · decide +kernel

theorem prime_3088380226873 : Nat.Prime 3088380226873 := by
  apply nodeValid_prime [2, 3, 239873, 536461] ⟨3088380226873, 11, [(2, 3), (3, 1), (239873, 1), (536461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239873
    · exact prime_536461
  · decide +kernel

theorem prime_3088380227081 : Nat.Prime 3088380227081 := by
  apply nodeValid_prime [2, 5, 233, 1973, 167953] ⟨3088380227081, 3, [(2, 3), (5, 1), (233, 1), (1973, 1), (167953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233
    · exact prime_1973
    · exact prime_167953
  · decide +kernel

theorem prime_3088380245207 : Nat.Prime 3088380245207 := by
  apply nodeValid_prime [2, 151, 1487, 6877219] ⟨3088380245207, 5, [(2, 1), (151, 1), (1487, 1), (6877219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_1487
    · exact prime_6877219
  · decide +kernel

theorem prime_3091178700593 : Nat.Prime 3091178700593 := by
  apply nodeValid_prime [2, 193198668787] ⟨3091178700593, 3, [(2, 4), (193198668787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193198668787
  · decide +kernel

theorem prime_3091178780749 : Nat.Prime 3091178780749 := by
  apply nodeValid_prime [2, 3, 821, 853, 122611] ⟨3091178780749, 2, [(2, 2), (3, 2), (821, 1), (853, 1), (122611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_821
    · exact prime_853
    · exact prime_122611
  · decide +kernel

theorem prime_3091178780891 : Nat.Prime 3091178780891 := by
  apply nodeValid_prime [2, 5, 23, 13439907743] ⟨3091178780891, 2, [(2, 1), (5, 1), (23, 1), (13439907743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_13439907743
  · decide +kernel

theorem prime_3093978680197 : Nat.Prime 3093978680197 := by
  apply nodeValid_prime [2, 3, 257831556683] ⟨3093978680197, 2, [(2, 2), (3, 1), (257831556683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257831556683
  · decide +kernel

theorem prime_3093978680473 : Nat.Prime 3093978680473 := by
  apply nodeValid_prime [2, 3, 4937, 26112169] ⟨3093978680473, 5, [(2, 3), (3, 1), (4937, 1), (26112169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4937
    · exact prime_26112169
  · decide +kernel

theorem prime_3093978873109 : Nat.Prime 3093978873109 := by
  apply nodeValid_prime [2, 3, 103, 2503219153] ⟨3093978873109, 6, [(2, 2), (3, 1), (103, 1), (2503219153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_2503219153
  · decide +kernel

theorem prime_3096780762587 : Nat.Prime 3096780762587 := by
  apply nodeValid_prime [2, 7, 73, 131, 191, 347, 349] ⟨3096780762587, 2, [(2, 1), (7, 1), (73, 1), (131, 1), (191, 1), (347, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_131
    · exact prime_191
    · exact prime_347
    · exact prime_349
  · decide +kernel

theorem prime_3096780921313 : Nat.Prime 3096780921313 := by
  apply nodeValid_prime [2, 3, 13, 31, 53, 271, 5573] ⟨3096780921313, 5, [(2, 5), (3, 1), (13, 1), (31, 1), (53, 1), (271, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_53
    · exact prime_271
    · exact prime_5573
  · decide +kernel

theorem prime_3096780921337 : Nat.Prime 3096780921337 := by
  apply nodeValid_prime [2, 3, 17, 19, 399481543] ⟨3096780921337, 7, [(2, 3), (3, 1), (17, 1), (19, 1), (399481543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_399481543
  · decide +kernel

theorem prime_3099584363237 : Nat.Prime 3099584363237 := by
  apply nodeValid_prime [2, 23, 26669, 1263307] ⟨3099584363237, 2, [(2, 2), (23, 1), (26669, 1), (1263307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_26669
    · exact prime_1263307
  · decide +kernel

theorem prime_3099584363347 : Nat.Prime 3099584363347 := by
  apply nodeValid_prime [2, 3, 31, 211, 241, 313, 349] ⟨3099584363347, 2, [(2, 1), (3, 2), (31, 1), (211, 1), (241, 1), (313, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_211
    · exact prime_241
    · exact prime_313
    · exact prime_349
  · decide +kernel

theorem prime_3099584364977 : Nat.Prime 3099584364977 := by
  apply nodeValid_prime [2, 11, 14869, 1184429] ⟨3099584364977, 3, [(2, 4), (11, 1), (14869, 1), (1184429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_14869
    · exact prime_1184429
  · decide +kernel

theorem prime_3102389684599 : Nat.Prime 3102389684599 := by
  apply nodeValid_prime [2, 3, 23, 37, 421, 1443223] ⟨3102389684599, 3, [(2, 1), (3, 1), (23, 1), (37, 1), (421, 1), (1443223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
    · exact prime_421
    · exact prime_1443223
  · decide +kernel

theorem prime_3102389745443 : Nat.Prime 3102389745443 := by
  apply nodeValid_prime [2, 13, 719, 165956443] ⟨3102389745443, 2, [(2, 1), (13, 1), (719, 1), (165956443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_719
    · exact prime_165956443
  · decide +kernel

theorem prime_3102389745649 : Nat.Prime 3102389745649 := by
  apply nodeValid_prime [2, 3, 37, 43, 2011, 20201] ⟨3102389745649, 19, [(2, 4), (3, 1), (37, 1), (43, 1), (2011, 1), (20201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_43
    · exact prime_2011
    · exact prime_20201
  · decide +kernel

theorem prime_3105196662199 : Nat.Prime 3105196662199 := by
  apply nodeValid_prime [2, 3, 517532777033] ⟨3105196662199, 7, [(2, 1), (3, 1), (517532777033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_517532777033
  · decide +kernel

theorem prime_3105196663633 : Nat.Prime 3105196663633 := by
  apply nodeValid_prime [2, 3, 7, 181, 51058877] ⟨3105196663633, 5, [(2, 4), (3, 1), (7, 1), (181, 1), (51058877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_181
    · exact prime_51058877
  · decide +kernel

theorem prime_3105196726817 : Nat.Prime 3105196726817 := by
  apply nodeValid_prime [2, 3449, 4021, 6997] ⟨3105196726817, 3, [(2, 5), (3449, 1), (4021, 1), (6997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3449
    · exact prime_4021
    · exact prime_6997
  · decide +kernel

theorem prime_3108005493457 : Nat.Prime 3108005493457 := by
  apply nodeValid_prime [2, 3, 1307, 49541021] ⟨3108005493457, 10, [(2, 4), (3, 1), (1307, 1), (49541021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1307
    · exact prime_49541021
  · decide +kernel

theorem prime_3108005495113 : Nat.Prime 3108005495113 := by
  apply nodeValid_prime [2, 3, 7, 18500032709] ⟨3108005495113, 5, [(2, 3), (3, 1), (7, 1), (18500032709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18500032709
  · decide +kernel

theorem prime_3108005500123 : Nat.Prime 3108005500123 := by
  apply nodeValid_prime [2, 3, 271, 637147499] ⟨3108005500123, 2, [(2, 1), (3, 2), (271, 1), (637147499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_637147499
  · decide +kernel

theorem prime_3110815870697 : Nat.Prime 3110815870697 := by
  apply nodeValid_prime [2, 103, 109, 34635431] ⟨3110815870697, 3, [(2, 3), (103, 1), (109, 1), (34635431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_109
    · exact prime_34635431
  · decide +kernel

theorem prime_3110815870931 : Nat.Prime 3110815870931 := by
  apply nodeValid_prime [2, 5, 3677, 84602009] ⟨3110815870931, 6, [(2, 1), (5, 1), (3677, 1), (84602009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3677
    · exact prime_84602009
  · decide +kernel

theorem prime_3110815993471 : Nat.Prime 3110815993471 := by
  apply nodeValid_prime [2, 3, 5, 12541, 8268389] ⟨3110815993471, 6, [(2, 1), (3, 1), (5, 1), (12541, 1), (8268389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12541
    · exact prime_8268389
  · decide +kernel

theorem prime_3113628183977 : Nat.Prime 3113628183977 := by
  apply nodeValid_prime [2, 197, 15767, 125303] ⟨3113628183977, 3, [(2, 3), (197, 1), (15767, 1), (125303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_15767
    · exact prime_125303
  · decide +kernel

theorem prime_3113628184369 : Nat.Prime 3113628184369 := by
  apply nodeValid_prime [2, 3, 13, 43, 79, 54403] ⟨3113628184369, 11, [(2, 4), (3, 4), (13, 1), (43, 1), (79, 1), (54403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_79
    · exact prime_54403
  · decide +kernel

theorem prime_3113628221189 : Nat.Prime 3113628221189 := by
  apply nodeValid_prime [2, 28867, 26965291] ⟨3113628221189, 2, [(2, 2), (28867, 1), (26965291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_28867
    · exact prime_26965291
  · decide +kernel

theorem prime_3116442177421 : Nat.Prime 3116442177421 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 31, 3413, 3433] ⟨3116442177421, 6, [(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (31, 1), (3413, 1), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_3413
    · exact prime_3433
  · decide +kernel

theorem prime_3116442198299 : Nat.Prime 3116442198299 := by
  apply nodeValid_prime [2, 11, 13, 431, 25282253] ⟨3116442198299, 2, [(2, 1), (11, 1), (13, 1), (431, 1), (25282253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_431
    · exact prime_25282253
  · decide +kernel

theorem prime_3116442198703 : Nat.Prime 3116442198703 := by
  apply nodeValid_prime [2, 3, 7, 433, 3497243] ⟨3116442198703, 3, [(2, 1), (3, 1), (7, 3), (433, 1), (3497243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_433
    · exact prime_3497243
  · decide +kernel

theorem prime_3119257853807 : Nat.Prime 3119257853807 := by
  apply nodeValid_prime [2, 89, 277, 63263251] ⟨3119257853807, 5, [(2, 1), (89, 1), (277, 1), (63263251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_277
    · exact prime_63263251
  · decide +kernel

theorem prime_3119257870667 : Nat.Prime 3119257870667 := by
  apply nodeValid_prime [2, 7, 17, 71, 7649, 24133] ⟨3119257870667, 2, [(2, 1), (7, 1), (17, 1), (71, 1), (7649, 1), (24133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_71
    · exact prime_7649
    · exact prime_24133
  · decide +kernel

theorem prime_3119257872041 : Nat.Prime 3119257872041 := by
  apply nodeValid_prime [2, 5, 23, 3390497687] ⟨3119257872041, 3, [(2, 3), (5, 1), (23, 1), (3390497687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_3390497687
  · decide +kernel

theorem prime_3122075250193 : Nat.Prime 3122075250193 := by
  apply nodeValid_prime [2, 3, 29, 1667, 1345453] ⟨3122075250193, 5, [(2, 4), (3, 1), (29, 1), (1667, 1), (1345453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1667
    · exact prime_1345453
  · decide +kernel

theorem prime_3122075354023 : Nat.Prime 3122075354023 := by
  apply nodeValid_prime [2, 3, 151, 479, 2398051] ⟨3122075354023, 3, [(2, 1), (3, 2), (151, 1), (479, 1), (2398051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_479
    · exact prime_2398051
  · decide +kernel

theorem prime_3122075361481 : Nat.Prime 3122075361481 := by
  apply nodeValid_prime [2, 3, 5, 73699, 353021] ⟨3122075361481, 7, [(2, 3), (3, 1), (5, 1), (73699, 1), (353021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73699
    · exact prime_353021
  · decide +kernel

theorem prime_3124894352513 : Nat.Prime 3124894352513 := by
  apply nodeValid_prime [2, 97, 4967, 50671] ⟨3124894352513, 3, [(2, 7), (97, 1), (4967, 1), (50671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_4967
    · exact prime_50671
  · decide +kernel

theorem prime_3124894353797 : Nat.Prime 3124894353797 := by
  apply nodeValid_prime [2, 19, 373, 1297, 84991] ⟨3124894353797, 2, [(2, 2), (19, 1), (373, 1), (1297, 1), (84991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_373
    · exact prime_1297
    · exact prime_84991
  · decide +kernel

theorem prime_3124894369957 : Nat.Prime 3124894369957 := by
  apply nodeValid_prime [2, 3, 43, 6055996841] ⟨3124894369957, 5, [(2, 2), (3, 1), (43, 1), (6055996841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_6055996841
  · decide +kernel

theorem prime_3127715153869 : Nat.Prime 3127715153869 := by
  apply nodeValid_prime [2, 3, 59, 911, 4849261] ⟨3127715153869, 2, [(2, 2), (3, 1), (59, 1), (911, 1), (4849261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_911
    · exact prime_4849261
  · decide +kernel

theorem prime_3127715155297 : Nat.Prime 3127715155297 := by
  apply nodeValid_prime [2, 3, 179, 20223691] ⟨3127715155297, 5, [(2, 5), (3, 3), (179, 1), (20223691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_20223691
  · decide +kernel

theorem prime_3127715212331 : Nat.Prime 3127715212331 := by
  apply nodeValid_prime [2, 5, 103, 617, 4921583] ⟨3127715212331, 2, [(2, 1), (5, 1), (103, 1), (617, 1), (4921583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_617
    · exact prime_4921583
  · decide +kernel

theorem prime_3130537736899 : Nat.Prime 3130537736899 := by
  apply nodeValid_prime [2, 3, 11, 13, 1216215127] ⟨3130537736899, 2, [(2, 1), (3, 2), (11, 1), (13, 1), (1216215127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_1216215127
  · decide +kernel

theorem prime_3130537736903 : Nat.Prime 3130537736903 := by
  apply nodeValid_prime [2, 1565268868451] ⟨3130537736903, 5, [(2, 1), (1565268868451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1565268868451
  · decide +kernel

theorem prime_3130537782059 : Nat.Prime 3130537782059 := by
  apply nodeValid_prime [2, 353, 3083, 1438271] ⟨3130537782059, 2, [(2, 1), (353, 1), (3083, 1), (1438271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_3083
    · exact prime_1438271
  · decide +kernel

end Sude.Lucas.Generated
