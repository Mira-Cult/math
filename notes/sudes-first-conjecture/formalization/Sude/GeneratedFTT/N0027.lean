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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1153 : Nat.Prime 1153 := by
  apply nodeValid_prime [2, 3] ⟨1153, 5, [(2, 7), (3, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_1721 : Nat.Prime 1721 := by
  apply nodeValid_prime [2, 5, 43] ⟨1721, 3, [(2, 3), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_2801 : Nat.Prime 2801 := by
  apply nodeValid_prime [2, 5, 7] ⟨2801, 3, [(2, 4), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_4447 : Nat.Prime 4447 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨4447, 3, [(2, 1), (3, 2), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_4519 : Nat.Prime 4519 := by
  apply nodeValid_prime [2, 3, 251] ⟨4519, 3, [(2, 1), (3, 2), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
  · decide +kernel

theorem prime_4729 : Nat.Prime 4729 := by
  apply nodeValid_prime [2, 3, 197] ⟨4729, 17, [(2, 3), (3, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
  · decide +kernel

theorem prime_5639 : Nat.Prime 5639 := by
  apply nodeValid_prime [2, 2819] ⟨5639, 7, [(2, 1), (2819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2819
  · decide +kernel

theorem prime_7699 : Nat.Prime 7699 := by
  apply nodeValid_prime [2, 3, 1283] ⟨7699, 3, [(2, 1), (3, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1283
  · decide +kernel

theorem prime_8111 : Nat.Prime 8111 := by
  apply nodeValid_prime [2, 5, 811] ⟨8111, 11, [(2, 1), (5, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_811
  · decide +kernel

theorem prime_8287 : Nat.Prime 8287 := by
  apply nodeValid_prime [2, 3, 1381] ⟨8287, 3, [(2, 1), (3, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1381
  · decide +kernel

theorem prime_8933 : Nat.Prime 8933 := by
  apply nodeValid_prime [2, 7, 11, 29] ⟨8933, 2, [(2, 2), (7, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_10601 : Nat.Prime 10601 := by
  apply nodeValid_prime [2, 5, 53] ⟨10601, 3, [(2, 3), (5, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_10729 : Nat.Prime 10729 := by
  apply nodeValid_prime [2, 3, 149] ⟨10729, 7, [(2, 3), (3, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
  · decide +kernel

theorem prime_10739 : Nat.Prime 10739 := by
  apply nodeValid_prime [2, 7, 13, 59] ⟨10739, 6, [(2, 1), (7, 1), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_12119 : Nat.Prime 12119 := by
  apply nodeValid_prime [2, 73, 83] ⟨12119, 7, [(2, 1), (73, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_83
  · decide +kernel

theorem prime_12967 : Nat.Prime 12967 := by
  apply nodeValid_prime [2, 3, 2161] ⟨12967, 3, [(2, 1), (3, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2161
  · decide +kernel

theorem prime_14449 : Nat.Prime 14449 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨14449, 22, [(2, 4), (3, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_15973 : Nat.Prime 15973 := by
  apply nodeValid_prime [2, 3, 11] ⟨15973, 7, [(2, 2), (3, 1), (11, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_18077 : Nat.Prime 18077 := by
  apply nodeValid_prime [2, 4519] ⟨18077, 2, [(2, 2), (4519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4519
  · decide +kernel

theorem prime_19819 : Nat.Prime 19819 := by
  apply nodeValid_prime [2, 3, 367] ⟨19819, 3, [(2, 1), (3, 3), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
  · decide +kernel

theorem prime_21767 : Nat.Prime 21767 := by
  apply nodeValid_prime [2, 10883] ⟨21767, 5, [(2, 1), (10883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10883
  · decide +kernel

theorem prime_23339 : Nat.Prime 23339 := by
  apply nodeValid_prime [2, 7, 1667] ⟨23339, 2, [(2, 1), (7, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1667
  · decide +kernel

theorem prime_23743 : Nat.Prime 23743 := by
  apply nodeValid_prime [2, 3, 1319] ⟨23743, 3, [(2, 1), (3, 2), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1319
  · decide +kernel

theorem prime_24439 : Nat.Prime 24439 := by
  apply nodeValid_prime [2, 3, 4073] ⟨24439, 6, [(2, 1), (3, 1), (4073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4073
  · decide +kernel

theorem prime_25867 : Nat.Prime 25867 := by
  apply nodeValid_prime [2, 3, 479] ⟨25867, 2, [(2, 1), (3, 3), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
  · decide +kernel

theorem prime_27457 : Nat.Prime 27457 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨27457, 7, [(2, 6), (3, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_32479 : Nat.Prime 32479 := by
  apply nodeValid_prime [2, 3, 5413] ⟨32479, 6, [(2, 1), (3, 1), (5413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5413
  · decide +kernel

theorem prime_33149 : Nat.Prime 33149 := by
  apply nodeValid_prime [2, 8287] ⟨33149, 2, [(2, 2), (8287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8287
  · decide +kernel

theorem prime_41411 : Nat.Prime 41411 := by
  apply nodeValid_prime [2, 5, 41, 101] ⟨41411, 2, [(2, 1), (5, 1), (41, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_101
  · decide +kernel

theorem prime_59629 : Nat.Prime 59629 := by
  apply nodeValid_prime [2, 3, 4969] ⟨59629, 2, [(2, 2), (3, 1), (4969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4969
  · decide +kernel

theorem prime_63703 : Nat.Prime 63703 := by
  apply nodeValid_prime [2, 3, 3539] ⟨63703, 3, [(2, 1), (3, 2), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3539
  · decide +kernel

theorem prime_63761 : Nat.Prime 63761 := by
  apply nodeValid_prime [2, 5, 797] ⟨63761, 3, [(2, 4), (5, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_797
  · decide +kernel

theorem prime_68821 : Nat.Prime 68821 := by
  apply nodeValid_prime [2, 3, 5, 31, 37] ⟨68821, 14, [(2, 2), (3, 1), (5, 1), (31, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_37
  · decide +kernel

theorem prime_83537 : Nat.Prime 83537 := by
  apply nodeValid_prime [2, 23, 227] ⟨83537, 3, [(2, 4), (23, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_227
  · decide +kernel

theorem prime_84809 : Nat.Prime 84809 := by
  apply nodeValid_prime [2, 10601] ⟨84809, 3, [(2, 3), (10601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10601
  · decide +kernel

theorem prime_90659 : Nat.Prime 90659 := by
  apply nodeValid_prime [2, 45329] ⟨90659, 2, [(2, 1), (45329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45329
  · decide +kernel

theorem prime_91873 : Nat.Prime 91873 := by
  apply nodeValid_prime [2, 3, 11, 29] ⟨91873, 5, [(2, 5), (3, 2), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_97001 : Nat.Prime 97001 := by
  apply nodeValid_prime [2, 5, 97] ⟨97001, 3, [(2, 3), (5, 3), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_110441 : Nat.Prime 110441 := by
  apply nodeValid_prime [2, 5, 11, 251] ⟨110441, 13, [(2, 3), (5, 1), (11, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_251
  · decide +kernel

theorem prime_113083 : Nat.Prime 113083 := by
  apply nodeValid_prime [2, 3, 47, 401] ⟨113083, 2, [(2, 1), (3, 1), (47, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_401
  · decide +kernel

theorem prime_118429 : Nat.Prime 118429 := by
  apply nodeValid_prime [2, 3, 71, 139] ⟨118429, 6, [(2, 2), (3, 1), (71, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_139
  · decide +kernel

theorem prime_122147 : Nat.Prime 122147 := by
  apply nodeValid_prime [2, 157, 389] ⟨122147, 2, [(2, 1), (157, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_389
  · decide +kernel

theorem prime_123583 : Nat.Prime 123583 := by
  apply nodeValid_prime [2, 3, 43, 479] ⟨123583, 5, [(2, 1), (3, 1), (43, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_479
  · decide +kernel

theorem prime_136709 : Nat.Prime 136709 := by
  apply nodeValid_prime [2, 11, 13, 239] ⟨136709, 3, [(2, 2), (11, 1), (13, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_239
  · decide +kernel

theorem prime_142573 : Nat.Prime 142573 := by
  apply nodeValid_prime [2, 3, 109] ⟨142573, 2, [(2, 2), (3, 1), (109, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_158341 : Nat.Prime 158341 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 29] ⟨158341, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_194003 : Nat.Prime 194003 := by
  apply nodeValid_prime [2, 97001] ⟨194003, 2, [(2, 1), (97001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_97001
  · decide +kernel

theorem prime_240899 : Nat.Prime 240899 := by
  apply nodeValid_prime [2, 7, 17207] ⟨240899, 6, [(2, 1), (7, 1), (17207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17207
  · decide +kernel

theorem prime_259783 : Nat.Prime 259783 := by
  apply nodeValid_prime [2, 3, 29, 1493] ⟨259783, 17, [(2, 1), (3, 1), (29, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1493
  · decide +kernel

theorem prime_290557 : Nat.Prime 290557 := by
  apply nodeValid_prime [2, 3, 7, 1153] ⟨290557, 2, [(2, 2), (3, 2), (7, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1153
  · decide +kernel

theorem prime_299671 : Nat.Prime 299671 := by
  apply nodeValid_prime [2, 3, 5, 7, 1427] ⟨299671, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1427
  · decide +kernel

theorem prime_338497 : Nat.Prime 338497 := by
  apply nodeValid_prime [2, 3, 41, 43] ⟨338497, 7, [(2, 6), (3, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_343153 : Nat.Prime 343153 := by
  apply nodeValid_prime [2, 3, 2383] ⟨343153, 5, [(2, 4), (3, 2), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2383
  · decide +kernel

theorem prime_382073 : Nat.Prime 382073 := by
  apply nodeValid_prime [2, 163, 293] ⟨382073, 3, [(2, 3), (163, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_293
  · decide +kernel

theorem prime_418031 : Nat.Prime 418031 := by
  apply nodeValid_prime [2, 5, 17, 2459] ⟨418031, 11, [(2, 1), (5, 1), (17, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2459
  · decide +kernel

theorem prime_501223 : Nat.Prime 501223 := by
  apply nodeValid_prime [2, 3, 83537] ⟨501223, 5, [(2, 1), (3, 1), (83537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83537
  · decide +kernel

theorem prime_533641 : Nat.Prime 533641 := by
  apply nodeValid_prime [2, 3, 5, 4447] ⟨533641, 17, [(2, 3), (3, 1), (5, 1), (4447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4447
  · decide +kernel

theorem prime_541711 : Nat.Prime 541711 := by
  apply nodeValid_prime [2, 3, 5, 13, 463] ⟨541711, 11, [(2, 1), (3, 2), (5, 1), (13, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_463
  · decide +kernel

theorem prime_581341 : Nat.Prime 581341 := by
  apply nodeValid_prime [2, 3, 5, 9689] ⟨581341, 2, [(2, 2), (3, 1), (5, 1), (9689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9689
  · decide +kernel

theorem prime_594571 : Nat.Prime 594571 := by
  apply nodeValid_prime [2, 3, 5, 19819] ⟨594571, 3, [(2, 1), (3, 1), (5, 1), (19819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19819
  · decide +kernel

theorem prime_606833 : Nat.Prime 606833 := by
  apply nodeValid_prime [2, 17, 23, 97] ⟨606833, 3, [(2, 4), (17, 1), (23, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_97
  · decide +kernel

theorem prime_631903 : Nat.Prime 631903 := by
  apply nodeValid_prime [2, 3, 19, 23, 241] ⟨631903, 3, [(2, 1), (3, 1), (19, 1), (23, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_241
  · decide +kernel

theorem prime_705499 : Nat.Prime 705499 := by
  apply nodeValid_prime [2, 3, 31, 3793] ⟨705499, 2, [(2, 1), (3, 1), (31, 1), (3793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3793
  · decide +kernel

theorem prime_725273 : Nat.Prime 725273 := by
  apply nodeValid_prime [2, 90659] ⟨725273, 3, [(2, 3), (90659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90659
  · decide +kernel

theorem prime_739493 : Nat.Prime 739493 := by
  apply nodeValid_prime [2, 13, 14221] ⟨739493, 2, [(2, 2), (13, 1), (14221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_14221
  · decide +kernel

theorem prime_748273 : Nat.Prime 748273 := by
  apply nodeValid_prime [2, 3, 7, 17, 131] ⟨748273, 5, [(2, 4), (3, 1), (7, 1), (17, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_131
  · decide +kernel

theorem prime_751379 : Nat.Prime 751379 := by
  apply nodeValid_prime [2, 31, 12119] ⟨751379, 2, [(2, 1), (31, 1), (12119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_12119
  · decide +kernel

theorem prime_756641 : Nat.Prime 756641 := by
  apply nodeValid_prime [2, 5, 4729] ⟨756641, 6, [(2, 5), (5, 1), (4729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4729
  · decide +kernel

theorem prime_807017 : Nat.Prime 807017 := by
  apply nodeValid_prime [2, 7, 14411] ⟨807017, 3, [(2, 3), (7, 1), (14411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_14411
  · decide +kernel

theorem prime_887323 : Nat.Prime 887323 := by
  apply nodeValid_prime [2, 3, 41, 3607] ⟨887323, 2, [(2, 1), (3, 1), (41, 1), (3607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_3607
  · decide +kernel

theorem prime_890963 : Nat.Prime 890963 := by
  apply nodeValid_prime [2, 79, 5639] ⟨890963, 2, [(2, 1), (79, 1), (5639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_5639
  · decide +kernel

theorem prime_971699 : Nat.Prime 971699 := by
  apply nodeValid_prime [2, 7, 13, 19, 281] ⟨971699, 2, [(2, 1), (7, 1), (13, 1), (19, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_281
  · decide +kernel

theorem prime_1041041 : Nat.Prime 1041041 := by
  apply nodeValid_prime [2, 5, 7, 11, 13] ⟨1041041, 21, [(2, 4), (5, 1), (7, 1), (11, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_1235831 : Nat.Prime 1235831 := by
  apply nodeValid_prime [2, 5, 123583] ⟨1235831, 7, [(2, 1), (5, 1), (123583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_123583
  · decide +kernel

theorem prime_1825631 : Nat.Prime 1825631 := by
  apply nodeValid_prime [2, 5, 17, 10739] ⟨1825631, 11, [(2, 1), (5, 1), (17, 1), (10739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_10739
  · decide +kernel

theorem prime_1895521 : Nat.Prime 1895521 := by
  apply nodeValid_prime [2, 3, 5, 11, 359] ⟨1895521, 14, [(2, 5), (3, 1), (5, 1), (11, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_359
  · decide +kernel

theorem prime_2058919 : Nat.Prime 2058919 := by
  apply nodeValid_prime [2, 3, 343153] ⟨2058919, 3, [(2, 1), (3, 1), (343153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_343153
  · decide +kernel

theorem prime_2104363 : Nat.Prime 2104363 := by
  apply nodeValid_prime [2, 3, 13, 17, 23] ⟨2104363, 5, [(2, 1), (3, 2), (13, 1), (17, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_2141647 : Nat.Prime 2141647 := by
  apply nodeValid_prime [2, 3, 13, 27457] ⟨2141647, 3, [(2, 1), (3, 1), (13, 1), (27457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_27457
  · decide +kernel

theorem prime_2487827 : Nat.Prime 2487827 := by
  apply nodeValid_prime [2, 11, 113083] ⟨2487827, 2, [(2, 1), (11, 1), (113083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113083
  · decide +kernel

theorem prime_2715191 : Nat.Prime 2715191 := by
  apply nodeValid_prime [2, 5, 47, 53, 109] ⟨2715191, 13, [(2, 1), (5, 1), (47, 1), (53, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_53
    · exact prime_109
  · decide +kernel

theorem prime_2821997 : Nat.Prime 2821997 := by
  apply nodeValid_prime [2, 705499] ⟨2821997, 2, [(2, 2), (705499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_705499
  · decide +kernel

theorem prime_3640999 : Nat.Prime 3640999 := by
  apply nodeValid_prime [2, 3, 606833] ⟨3640999, 6, [(2, 1), (3, 1), (606833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_606833
  · decide +kernel

theorem prime_3814963 : Nat.Prime 3814963 := by
  apply nodeValid_prime [2, 3, 227, 2801] ⟨3814963, 3, [(2, 1), (3, 1), (227, 1), (2801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_2801
  · decide +kernel

theorem prime_3824869 : Nat.Prime 3824869 := by
  apply nodeValid_prime [2, 3, 29, 379] ⟨3824869, 2, [(2, 2), (3, 1), (29, 2), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_379
  · decide +kernel

theorem prime_3991619 : Nat.Prime 3991619 := by
  apply nodeValid_prime [2, 29, 68821] ⟨3991619, 2, [(2, 1), (29, 1), (68821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_68821
  · decide +kernel

theorem prime_5437793 : Nat.Prime 5437793 := by
  apply nodeValid_prime [2, 109, 1559] ⟨5437793, 3, [(2, 5), (109, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_1559
  · decide +kernel

theorem prime_6014677 : Nat.Prime 6014677 := by
  apply nodeValid_prime [2, 3, 501223] ⟨6014677, 2, [(2, 2), (3, 1), (501223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_501223
  · decide +kernel

theorem prime_7083719 : Nat.Prime 7083719 := by
  apply nodeValid_prime [2, 83, 139, 307] ⟨7083719, 11, [(2, 1), (83, 1), (139, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_139
    · exact prime_307
  · decide +kernel

theorem prime_9326501 : Nat.Prime 9326501 := by
  apply nodeValid_prime [2, 5, 23, 811] ⟨9326501, 2, [(2, 2), (5, 3), (23, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_811
  · decide +kernel

theorem prime_9886649 : Nat.Prime 9886649 := by
  apply nodeValid_prime [2, 1235831] ⟨9886649, 3, [(2, 3), (1235831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1235831
  · decide +kernel

theorem prime_10153823 : Nat.Prime 10153823 := by
  apply nodeValid_prime [2, 7, 725273] ⟨10153823, 5, [(2, 1), (7, 1), (725273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_725273
  · decide +kernel

theorem prime_10788157 : Nat.Prime 10788157 := by
  apply nodeValid_prime [2, 3, 299671] ⟨10788157, 19, [(2, 2), (3, 2), (299671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_299671
  · decide +kernel

theorem prime_12849883 : Nat.Prime 12849883 := by
  apply nodeValid_prime [2, 3, 2141647] ⟨12849883, 2, [(2, 1), (3, 1), (2141647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2141647
  · decide +kernel

theorem prime_16478923 : Nat.Prime 16478923 := by
  apply nodeValid_prime [2, 3, 547, 5021] ⟨16478923, 2, [(2, 1), (3, 1), (547, 1), (5021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_547
    · exact prime_5021
  · decide +kernel

theorem prime_18238067 : Nat.Prime 18238067 := by
  apply nodeValid_prime [2, 7, 11, 118429] ⟨18238067, 2, [(2, 1), (7, 1), (11, 1), (118429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_118429
  · decide +kernel

theorem prime_22532759 : Nat.Prime 22532759 := by
  apply nodeValid_prime [2, 461, 24439] ⟨22532759, 7, [(2, 1), (461, 1), (24439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_461
    · exact prime_24439
  · decide +kernel

theorem prime_27239077 : Nat.Prime 27239077 := by
  apply nodeValid_prime [2, 3, 756641] ⟨27239077, 2, [(2, 2), (3, 2), (756641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_756641
  · decide +kernel

theorem prime_28183079 : Nat.Prime 28183079 := by
  apply nodeValid_prime [2, 7, 11, 127, 131] ⟨28183079, 7, [(2, 1), (7, 1), (11, 2), (127, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_127
    · exact prime_131
  · decide +kernel

theorem prime_37400773 : Nat.Prime 37400773 := by
  apply nodeValid_prime [2, 3, 1721, 1811] ⟨37400773, 5, [(2, 2), (3, 1), (1721, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1721
    · exact prime_1811
  · decide +kernel

theorem prime_54859687 : Nat.Prime 54859687 := by
  apply nodeValid_prime [2, 3, 7, 139, 9397] ⟨54859687, 5, [(2, 1), (3, 1), (7, 1), (139, 1), (9397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
    · exact prime_9397
  · decide +kernel

theorem prime_54956233 : Nat.Prime 54956233 := by
  apply nodeValid_prime [2, 3, 84809] ⟨54956233, 5, [(2, 3), (3, 4), (84809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_84809
  · decide +kernel

theorem prime_62714009 : Nat.Prime 62714009 := by
  apply nodeValid_prime [2, 7, 23, 29, 73] ⟨62714009, 3, [(2, 3), (7, 1), (23, 2), (29, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_29
    · exact prime_73
  · decide +kernel

theorem prime_71585557 : Nat.Prime 71585557 := by
  apply nodeValid_prime [2, 3, 7, 139, 6131] ⟨71585557, 5, [(2, 2), (3, 1), (7, 1), (139, 1), (6131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
    · exact prime_6131
  · decide +kernel

theorem prime_72485531 : Nat.Prime 72485531 := by
  apply nodeValid_prime [2, 5, 13, 43, 12967] ⟨72485531, 6, [(2, 1), (5, 1), (13, 1), (43, 1), (12967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_12967
  · decide +kernel

theorem prime_75942103 : Nat.Prime 75942103 := by
  apply nodeValid_prime [2, 3, 101, 113, 1109] ⟨75942103, 3, [(2, 1), (3, 1), (101, 1), (113, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_113
    · exact prime_1109
  · decide +kernel

theorem prime_85532449 : Nat.Prime 85532449 := by
  apply nodeValid_prime [2, 3, 890963] ⟨85532449, 11, [(2, 5), (3, 1), (890963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_890963
  · decide +kernel

theorem prime_142153523 : Nat.Prime 142153523 := by
  apply nodeValid_prime [2, 7, 10153823] ⟨142153523, 2, [(2, 1), (7, 1), (10153823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10153823
  · decide +kernel

theorem prime_240000083 : Nat.Prime 240000083 := by
  apply nodeValid_prime [2, 7, 59, 290557] ⟨240000083, 2, [(2, 1), (7, 1), (59, 1), (290557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_290557
  · decide +kernel

theorem prime_267394019 : Nat.Prime 267394019 := by
  apply nodeValid_prime [2, 59, 401, 5651] ⟨267394019, 2, [(2, 1), (59, 1), (401, 1), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_401
    · exact prime_5651
  · decide +kernel

theorem prime_274231651 : Nat.Prime 274231651 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 23743] ⟨274231651, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (23743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23743
  · decide +kernel

theorem prime_455652619 : Nat.Prime 455652619 := by
  apply nodeValid_prime [2, 3, 75942103] ⟨455652619, 7, [(2, 1), (3, 1), (75942103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75942103
  · decide +kernel

theorem prime_480000167 : Nat.Prime 480000167 := by
  apply nodeValid_prime [2, 240000083] ⟨480000167, 5, [(2, 1), (240000083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_240000083
  · decide +kernel

theorem prime_894361057 : Nat.Prime 894361057 := by
  apply nodeValid_prime [2, 3, 1723, 5407] ⟨894361057, 5, [(2, 5), (3, 1), (1723, 1), (5407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1723
    · exact prime_5407
  · decide +kernel

theorem prime_1120051937 : Nat.Prime 1120051937 := by
  apply nodeValid_prime [2, 17, 2058919] ⟨1120051937, 3, [(2, 5), (17, 1), (2058919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2058919
  · decide +kernel

theorem prime_1296948563 : Nat.Prime 1296948563 := by
  apply nodeValid_prime [2, 7, 13, 389, 2617] ⟨1296948563, 2, [(2, 1), (7, 2), (13, 1), (389, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_389
    · exact prime_2617
  · decide +kernel

theorem prime_1518842051 : Nat.Prime 1518842051 := by
  apply nodeValid_prime [2, 5, 11, 17, 61, 2663] ⟨1518842051, 2, [(2, 1), (5, 2), (11, 1), (17, 1), (61, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_61
    · exact prime_2663
  · decide +kernel

theorem prime_2692855657 : Nat.Prime 2692855657 := by
  apply nodeValid_prime [2, 3, 37400773] ⟨2692855657, 10, [(2, 3), (3, 2), (37400773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37400773
  · decide +kernel

theorem prime_2698225811 : Nat.Prime 2698225811 := by
  apply nodeValid_prime [2, 5, 7, 61, 631903] ⟨2698225811, 6, [(2, 1), (5, 1), (7, 1), (61, 1), (631903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_631903
  · decide +kernel

theorem prime_6682550297 : Nat.Prime 6682550297 := by
  apply nodeValid_prime [2, 383, 1013, 2153] ⟨6682550297, 3, [(2, 3), (383, 1), (1013, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_1013
    · exact prime_2153
  · decide +kernel

theorem prime_7469697377 : Nat.Prime 7469697377 := by
  apply nodeValid_prime [2, 89, 1033, 2539] ⟨7469697377, 3, [(2, 5), (89, 1), (1033, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1033
    · exact prime_2539
  · decide +kernel

theorem prime_7899072067 : Nat.Prime 7899072067 := by
  apply nodeValid_prime [2, 3, 17, 67, 79, 4877] ⟨7899072067, 3, [(2, 1), (3, 2), (17, 1), (67, 1), (79, 1), (4877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
    · exact prime_79
    · exact prime_4877
  · decide +kernel

theorem prime_10671992809 : Nat.Prime 10671992809 := by
  apply nodeValid_prime [2, 3, 19, 29, 807017] ⟨10671992809, 31, [(2, 3), (3, 1), (19, 1), (29, 1), (807017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_807017
  · decide +kernel

theorem prime_11694362189 : Nat.Prime 11694362189 := by
  apply nodeValid_prime [2, 271, 10788157] ⟨11694362189, 2, [(2, 2), (271, 1), (10788157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_10788157
  · decide +kernel

theorem prime_13214922881 : Nat.Prime 13214922881 := by
  apply nodeValid_prime [2, 5, 61, 338497] ⟨13214922881, 6, [(2, 7), (5, 1), (61, 1), (338497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_338497
  · decide +kernel

theorem prime_20009986091 : Nat.Prime 20009986091 := by
  apply nodeValid_prime [2, 5, 71, 28183079] ⟨20009986091, 2, [(2, 1), (5, 1), (71, 1), (28183079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_28183079
  · decide +kernel

theorem prime_20085364093 : Nat.Prime 20085364093 := by
  apply nodeValid_prime [2, 3, 71, 193, 122147] ⟨20085364093, 2, [(2, 2), (3, 1), (71, 1), (193, 1), (122147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_193
    · exact prime_122147
  · decide +kernel

theorem prime_20426939047 : Nat.Prime 20426939047 := by
  apply nodeValid_prime [2, 3, 2389, 158341] ⟨20426939047, 3, [(2, 1), (3, 3), (2389, 1), (158341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2389
    · exact prime_158341
  · decide +kernel

theorem prime_23388724379 : Nat.Prime 23388724379 := by
  apply nodeValid_prime [2, 11694362189] ⟨23388724379, 2, [(2, 1), (11694362189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11694362189
  · decide +kernel

theorem prime_26830831711 : Nat.Prime 26830831711 := by
  apply nodeValid_prime [2, 3, 5, 894361057] ⟨26830831711, 6, [(2, 1), (3, 1), (5, 1), (894361057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_894361057
  · decide +kernel

theorem prime_26881246489 : Nat.Prime 26881246489 := by
  apply nodeValid_prime [2, 3, 1120051937] ⟨26881246489, 13, [(2, 3), (3, 1), (1120051937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1120051937
  · decide +kernel

theorem prime_52660477621 : Nat.Prime 52660477621 := by
  apply nodeValid_prime [2, 3, 5, 883, 110441] ⟨52660477621, 2, [(2, 2), (3, 3), (5, 1), (883, 1), (110441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_883
    · exact prime_110441
  · decide +kernel

theorem prime_79289537287 : Nat.Prime 79289537287 := by
  apply nodeValid_prime [2, 3, 13214922881] ⟨79289537287, 3, [(2, 1), (3, 1), (13214922881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13214922881
  · decide +kernel

theorem prime_160079888729 : Nat.Prime 160079888729 := by
  apply nodeValid_prime [2, 20009986091] ⟨160079888729, 3, [(2, 3), (20009986091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20009986091
  · decide +kernel

theorem prime_161590311419 : Nat.Prime 161590311419 := by
  apply nodeValid_prime [2, 37, 15973, 136709] ⟨161590311419, 2, [(2, 1), (37, 1), (15973, 1), (136709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_15973
    · exact prime_136709
  · decide +kernel

theorem prime_161590312283 : Nat.Prime 161590312283 := by
  apply nodeValid_prime [2, 7, 19, 101, 6014677] ⟨161590312283, 2, [(2, 1), (7, 1), (19, 1), (101, 1), (6014677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_101
    · exact prime_6014677
  · decide +kernel

theorem prime_314770678351 : Nat.Prime 314770678351 := by
  apply nodeValid_prime [2, 3, 5, 31, 281, 240899] ⟨314770678351, 3, [(2, 1), (3, 1), (5, 2), (31, 1), (281, 1), (240899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_281
    · exact prime_240899
  · decide +kernel

theorem prime_314770733969 : Nat.Prime 314770733969 := by
  apply nodeValid_prime [2, 1531, 12849883] ⟨314770733969, 3, [(2, 4), (1531, 1), (12849883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1531
    · exact prime_12849883
  · decide +kernel

theorem prime_314770735667 : Nat.Prime 314770735667 := by
  apply nodeValid_prime [2, 83, 2137, 887323] ⟨314770735667, 2, [(2, 1), (83, 1), (2137, 1), (887323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_2137
    · exact prime_887323
  · decide +kernel

theorem prime_315366369271 : Nat.Prime 315366369271 := by
  apply nodeValid_prime [2, 3, 5, 173, 953, 63761] ⟨315366369271, 3, [(2, 1), (3, 1), (5, 1), (173, 1), (953, 1), (63761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_953
    · exact prime_63761
  · decide +kernel

theorem prime_315366370381 : Nat.Prime 315366370381 := by
  apply nodeValid_prime [2, 3, 5, 19, 439, 23339] ⟨315366370381, 2, [(2, 2), (3, 4), (5, 1), (19, 1), (439, 1), (23339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_439
    · exact prime_23339
  · decide +kernel

theorem prime_315366398651 : Nat.Prime 315366398651 := by
  apply nodeValid_prime [2, 5, 23, 274231651] ⟨315366398651, 2, [(2, 1), (5, 2), (23, 1), (274231651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_274231651
  · decide +kernel

theorem prime_315962865587 : Nat.Prime 315962865587 := by
  apply nodeValid_prime [2, 41411, 3814963] ⟨315962865587, 2, [(2, 1), (41411, 1), (3814963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41411
    · exact prime_3814963
  · decide +kernel

theorem prime_315962865727 : Nat.Prime 315962865727 := by
  apply nodeValid_prime [2, 3, 52660477621] ⟨315962865727, 6, [(2, 1), (3, 1), (52660477621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52660477621
  · decide +kernel

theorem prime_315962882681 : Nat.Prime 315962882681 := by
  apply nodeValid_prime [2, 5, 7899072067] ⟨315962882681, 3, [(2, 3), (5, 1), (7899072067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7899072067
  · decide +kernel

theorem prime_316560110329 : Nat.Prime 316560110329 := by
  apply nodeValid_prime [2, 3, 7, 11, 107, 533641] ⟨316560110329, 29, [(2, 3), (3, 2), (7, 1), (11, 1), (107, 1), (533641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_107
    · exact prime_533641
  · decide +kernel

theorem prime_316560110831 : Nat.Prime 316560110831 := by
  apply nodeValid_prime [2, 5, 17, 113, 16478923] ⟨316560110831, 43, [(2, 1), (5, 1), (17, 1), (113, 1), (16478923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_113
    · exact prime_16478923
  · decide +kernel

theorem prime_316560133349 : Nat.Prime 316560133349 := by
  apply nodeValid_prime [2, 353, 863, 259783] ⟨316560133349, 2, [(2, 2), (353, 1), (863, 1), (259783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_863
    · exact prime_259783
  · decide +kernel

theorem prime_317158137269 : Nat.Prime 317158137269 := by
  apply nodeValid_prime [2, 7, 29, 157, 2487827] ⟨317158137269, 2, [(2, 2), (7, 1), (29, 1), (157, 1), (2487827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_157
    · exact prime_2487827
  · decide +kernel

theorem prime_317158137481 : Nat.Prime 317158137481 := by
  apply nodeValid_prime [2, 3, 5, 691, 3824869] ⟨317158137481, 14, [(2, 3), (3, 1), (5, 1), (691, 1), (3824869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_691
    · exact prime_3824869
  · decide +kernel

theorem prime_317158149149 : Nat.Prime 317158149149 := by
  apply nodeValid_prime [2, 79289537287] ⟨317158149149, 2, [(2, 2), (79289537287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_79289537287
  · decide +kernel

theorem prime_317756939207 : Nat.Prime 317756939207 := by
  apply nodeValid_prime [2, 7, 59, 54956233] ⟨317756939207, 5, [(2, 1), (7, 2), (59, 1), (54956233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_54956233
  · decide +kernel

theorem prime_317756967419 : Nat.Prime 317756967419 := by
  apply nodeValid_prime [2, 11, 641, 22532759] ⟨317756967419, 2, [(2, 1), (11, 1), (641, 1), (22532759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_641
    · exact prime_22532759
  · decide +kernel

theorem prime_317756967527 : Nat.Prime 317756967527 := by
  apply nodeValid_prime [2, 59, 2692855657] ⟨317756967527, 5, [(2, 1), (59, 1), (2692855657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2692855657
  · decide +kernel

theorem prime_318356452093 : Nat.Prime 318356452093 := by
  apply nodeValid_prime [2, 3, 7, 1801, 2104363] ⟨318356452093, 2, [(2, 2), (3, 1), (7, 1), (1801, 1), (2104363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1801
    · exact prime_2104363
  · decide +kernel

theorem prime_318356452153 : Nat.Prime 318356452153 := by
  apply nodeValid_prime [2, 3, 61, 72485531] ⟨318356452153, 5, [(2, 3), (3, 2), (61, 1), (72485531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_72485531
  · decide +kernel

theorem prime_318356499299 : Nat.Prime 318356499299 := by
  apply nodeValid_prime [2, 23, 977, 7083719] ⟨318356499299, 2, [(2, 1), (23, 1), (977, 1), (7083719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_977
    · exact prime_7083719
  · decide +kernel

theorem prime_318956830711 : Nat.Prime 318956830711 := by
  apply nodeValid_prime [2, 3, 5, 7, 1518842051] ⟨318956830711, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (1518842051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1518842051
  · decide +kernel

theorem prime_318956832839 : Nat.Prime 318956832839 := by
  apply nodeValid_prime [2, 7, 59629, 382073] ⟨318956832839, 7, [(2, 1), (7, 1), (59629, 1), (382073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59629
    · exact prime_382073
  · decide +kernel

theorem prime_318956833301 : Nat.Prime 318956833301 := by
  apply nodeValid_prime [2, 5, 7, 455652619] ⟨318956833301, 2, [(2, 2), (5, 2), (7, 1), (455652619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_455652619
  · decide +kernel

theorem prime_319557926449 : Nat.Prime 319557926449 := by
  apply nodeValid_prime [2, 3, 31, 71585557] ⟨319557926449, 7, [(2, 4), (3, 2), (31, 1), (71585557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_71585557
  · decide +kernel

theorem prime_319557945361 : Nat.Prime 319557945361 := by
  apply nodeValid_prime [2, 3, 5, 1279, 1041041] ⟨319557945361, 11, [(2, 4), (3, 1), (5, 1), (1279, 1), (1041041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1279
    · exact prime_1041041
  · decide +kernel

theorem prime_319557945517 : Nat.Prime 319557945517 := by
  apply nodeValid_prime [2, 3, 63703, 418031] ⟨319557945517, 5, [(2, 2), (3, 1), (63703, 1), (418031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63703
    · exact prime_418031
  · decide +kernel

theorem prime_320159776753 : Nat.Prime 320159776753 := by
  apply nodeValid_prime [2, 3, 557, 3991619] ⟨320159776753, 7, [(2, 4), (3, 2), (557, 1), (3991619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
    · exact prime_3991619
  · decide +kernel

theorem prime_320159777459 : Nat.Prime 320159777459 := by
  apply nodeValid_prime [2, 160079888729] ⟨320159777459, 2, [(2, 1), (160079888729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160079888729
  · decide +kernel

theorem prime_320159784271 : Nat.Prime 320159784271 := by
  apply nodeValid_prime [2, 3, 5, 10671992809] ⟨320159784271, 3, [(2, 1), (3, 1), (5, 1), (10671992809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10671992809
  · decide +kernel

theorem prime_320762414257 : Nat.Prime 320762414257 := by
  apply nodeValid_prime [2, 3, 6682550297] ⟨320762414257, 5, [(2, 4), (3, 1), (6682550297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6682550297
  · decide +kernel

theorem prime_320762440151 : Nat.Prime 320762440151 := by
  apply nodeValid_prime [2, 5, 23, 41, 263, 25867] ⟨320762440151, 17, [(2, 1), (5, 2), (23, 1), (41, 1), (263, 1), (25867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_41
    · exact prime_263
    · exact prime_25867
  · decide +kernel

theorem prime_320762440157 : Nat.Prime 320762440157 := by
  apply nodeValid_prime [2, 8111, 9886649] ⟨320762440157, 2, [(2, 2), (8111, 1), (9886649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8111
    · exact prime_9886649
  · decide +kernel

theorem prime_321365815213 : Nat.Prime 321365815213 := by
  apply nodeValid_prime [2, 3, 13, 14449, 142573] ⟨321365815213, 6, [(2, 2), (3, 1), (13, 1), (14449, 1), (142573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_14449
    · exact prime_142573
  · decide +kernel

theorem prime_321365824931 : Nat.Prime 321365824931 := by
  apply nodeValid_prime [2, 5, 29, 607, 1825631] ⟨321365824931, 2, [(2, 1), (5, 1), (29, 1), (607, 1), (1825631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_607
    · exact prime_1825631
  · decide +kernel

theorem prime_321365825489 : Nat.Prime 321365825489 := by
  apply nodeValid_prime [2, 20085364093] ⟨321365825489, 3, [(2, 4), (20085364093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20085364093
  · decide +kernel

theorem prime_321969899441 : Nat.Prime 321969899441 := by
  apply nodeValid_prime [2, 5, 7, 23, 43, 581341] ⟨321969899441, 3, [(2, 4), (5, 1), (7, 1), (23, 1), (43, 1), (581341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_43
    · exact prime_581341
  · decide +kernel

theorem prime_321969899533 : Nat.Prime 321969899533 := by
  apply nodeValid_prime [2, 3, 23, 1559, 748273] ⟨321969899533, 2, [(2, 2), (3, 1), (23, 1), (1559, 1), (748273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1559
    · exact prime_748273
  · decide +kernel

theorem prime_321969980533 : Nat.Prime 321969980533 := by
  apply nodeValid_prime [2, 3, 26830831711] ⟨321969980533, 2, [(2, 2), (3, 1), (26830831711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26830831711
  · decide +kernel

theorem prime_322574917031 : Nat.Prime 322574917031 := by
  apply nodeValid_prime [2, 5, 89, 373, 971699] ⟨322574917031, 29, [(2, 1), (5, 1), (89, 1), (373, 1), (971699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_373
    · exact prime_971699
  · decide +kernel

theorem prime_322574957869 : Nat.Prime 322574957869 := by
  apply nodeValid_prime [2, 3, 26881246489] ⟨322574957869, 2, [(2, 2), (3, 1), (26881246489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26881246489
  · decide +kernel

theorem prime_322574959561 : Nat.Prime 322574959561 := by
  apply nodeValid_prime [2, 3, 5, 7, 54859687] ⟨322574959561, 22, [(2, 3), (3, 1), (5, 1), (7, 2), (54859687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_54859687
  · decide +kernel

theorem prime_323180622839 : Nat.Prime 323180622839 := by
  apply nodeValid_prime [2, 161590311419] ⟨323180622839, 7, [(2, 1), (161590311419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_161590311419
  · decide +kernel

theorem prime_323180624567 : Nat.Prime 323180624567 := by
  apply nodeValid_prime [2, 161590312283] ⟨323180624567, 5, [(2, 1), (161590312283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_161590312283
  · decide +kernel

theorem prime_323180625791 : Nat.Prime 323180625791 := by
  apply nodeValid_prime [2, 5, 11, 29, 137, 739493] ⟨323180625791, 14, [(2, 1), (5, 1), (11, 1), (29, 1), (137, 1), (739493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_137
    · exact prime_739493
  · decide +kernel

theorem prime_323787095171 : Nat.Prime 323787095171 := by
  apply nodeValid_prime [2, 5, 7, 11, 23, 199, 91873] ⟨323787095171, 6, [(2, 1), (5, 1), (7, 1), (11, 1), (23, 1), (199, 1), (91873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_199
    · exact prime_91873
  · decide +kernel

theorem prime_323787097321 : Nat.Prime 323787097321 := by
  apply nodeValid_prime [2, 3, 5, 2698225811] ⟨323787097321, 17, [(2, 3), (3, 1), (5, 1), (2698225811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2698225811
  · decide +kernel

theorem prime_323787100573 : Nat.Prime 323787100573 := by
  apply nodeValid_prime [2, 3, 13, 773, 33149] ⟨323787100573, 5, [(2, 2), (3, 5), (13, 1), (773, 1), (33149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_773
    · exact prime_33149
  · decide +kernel

theorem prime_324394339487 : Nat.Prime 324394339487 := by
  apply nodeValid_prime [2, 7, 163, 142153523] ⟨324394339487, 5, [(2, 1), (7, 1), (163, 1), (142153523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163
    · exact prime_142153523
  · decide +kernel

theorem prime_324394357783 : Nat.Prime 324394357783 := by
  apply nodeValid_prime [2, 3, 11, 17, 31, 9326501] ⟨324394357783, 6, [(2, 1), (3, 1), (11, 1), (17, 1), (31, 1), (9326501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_31
    · exact prime_9326501
  · decide +kernel

theorem prime_324394358429 : Nat.Prime 324394358429 := by
  apply nodeValid_prime [2, 7, 17, 907, 751379] ⟨324394358429, 10, [(2, 2), (7, 1), (17, 1), (907, 1), (751379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_907
    · exact prime_751379
  · decide +kernel

theorem prime_325002353941 : Nat.Prime 325002353941 := by
  apply nodeValid_prime [2, 3, 5, 11, 18238067] ⟨325002353941, 13, [(2, 2), (3, 4), (5, 1), (11, 1), (18238067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_18238067
  · decide +kernel

theorem prime_325002412661 : Nat.Prime 325002412661 := by
  apply nodeValid_prime [2, 5, 17, 19, 1549, 32479] ⟨325002412661, 2, [(2, 2), (5, 1), (17, 1), (19, 1), (1549, 1), (32479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_1549
    · exact prime_32479
  · decide +kernel

theorem prime_325611134729 : Nat.Prime 325611134729 := by
  apply nodeValid_prime [2, 11, 59, 62714009] ⟨325611134729, 3, [(2, 3), (11, 1), (59, 1), (62714009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_62714009
  · decide +kernel

theorem prime_325611135103 : Nat.Prime 325611135103 := by
  apply nodeValid_prime [2, 3, 11, 23, 79, 2715191] ⟨325611135103, 5, [(2, 1), (3, 1), (11, 1), (23, 1), (79, 1), (2715191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_79
    · exact prime_2715191
  · decide +kernel

theorem prime_325611143147 : Nat.Prime 325611143147 := by
  apply nodeValid_prime [2, 109, 7699, 194003] ⟨325611143147, 2, [(2, 1), (109, 1), (7699, 1), (194003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_7699
    · exact prime_194003
  · decide +kernel

theorem prime_326220703181 : Nat.Prime 326220703181 := by
  apply nodeValid_prime [2, 5, 61, 267394019] ⟨326220703181, 2, [(2, 2), (5, 1), (61, 1), (267394019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_267394019
  · decide +kernel

theorem prime_326220759707 : Nat.Prime 326220759707 := by
  apply nodeValid_prime [2, 29, 10729, 18077] ⟨326220759707, 2, [(2, 1), (29, 2), (10729, 1), (18077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_10729
    · exact prime_18077
  · decide +kernel

theorem prime_326220760487 : Nat.Prime 326220760487 := by
  apply nodeValid_prime [2, 1907, 85532449] ⟨326220760487, 5, [(2, 1), (1907, 1), (85532449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1907
    · exact prime_85532449
  · decide +kernel

theorem prime_326831024753 : Nat.Prime 326831024753 := by
  apply nodeValid_prime [2, 20426939047] ⟨326831024753, 3, [(2, 4), (20426939047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20426939047
  · decide +kernel

theorem prime_326831026127 : Nat.Prime 326831026127 := by
  apply nodeValid_prime [2, 11, 17, 19, 2113, 21767] ⟨326831026127, 5, [(2, 1), (11, 1), (17, 1), (19, 1), (2113, 1), (21767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_2113
    · exact prime_21767
  · decide +kernel

theorem prime_326831037877 : Nat.Prime 326831037877 := by
  apply nodeValid_prime [2, 3, 7, 1296948563] ⟨326831037877, 2, [(2, 2), (3, 2), (7, 1), (1296948563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1296948563
  · decide +kernel

theorem prime_327442141121 : Nat.Prime 327442141121 := by
  apply nodeValid_prime [2, 5, 1721, 594571] ⟨327442141121, 3, [(2, 6), (5, 1), (1721, 1), (594571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1721
    · exact prime_594571
  · decide +kernel

theorem prime_327442141307 : Nat.Prime 327442141307 := by
  apply nodeValid_prime [2, 7, 23388724379] ⟨327442141307, 2, [(2, 1), (7, 1), (23388724379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23388724379
  · decide +kernel

theorem prime_327442148179 : Nat.Prime 327442148179 := by
  apply nodeValid_prime [2, 3, 17, 41, 2087, 37517] ⟨327442148179, 2, [(2, 1), (3, 1), (17, 1), (41, 1), (2087, 1), (37517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_2087
    · exact prime_37517
  · decide +kernel

theorem prime_328054009123 : Nat.Prime 328054009123 := by
  apply nodeValid_prime [2, 3, 7, 8933, 13879] ⟨328054009123, 3, [(2, 1), (3, 3), (7, 2), (8933, 1), (13879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8933
    · exact prime_13879
  · decide +kernel

theorem prime_328054009901 : Nat.Prime 328054009901 := by
  apply nodeValid_prime [2, 5, 17, 53, 3640999] ⟨328054009901, 10, [(2, 2), (5, 2), (17, 1), (53, 1), (3640999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_53
    · exact prime_3640999
  · decide +kernel

theorem prime_328054028429 : Nat.Prime 328054028429 := by
  apply nodeValid_prime [2, 7, 883, 1895521] ⟨328054028429, 2, [(2, 2), (7, 2), (883, 1), (1895521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_883
    · exact prime_1895521
  · decide +kernel

theorem prime_328666684589 : Nat.Prime 328666684589 := by
  apply nodeValid_prime [2, 11, 7469697377] ⟨328666684589, 2, [(2, 2), (11, 1), (7469697377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_7469697377
  · decide +kernel

theorem prime_328666702603 : Nat.Prime 328666702603 := by
  apply nodeValid_prime [2, 3, 7, 47, 59, 2821997] ⟨328666702603, 2, [(2, 1), (3, 1), (7, 1), (47, 1), (59, 1), (2821997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_59
    · exact prime_2821997
  · decide +kernel

theorem prime_328666703083 : Nat.Prime 328666703083 := by
  apply nodeValid_prime [2, 3, 2011, 27239077] ⟨328666703083, 2, [(2, 1), (3, 1), (2011, 1), (27239077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2011
    · exact prime_27239077
  · decide +kernel

theorem prime_329280114563 : Nat.Prime 329280114563 := by
  apply nodeValid_prime [2, 7, 480000167] ⟨329280114563, 2, [(2, 1), (7, 3), (480000167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_480000167
  · decide +kernel

theorem prime_329280114773 : Nat.Prime 329280114773 := by
  apply nodeValid_prime [2, 7, 17, 1277, 541711] ⟨329280114773, 5, [(2, 2), (7, 1), (17, 1), (1277, 1), (541711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1277
    · exact prime_541711
  · decide +kernel

theorem prime_329280117323 : Nat.Prime 329280117323 := by
  apply nodeValid_prime [2, 13, 17, 137, 5437793] ⟨329280117323, 2, [(2, 1), (13, 1), (17, 1), (137, 1), (5437793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_137
    · exact prime_5437793
  · decide +kernel

end Sude.Lucas.Generated
