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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1987 : Nat.Prime 1987 := by
  apply nodeValid_prime [2, 3, 331] ⟨1987, 2, [(2, 1), (3, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
  · decide +kernel

theorem prime_2239 : Nat.Prime 2239 := by
  apply nodeValid_prime [2, 3, 373] ⟨2239, 3, [(2, 1), (3, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373
  · decide +kernel

theorem prime_2707 : Nat.Prime 2707 := by
  apply nodeValid_prime [2, 3, 11, 41] ⟨2707, 2, [(2, 1), (3, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_3001 : Nat.Prime 3001 := by
  apply nodeValid_prime [2, 3, 5] ⟨3001, 14, [(2, 3), (3, 1), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_3251 : Nat.Prime 3251 := by
  apply nodeValid_prime [2, 5, 13] ⟨3251, 6, [(2, 1), (5, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_3851 : Nat.Prime 3851 := by
  apply nodeValid_prime [2, 5, 7, 11] ⟨3851, 2, [(2, 1), (5, 2), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_3929 : Nat.Prime 3929 := by
  apply nodeValid_prime [2, 491] ⟨3929, 3, [(2, 3), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_491
  · decide +kernel

theorem prime_5021 : Nat.Prime 5021 := by
  apply nodeValid_prime [2, 5, 251] ⟨5021, 3, [(2, 2), (5, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
  · decide +kernel

theorem prime_5077 : Nat.Prime 5077 := by
  apply nodeValid_prime [2, 3, 47] ⟨5077, 2, [(2, 2), (3, 3), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_5119 : Nat.Prime 5119 := by
  apply nodeValid_prime [2, 3, 853] ⟨5119, 3, [(2, 1), (3, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853
  · decide +kernel

theorem prime_5849 : Nat.Prime 5849 := by
  apply nodeValid_prime [2, 17, 43] ⟨5849, 3, [(2, 3), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_6073 : Nat.Prime 6073 := by
  apply nodeValid_prime [2, 3, 11, 23] ⟨6073, 10, [(2, 3), (3, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_6287 : Nat.Prime 6287 := by
  apply nodeValid_prime [2, 7, 449] ⟨6287, 7, [(2, 1), (7, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_449
  · decide +kernel

theorem prime_7507 : Nat.Prime 7507 := by
  apply nodeValid_prime [2, 3, 139] ⟨7507, 2, [(2, 1), (3, 3), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_7537 : Nat.Prime 7537 := by
  apply nodeValid_prime [2, 3, 157] ⟨7537, 7, [(2, 4), (3, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
  · decide +kernel

theorem prime_7549 : Nat.Prime 7549 := by
  apply nodeValid_prime [2, 3, 17, 37] ⟨7549, 2, [(2, 2), (3, 1), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_8761 : Nat.Prime 8761 := by
  apply nodeValid_prime [2, 3, 5, 73] ⟨8761, 23, [(2, 3), (3, 1), (5, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_9857 : Nat.Prime 9857 := by
  apply nodeValid_prime [2, 7, 11] ⟨9857, 5, [(2, 7), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_10091 : Nat.Prime 10091 := by
  apply nodeValid_prime [2, 5, 1009] ⟨10091, 2, [(2, 1), (5, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1009
  · decide +kernel

theorem prime_10151 : Nat.Prime 10151 := by
  apply nodeValid_prime [2, 5, 7, 29] ⟨10151, 7, [(2, 1), (5, 2), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_11699 : Nat.Prime 11699 := by
  apply nodeValid_prime [2, 5849] ⟨11699, 2, [(2, 1), (5849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5849
  · decide +kernel

theorem prime_12713 : Nat.Prime 12713 := by
  apply nodeValid_prime [2, 7, 227] ⟨12713, 3, [(2, 3), (7, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
  · decide +kernel

theorem prime_13001 : Nat.Prime 13001 := by
  apply nodeValid_prime [2, 5, 13] ⟨13001, 3, [(2, 3), (5, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_14197 : Nat.Prime 14197 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨14197, 11, [(2, 2), (3, 1), (7, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_14411 : Nat.Prime 14411 := by
  apply nodeValid_prime [2, 5, 11, 131] ⟨14411, 2, [(2, 1), (5, 1), (11, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_131
  · decide +kernel

theorem prime_15551 : Nat.Prime 15551 := by
  apply nodeValid_prime [2, 5, 311] ⟨15551, 7, [(2, 1), (5, 2), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_311
  · decide +kernel

theorem prime_17099 : Nat.Prime 17099 := by
  apply nodeValid_prime [2, 83, 103] ⟨17099, 2, [(2, 1), (83, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_103
  · decide +kernel

theorem prime_19073 : Nat.Prime 19073 := by
  apply nodeValid_prime [2, 149] ⟨19073, 3, [(2, 7), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_149
  · decide +kernel

theorem prime_19079 : Nat.Prime 19079 := by
  apply nodeValid_prime [2, 9539] ⟨19079, 7, [(2, 1), (9539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9539
  · decide +kernel

theorem prime_19507 : Nat.Prime 19507 := by
  apply nodeValid_prime [2, 3, 3251] ⟨19507, 2, [(2, 1), (3, 1), (3251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3251
  · decide +kernel

theorem prime_23279 : Nat.Prime 23279 := by
  apply nodeValid_prime [2, 103, 113] ⟨23279, 7, [(2, 1), (103, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_113
  · decide +kernel

theorem prime_23311 : Nat.Prime 23311 := by
  apply nodeValid_prime [2, 3, 5, 7, 37] ⟨23311, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_23399 : Nat.Prime 23399 := by
  apply nodeValid_prime [2, 11699] ⟨23399, 17, [(2, 1), (11699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11699
  · decide +kernel

theorem prime_24841 : Nat.Prime 24841 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨24841, 14, [(2, 3), (3, 3), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_26251 : Nat.Prime 26251 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨26251, 2, [(2, 1), (3, 1), (5, 4), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_28051 : Nat.Prime 28051 := by
  apply nodeValid_prime [2, 3, 5, 11, 17] ⟨28051, 2, [(2, 1), (3, 1), (5, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_30197 : Nat.Prime 30197 := by
  apply nodeValid_prime [2, 7549] ⟨30197, 2, [(2, 2), (7549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7549
  · decide +kernel

theorem prime_32051 : Nat.Prime 32051 := by
  apply nodeValid_prime [2, 5, 641] ⟨32051, 10, [(2, 1), (5, 2), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
  · decide +kernel

theorem prime_32971 : Nat.Prime 32971 := by
  apply nodeValid_prime [2, 3, 5, 7, 157] ⟨32971, 11, [(2, 1), (3, 1), (5, 1), (7, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_157
  · decide +kernel

theorem prime_33679 : Nat.Prime 33679 := by
  apply nodeValid_prime [2, 3, 1871] ⟨33679, 3, [(2, 1), (3, 2), (1871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1871
  · decide +kernel

theorem prime_35597 : Nat.Prime 35597 := by
  apply nodeValid_prime [2, 11, 809] ⟨35597, 2, [(2, 2), (11, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_809
  · decide +kernel

theorem prime_36083 : Nat.Prime 36083 := by
  apply nodeValid_prime [2, 18041] ⟨36083, 2, [(2, 1), (18041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18041
  · decide +kernel

theorem prime_38921 : Nat.Prime 38921 := by
  apply nodeValid_prime [2, 5, 7, 139] ⟨38921, 6, [(2, 3), (5, 1), (7, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_39209 : Nat.Prime 39209 := by
  apply nodeValid_prime [2, 13, 29] ⟨39209, 3, [(2, 3), (13, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_40169 : Nat.Prime 40169 := by
  apply nodeValid_prime [2, 5021] ⟨40169, 3, [(2, 3), (5021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5021
  · decide +kernel

theorem prime_41729 : Nat.Prime 41729 := by
  apply nodeValid_prime [2, 163] ⟨41729, 3, [(2, 8), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163
  · decide +kernel

theorem prime_42293 : Nat.Prime 42293 := by
  apply nodeValid_prime [2, 97, 109] ⟨42293, 2, [(2, 2), (97, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_109
  · decide +kernel

theorem prime_46559 : Nat.Prime 46559 := by
  apply nodeValid_prime [2, 23279] ⟨46559, 7, [(2, 1), (23279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23279
  · decide +kernel

theorem prime_49207 : Nat.Prime 49207 := by
  apply nodeValid_prime [2, 3, 59, 139] ⟨49207, 3, [(2, 1), (3, 1), (59, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_139
  · decide +kernel

theorem prime_50993 : Nat.Prime 50993 := by
  apply nodeValid_prime [2, 3187] ⟨50993, 3, [(2, 4), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3187
  · decide +kernel

theorem prime_54767 : Nat.Prime 54767 := by
  apply nodeValid_prime [2, 139, 197] ⟨54767, 5, [(2, 1), (139, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_197
  · decide +kernel

theorem prime_62003 : Nat.Prime 62003 := by
  apply nodeValid_prime [2, 29, 1069] ⟨62003, 2, [(2, 1), (29, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1069
  · decide +kernel

theorem prime_72167 : Nat.Prime 72167 := by
  apply nodeValid_prime [2, 36083] ⟨72167, 5, [(2, 1), (36083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36083
  · decide +kernel

theorem prime_74209 : Nat.Prime 74209 := by
  apply nodeValid_prime [2, 3, 773] ⟨74209, 19, [(2, 5), (3, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_773
  · decide +kernel

theorem prime_74219 : Nat.Prime 74219 := by
  apply nodeValid_prime [2, 43, 863] ⟨74219, 2, [(2, 1), (43, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_863
  · decide +kernel

theorem prime_92809 : Nat.Prime 92809 := by
  apply nodeValid_prime [2, 3, 1289] ⟨92809, 14, [(2, 3), (3, 2), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1289
  · decide +kernel

theorem prime_101987 : Nat.Prime 101987 := by
  apply nodeValid_prime [2, 50993] ⟨101987, 2, [(2, 1), (50993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_50993
  · decide +kernel

theorem prime_102503 : Nat.Prime 102503 := by
  apply nodeValid_prime [2, 53, 967] ⟨102503, 5, [(2, 1), (53, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_967
  · decide +kernel

theorem prime_117043 : Nat.Prime 117043 := by
  apply nodeValid_prime [2, 3, 19507] ⟨117043, 2, [(2, 1), (3, 1), (19507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19507
  · decide +kernel

theorem prime_120907 : Nat.Prime 120907 := by
  apply nodeValid_prime [2, 3, 2239] ⟨120907, 2, [(2, 1), (3, 3), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2239
  · decide +kernel

theorem prime_121021 : Nat.Prime 121021 := by
  apply nodeValid_prime [2, 3, 5, 2017] ⟨121021, 7, [(2, 2), (3, 1), (5, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2017
  · decide +kernel

theorem prime_125329 : Nat.Prime 125329 := by
  apply nodeValid_prime [2, 3, 7, 373] ⟨125329, 22, [(2, 4), (3, 1), (7, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_373
  · decide +kernel

theorem prime_128993 : Nat.Prime 128993 := by
  apply nodeValid_prime [2, 29, 139] ⟨128993, 3, [(2, 5), (29, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_139
  · decide +kernel

theorem prime_146609 : Nat.Prime 146609 := by
  apply nodeValid_prime [2, 7, 11, 17] ⟨146609, 3, [(2, 4), (7, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_155717 : Nat.Prime 155717 := by
  apply nodeValid_prime [2, 11, 3539] ⟨155717, 2, [(2, 2), (11, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3539
  · decide +kernel

theorem prime_228647 : Nat.Prime 228647 := by
  apply nodeValid_prime [2, 11, 19, 547] ⟨228647, 5, [(2, 1), (11, 1), (19, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_547
  · decide +kernel

theorem prime_243137 : Nat.Prime 243137 := by
  apply nodeValid_prime [2, 29, 131] ⟨243137, 3, [(2, 6), (29, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_131
  · decide +kernel

theorem prime_257987 : Nat.Prime 257987 := by
  apply nodeValid_prime [2, 128993] ⟨257987, 2, [(2, 1), (128993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_128993
  · decide +kernel

theorem prime_298093 : Nat.Prime 298093 := by
  apply nodeValid_prime [2, 3, 24841] ⟨298093, 5, [(2, 2), (3, 1), (24841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24841
  · decide +kernel

theorem prime_315751 : Nat.Prime 315751 := by
  apply nodeValid_prime [2, 3, 5, 421] ⟨315751, 7, [(2, 1), (3, 1), (5, 3), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_421
  · decide +kernel

theorem prime_329711 : Nat.Prime 329711 := by
  apply nodeValid_prime [2, 5, 32971] ⟨329711, 7, [(2, 1), (5, 1), (32971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_32971
  · decide +kernel

theorem prime_395137 : Nat.Prime 395137 := by
  apply nodeValid_prime [2, 3, 7] ⟨395137, 5, [(2, 7), (3, 2), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_468173 : Nat.Prime 468173 := by
  apply nodeValid_prime [2, 117043] ⟨468173, 2, [(2, 2), (117043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117043
  · decide +kernel

theorem prime_518911 : Nat.Prime 518911 := by
  apply nodeValid_prime [2, 3, 5, 7, 353] ⟨518911, 17, [(2, 1), (3, 1), (5, 1), (7, 2), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_353
  · decide +kernel

theorem prime_570491 : Nat.Prime 570491 := by
  apply nodeValid_prime [2, 5, 89, 641] ⟨570491, 6, [(2, 1), (5, 1), (89, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_641
  · decide +kernel

theorem prime_615019 : Nat.Prime 615019 := by
  apply nodeValid_prime [2, 3, 102503] ⟨615019, 2, [(2, 1), (3, 1), (102503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102503
  · decide +kernel

theorem prime_615539 : Nat.Prime 615539 := by
  apply nodeValid_prime [2, 7, 11, 571] ⟨615539, 2, [(2, 1), (7, 2), (11, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_571
  · decide +kernel

theorem prime_659423 : Nat.Prime 659423 := by
  apply nodeValid_prime [2, 329711] ⟨659423, 5, [(2, 1), (329711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_329711
  · decide +kernel

theorem prime_662477 : Nat.Prime 662477 := by
  apply nodeValid_prime [2, 29, 5711] ⟨662477, 2, [(2, 2), (29, 1), (5711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_5711
  · decide +kernel

theorem prime_776137 : Nat.Prime 776137 := by
  apply nodeValid_prime [2, 3, 73, 443] ⟨776137, 5, [(2, 3), (3, 1), (73, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_443
  · decide +kernel

theorem prime_907457 : Nat.Prime 907457 := by
  apply nodeValid_prime [2, 11, 1289] ⟨907457, 3, [(2, 6), (11, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1289
  · decide +kernel

theorem prime_1212173 : Nat.Prime 1212173 := by
  apply nodeValid_prime [2, 13, 23311] ⟨1212173, 2, [(2, 2), (13, 1), (23311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23311
  · decide +kernel

theorem prime_1304929 : Nat.Prime 1304929 := by
  apply nodeValid_prime [2, 3, 23, 197] ⟨1304929, 11, [(2, 5), (3, 2), (23, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_197
  · decide +kernel

theorem prime_1408289 : Nat.Prime 1408289 := by
  apply nodeValid_prime [2, 7, 6287] ⟨1408289, 3, [(2, 5), (7, 1), (6287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6287
  · decide +kernel

theorem prime_1591237 : Nat.Prime 1591237 := by
  apply nodeValid_prime [2, 3, 44201] ⟨1591237, 2, [(2, 2), (3, 2), (44201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44201
  · decide +kernel

theorem prime_2418037 : Nat.Prime 2418037 := by
  apply nodeValid_prime [2, 3, 23, 8761] ⟨2418037, 2, [(2, 2), (3, 1), (23, 1), (8761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_8761
  · decide +kernel

theorem prime_2524061 : Nat.Prime 2524061 := by
  apply nodeValid_prime [2, 5, 7, 11, 149] ⟨2524061, 2, [(2, 2), (5, 1), (7, 1), (11, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_149
  · decide +kernel

theorem prime_2980931 : Nat.Prime 2980931 := by
  apply nodeValid_prime [2, 5, 298093] ⟨2980931, 2, [(2, 1), (5, 1), (298093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_298093
  · decide +kernel

theorem prime_2981371 : Nat.Prime 2981371 := by
  apply nodeValid_prime [2, 3, 5, 7, 14197] ⟨2981371, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (14197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_14197
  · decide +kernel

theorem prime_3007897 : Nat.Prime 3007897 := by
  apply nodeValid_prime [2, 3, 125329] ⟨3007897, 5, [(2, 3), (3, 1), (125329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_125329
  · decide +kernel

theorem prime_3189583 : Nat.Prime 3189583 := by
  apply nodeValid_prime [2, 3, 11, 89, 181] ⟨3189583, 13, [(2, 1), (3, 2), (11, 1), (89, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89
    · exact prime_181
  · decide +kernel

theorem prime_3630631 : Nat.Prime 3630631 := by
  apply nodeValid_prime [2, 3, 5, 121021] ⟨3630631, 3, [(2, 1), (3, 1), (5, 1), (121021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_121021
  · decide +kernel

theorem prime_3789013 : Nat.Prime 3789013 := by
  apply nodeValid_prime [2, 3, 315751] ⟨3789013, 2, [(2, 2), (3, 1), (315751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_315751
  · decide +kernel

theorem prime_4150369 : Nat.Prime 4150369 := by
  apply nodeValid_prime [2, 3, 14411] ⟨4150369, 13, [(2, 5), (3, 2), (14411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14411
  · decide +kernel

theorem prime_6150191 : Nat.Prime 6150191 := by
  apply nodeValid_prime [2, 5, 615019] ⟨6150191, 11, [(2, 1), (5, 1), (615019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_615019
  · decide +kernel

theorem prime_6175693 : Nat.Prime 6175693 := by
  apply nodeValid_prime [2, 3, 17, 10091] ⟨6175693, 5, [(2, 2), (3, 2), (17, 1), (10091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_10091
  · decide +kernel

theorem prime_8380621 : Nat.Prime 8380621 := by
  apply nodeValid_prime [2, 3, 5, 46559] ⟨8380621, 2, [(2, 2), (3, 2), (5, 1), (46559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46559
  · decide +kernel

theorem prime_9758431 : Nat.Prime 9758431 := by
  apply nodeValid_prime [2, 3, 5, 11, 9857] ⟨9758431, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (9857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_9857
  · decide +kernel

theorem prime_10153513 : Nat.Prime 10153513 := by
  apply nodeValid_prime [2, 3, 1741] ⟨10153513, 7, [(2, 3), (3, 6), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1741
  · decide +kernel

theorem prime_11310799 : Nat.Prime 11310799 := by
  apply nodeValid_prime [2, 3, 1217, 1549] ⟨11310799, 3, [(2, 1), (3, 1), (1217, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1217
    · exact prime_1549
  · decide +kernel

theorem prime_12006509 : Nat.Prime 12006509 := by
  apply nodeValid_prime [2, 61, 49207] ⟨12006509, 2, [(2, 2), (61, 1), (49207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_49207
  · decide +kernel

theorem prime_12300383 : Nat.Prime 12300383 := by
  apply nodeValid_prime [2, 6150191] ⟨12300383, 5, [(2, 1), (6150191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6150191
  · decide +kernel

theorem prime_12340667 : Nat.Prime 12340667 := by
  apply nodeValid_prime [2, 13, 31, 61, 251] ⟨12340667, 2, [(2, 1), (13, 1), (31, 1), (61, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_61
    · exact prime_251
  · decide +kernel

theorem prime_18047383 : Nat.Prime 18047383 := by
  apply nodeValid_prime [2, 3, 3007897] ⟨18047383, 3, [(2, 1), (3, 1), (3007897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3007897
  · decide +kernel

theorem prime_21014761 : Nat.Prime 21014761 := by
  apply nodeValid_prime [2, 3, 5, 13, 19, 709] ⟨21014761, 7, [(2, 3), (3, 1), (5, 1), (13, 1), (19, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_709
  · decide +kernel

theorem prime_21588233 : Nat.Prime 21588233 := by
  apply nodeValid_prime [2, 17, 181, 877] ⟨21588233, 3, [(2, 3), (17, 1), (181, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_181
    · exact prime_877
  · decide +kernel

theorem prime_21848863 : Nat.Prime 21848863 := by
  apply nodeValid_prime [2, 3, 7, 31, 97, 173] ⟨21848863, 3, [(2, 1), (3, 1), (7, 1), (31, 1), (97, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_97
    · exact prime_173
  · decide +kernel

theorem prime_26471891 : Nat.Prime 26471891 := by
  apply nodeValid_prime [2, 5, 17, 155717] ⟨26471891, 2, [(2, 1), (5, 1), (17, 1), (155717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_155717
  · decide +kernel

theorem prime_34483367 : Nat.Prime 34483367 := by
  apply nodeValid_prime [2, 19, 907457] ⟨34483367, 5, [(2, 1), (19, 1), (907457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_907457
  · decide +kernel

theorem prime_35429059 : Nat.Prime 35429059 := by
  apply nodeValid_prime [2, 3, 7, 40169] ⟨35429059, 2, [(2, 1), (3, 2), (7, 2), (40169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_40169
  · decide +kernel

theorem prime_42705979 : Nat.Prime 42705979 := by
  apply nodeValid_prime [2, 3, 7, 61, 79, 211] ⟨42705979, 3, [(2, 1), (3, 1), (7, 1), (61, 1), (79, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_79
    · exact prime_211
  · decide +kernel

theorem prime_49055057 : Nat.Prime 49055057 := by
  apply nodeValid_prime [2, 1543, 1987] ⟨49055057, 3, [(2, 4), (1543, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1543
    · exact prime_1987
  · decide +kernel

theorem prime_67121489 : Nat.Prime 67121489 := by
  apply nodeValid_prime [2, 7, 499, 1201] ⟨67121489, 3, [(2, 4), (7, 1), (499, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_499
    · exact prime_1201
  · decide +kernel

theorem prime_102302143 : Nat.Prime 102302143 := by
  apply nodeValid_prime [2, 3, 157, 223, 487] ⟨102302143, 3, [(2, 1), (3, 1), (157, 1), (223, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_223
    · exact prime_487
  · decide +kernel

theorem prime_147408319 : Nat.Prime 147408319 := by
  apply nodeValid_prime [2, 3, 1877, 4363] ⟨147408319, 3, [(2, 1), (3, 2), (1877, 1), (4363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1877
    · exact prime_4363
  · decide +kernel

theorem prime_153713333 : Nat.Prime 153713333 := by
  apply nodeValid_prime [2, 5119, 7507] ⟨153713333, 2, [(2, 2), (5119, 1), (7507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5119
    · exact prime_7507
  · decide +kernel

theorem prime_198844703 : Nat.Prime 198844703 := by
  apply nodeValid_prime [2, 7, 607, 23399] ⟨198844703, 5, [(2, 1), (7, 1), (607, 1), (23399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_607
    · exact prime_23399
  · decide +kernel

theorem prime_506396381 : Nat.Prime 506396381 := by
  apply nodeValid_prime [2, 5, 7, 43, 61, 197] ⟨506396381, 2, [(2, 2), (5, 1), (7, 2), (43, 1), (61, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_61
    · exact prime_197
  · decide +kernel

theorem prime_866182189 : Nat.Prime 866182189 := by
  apply nodeValid_prime [2, 3, 61, 157, 7537] ⟨866182189, 6, [(2, 2), (3, 1), (61, 1), (157, 1), (7537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_157
    · exact prime_7537
  · decide +kernel

theorem prime_985540289 : Nat.Prime 985540289 := by
  apply nodeValid_prime [2, 37, 41, 10151] ⟨985540289, 3, [(2, 6), (37, 1), (41, 1), (10151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_41
    · exact prime_10151
  · decide +kernel

theorem prime_1034865011 : Nat.Prime 1034865011 := by
  apply nodeValid_prime [2, 5, 41, 2524061] ⟨1034865011, 6, [(2, 1), (5, 1), (41, 1), (2524061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_2524061
  · decide +kernel

theorem prime_1295293981 : Nat.Prime 1295293981 := by
  apply nodeValid_prime [2, 3, 5, 21588233] ⟨1295293981, 2, [(2, 2), (3, 1), (5, 1), (21588233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21588233
  · decide +kernel

theorem prime_1421814083 : Nat.Prime 1421814083 := by
  apply nodeValid_prime [2, 13, 373, 146609] ⟨1421814083, 2, [(2, 1), (13, 1), (373, 1), (146609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_373
    · exact prime_146609
  · decide +kernel

theorem prime_1657748051 : Nat.Prime 1657748051 := by
  apply nodeValid_prime [2, 5, 7, 277, 17099] ⟨1657748051, 2, [(2, 1), (5, 2), (7, 1), (277, 1), (17099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_277
    · exact prime_17099
  · decide +kernel

theorem prime_2455251433 : Nat.Prime 2455251433 := by
  apply nodeValid_prime [2, 3, 102302143] ⟨2455251433, 5, [(2, 3), (3, 1), (102302143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102302143
  · decide +kernel

theorem prime_2621264699 : Nat.Prime 2621264699 := by
  apply nodeValid_prime [2, 13, 1277, 6073] ⟨2621264699, 2, [(2, 1), (13, 2), (1277, 1), (6073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1277
    · exact prime_6073
  · decide +kernel

theorem prime_8593379479 : Nat.Prime 8593379479 := by
  apply nodeValid_prime [2, 3, 113, 1408289] ⟨8593379479, 3, [(2, 1), (3, 3), (113, 1), (1408289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_1408289
  · decide +kernel

theorem prime_10068223351 : Nat.Prime 10068223351 := by
  apply nodeValid_prime [2, 3, 5, 67121489] ⟨10068223351, 3, [(2, 1), (3, 1), (5, 2), (67121489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67121489
  · decide +kernel

theorem prime_33928557367 : Nat.Prime 33928557367 := by
  apply nodeValid_prime [2, 3, 11, 29, 191, 92809] ⟨33928557367, 5, [(2, 1), (3, 1), (11, 1), (29, 1), (191, 1), (92809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_191
    · exact prime_92809
  · decide +kernel

theorem prime_100682233511 : Nat.Prime 100682233511 := by
  apply nodeValid_prime [2, 5, 10068223351] ⟨100682233511, 17, [(2, 1), (5, 1), (10068223351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10068223351
  · decide +kernel

theorem prime_100682234909 : Nat.Prime 100682234909 := by
  apply nodeValid_prime [2, 37, 67, 10153513] ⟨100682234909, 2, [(2, 2), (37, 1), (67, 1), (10153513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_67
    · exact prime_10153513
  · decide +kernel

theorem prime_199173885697 : Nat.Prime 199173885697 := by
  apply nodeValid_prime [2, 3, 29, 2980931] ⟨199173885697, 5, [(2, 8), (3, 2), (29, 1), (2980931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2980931
  · decide +kernel

theorem prime_199173887251 : Nat.Prime 199173887251 := by
  apply nodeValid_prime [2, 3, 5, 13, 373, 54767] ⟨199173887251, 3, [(2, 1), (3, 1), (5, 3), (13, 1), (373, 1), (54767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_373
    · exact prime_54767
  · decide +kernel

theorem prime_199173923129 : Nat.Prime 199173923129 := by
  apply nodeValid_prime [2, 19079, 1304929] ⟨199173923129, 3, [(2, 3), (19079, 1), (1304929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19079
    · exact prime_1304929
  · decide +kernel

theorem prime_199610733589 : Nat.Prime 199610733589 := by
  apply nodeValid_prime [2, 3, 7, 61, 151, 257987] ⟨199610733589, 6, [(2, 2), (3, 1), (7, 1), (61, 1), (151, 1), (257987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_151
    · exact prime_257987
  · decide +kernel

theorem prime_199610749147 : Nat.Prime 199610749147 := by
  apply nodeValid_prime [2, 3, 5387, 6175693] ⟨199610749147, 2, [(2, 1), (3, 1), (5387, 1), (6175693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5387
    · exact prime_6175693
  · decide +kernel

theorem prime_200048179691 : Nat.Prime 200048179691 := by
  apply nodeValid_prime [2, 5, 30197, 662477] ⟨200048179691, 2, [(2, 1), (5, 1), (30197, 1), (662477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30197
    · exact prime_662477
  · decide +kernel

theorem prime_200048179693 : Nat.Prime 200048179693 := by
  apply nodeValid_prime [2, 3, 107, 4003, 38921] ⟨200048179693, 5, [(2, 2), (3, 1), (107, 1), (4003, 1), (38921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_4003
    · exact prime_38921
  · decide +kernel

theorem prime_200048189629 : Nat.Prime 200048189629 := by
  apply nodeValid_prime [2, 3, 7, 109, 21848863] ⟨200048189629, 2, [(2, 2), (3, 1), (7, 1), (109, 1), (21848863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
    · exact prime_21848863
  · decide +kernel

theorem prime_200486295739 : Nat.Prime 200486295739 := by
  apply nodeValid_prime [2, 3, 17, 19, 34483367] ⟨200486295739, 2, [(2, 1), (3, 2), (17, 1), (19, 1), (34483367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_34483367
  · decide +kernel

theorem prime_200486313301 : Nat.Prime 200486313301 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 2027, 3623] ⟨200486313301, 6, [(2, 2), (3, 1), (5, 2), (7, 1), (13, 1), (2027, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_2027
    · exact prime_3623
  · decide +kernel

theorem prime_200486314579 : Nat.Prime 200486314579 := by
  apply nodeValid_prime [2, 3, 11, 23, 83, 1591237] ⟨200486314579, 2, [(2, 1), (3, 1), (11, 1), (23, 1), (83, 1), (1591237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_83
    · exact prime_1591237
  · decide +kernel

theorem prime_200925048997 : Nat.Prime 200925048997 := by
  apply nodeValid_prime [2, 3, 7, 4339, 26251] ⟨200925048997, 2, [(2, 2), (3, 2), (7, 2), (4339, 1), (26251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4339
    · exact prime_26251
  · decide +kernel

theorem prime_200925049249 : Nat.Prime 200925049249 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 19, 28051] ⟨200925049249, 26, [(2, 5), (3, 2), (7, 1), (11, 1), (17, 1), (19, 1), (28051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_28051
  · decide +kernel

theorem prime_200925055579 : Nat.Prime 200925055579 := by
  apply nodeValid_prime [2, 3, 13, 499, 1907, 2707] ⟨200925055579, 2, [(2, 1), (3, 1), (13, 1), (499, 1), (1907, 1), (2707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_499
    · exact prime_1907
    · exact prime_2707
  · decide +kernel

theorem prime_201364466231 : Nat.Prime 201364466231 := by
  apply nodeValid_prime [2, 5, 131, 153713333] ⟨201364466231, 11, [(2, 1), (5, 1), (131, 1), (153713333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_153713333
  · decide +kernel

theorem prime_201364467023 : Nat.Prime 201364467023 := by
  apply nodeValid_prime [2, 100682233511] ⟨201364467023, 5, [(2, 1), (100682233511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_100682233511
  · decide +kernel

theorem prime_201364469819 : Nat.Prime 201364469819 := by
  apply nodeValid_prime [2, 100682234909] ⟨201364469819, 2, [(2, 1), (100682234909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_100682234909
  · decide +kernel

theorem prime_201804531947 : Nat.Prime 201804531947 := by
  apply nodeValid_prime [2, 41729, 2418037] ⟨201804531947, 2, [(2, 1), (41729, 1), (2418037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41729
    · exact prime_2418037
  · decide +kernel

theorem prime_201804532537 : Nat.Prime 201804532537 := by
  apply nodeValid_prime [2, 3, 29, 2843, 101987] ⟨201804532537, 5, [(2, 3), (3, 1), (29, 1), (2843, 1), (101987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2843
    · exact prime_101987
  · decide +kernel

theorem prime_201804539537 : Nat.Prime 201804539537 := by
  apply nodeValid_prime [2, 31, 617, 659423] ⟨201804539537, 3, [(2, 4), (31, 1), (617, 1), (659423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_617
    · exact prime_659423
  · decide +kernel

theorem prime_202245246793 : Nat.Prime 202245246793 := by
  apply nodeValid_prime [2, 3, 3851, 243137] ⟨202245246793, 5, [(2, 3), (3, 3), (3851, 1), (243137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3851
    · exact prime_243137
  · decide +kernel

theorem prime_202245247241 : Nat.Prime 202245247241 := by
  apply nodeValid_prime [2, 5, 191, 26471891] ⟨202245247241, 3, [(2, 3), (5, 1), (191, 1), (26471891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
    · exact prime_26471891
  · decide +kernel

theorem prime_202245262223 : Nat.Prime 202245262223 := by
  apply nodeValid_prime [2, 61, 1657748051] ⟨202245262223, 5, [(2, 1), (61, 1), (1657748051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_1657748051
  · decide +kernel

theorem prime_202686632191 : Nat.Prime 202686632191 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 139, 173, 787] ⟨202686632191, 6, [(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (139, 1), (173, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_139
    · exact prime_173
    · exact prime_787
  · decide +kernel

theorem prime_202686632227 : Nat.Prime 202686632227 := by
  apply nodeValid_prime [2, 3, 13, 866182189] ⟨202686632227, 5, [(2, 1), (3, 2), (13, 1), (866182189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_866182189
  · decide +kernel

theorem prime_202686636601 : Nat.Prime 202686636601 := by
  apply nodeValid_prime [2, 3, 5, 7, 31, 518911] ⟨202686636601, 13, [(2, 3), (3, 2), (5, 2), (7, 1), (31, 1), (518911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_518911
  · decide +kernel

theorem prime_203128663583 : Nat.Prime 203128663583 := by
  apply nodeValid_prime [2, 13, 53, 147408319] ⟨203128663583, 5, [(2, 1), (13, 1), (53, 1), (147408319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_147408319
  · decide +kernel

theorem prime_203128678303 : Nat.Prime 203128678303 := by
  apply nodeValid_prime [2, 3, 11, 2539, 1212173] ⟨203128678303, 5, [(2, 1), (3, 1), (11, 1), (2539, 1), (1212173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2539
    · exact prime_1212173
  · decide +kernel

theorem prime_203128679827 : Nat.Prime 203128679827 := by
  apply nodeValid_prime [2, 3, 179, 21014761] ⟨203128679827, 2, [(2, 1), (3, 3), (179, 1), (21014761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_21014761
  · decide +kernel

theorem prime_203571338651 : Nat.Prime 203571338651 := by
  apply nodeValid_prime [2, 5, 331, 12300383] ⟨203571338651, 2, [(2, 1), (5, 2), (331, 1), (12300383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_331
    · exact prime_12300383
  · decide +kernel

theorem prime_203571344203 : Nat.Prime 203571344203 := by
  apply nodeValid_prime [2, 3, 33928557367] ⟨203571344203, 3, [(2, 1), (3, 1), (33928557367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33928557367
  · decide +kernel

theorem prime_203571345163 : Nat.Prime 203571345163 := by
  apply nodeValid_prime [2, 3, 67, 506396381] ⟨203571345163, 2, [(2, 1), (3, 1), (67, 1), (506396381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_506396381
  · decide +kernel

theorem prime_204014665121 : Nat.Prime 204014665121 := by
  apply nodeValid_prime [2, 5, 7, 59, 73, 42293] ⟨204014665121, 6, [(2, 5), (5, 1), (7, 1), (59, 1), (73, 1), (42293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_73
    · exact prime_42293
  · decide +kernel

theorem prime_204014665279 : Nat.Prime 204014665279 := by
  apply nodeValid_prime [2, 3, 19, 198844703] ⟨204014665279, 3, [(2, 1), (3, 3), (19, 1), (198844703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_198844703
  · decide +kernel

theorem prime_204014665661 : Nat.Prime 204014665661 := by
  apply nodeValid_prime [2, 5, 13, 83, 131, 72167] ⟨204014665661, 2, [(2, 2), (5, 1), (13, 1), (83, 1), (131, 1), (72167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_83
    · exact prime_131
    · exact prime_72167
  · decide +kernel

theorem prime_204458646313 : Nat.Prime 204458646313 := by
  apply nodeValid_prime [2, 3, 97, 9758431] ⟨204458646313, 5, [(2, 3), (3, 3), (97, 1), (9758431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_9758431
  · decide +kernel

theorem prime_204458646523 : Nat.Prime 204458646523 := by
  apply nodeValid_prime [2, 3, 13, 2621264699] ⟨204458646523, 2, [(2, 1), (3, 1), (13, 1), (2621264699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2621264699
  · decide +kernel

theorem prime_204458649467 : Nat.Prime 204458649467 := by
  apply nodeValid_prime [2, 32051, 3189583] ⟨204458649467, 2, [(2, 1), (32051, 1), (3189583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32051
    · exact prime_3189583
  · decide +kernel

theorem prime_204903272179 : Nat.Prime 204903272179 := by
  apply nodeValid_prime [2, 3, 11, 1034865011] ⟨204903272179, 7, [(2, 1), (3, 2), (11, 1), (1034865011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1034865011
  · decide +kernel

theorem prime_204903272549 : Nat.Prime 204903272549 := by
  apply nodeValid_prime [2, 13, 5077, 776137] ⟨204903272549, 2, [(2, 2), (13, 1), (5077, 1), (776137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5077
    · exact prime_776137
  · decide +kernel

theorem prime_204903287243 : Nat.Prime 204903287243 := by
  apply nodeValid_prime [2, 2399, 42705979] ⟨204903287243, 2, [(2, 1), (2399, 1), (42705979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2399
    · exact prime_42705979
  · decide +kernel

theorem prime_205348577143 : Nat.Prime 205348577143 := by
  apply nodeValid_prime [2, 3, 1151, 1559, 19073] ⟨205348577143, 3, [(2, 1), (3, 1), (1151, 1), (1559, 1), (19073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1151
    · exact prime_1559
    · exact prime_19073
  · decide +kernel

theorem prime_205348698677 : Nat.Prime 205348698677 := by
  apply nodeValid_prime [2, 11, 43, 3049, 35597] ⟨205348698677, 2, [(2, 2), (11, 1), (43, 1), (3049, 1), (35597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_3049
    · exact prime_35597
  · decide +kernel

theorem prime_205348698881 : Nat.Prime 205348698881 := by
  apply nodeValid_prime [2, 5, 13, 12340667] ⟨205348698881, 11, [(2, 8), (5, 1), (13, 1), (12340667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_12340667
  · decide +kernel

theorem prime_205794519131 : Nat.Prime 205794519131 := by
  apply nodeValid_prime [2, 5, 47, 13001, 33679] ⟨205794519131, 6, [(2, 1), (5, 1), (47, 1), (13001, 1), (33679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_13001
    · exact prime_33679
  · decide +kernel

theorem prime_205794529277 : Nat.Prime 205794529277 := by
  apply nodeValid_prime [2, 7, 877, 8380621] ⟨205794529277, 2, [(2, 2), (7, 1), (877, 1), (8380621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_877
    · exact prime_8380621
  · decide +kernel

theorem prime_205794529319 : Nat.Prime 205794529319 := by
  apply nodeValid_prime [2, 7, 79, 3001, 62003] ⟨205794529319, 7, [(2, 1), (7, 1), (79, 1), (3001, 1), (62003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_3001
    · exact prime_62003
  · decide +kernel

theorem prime_206241107497 : Nat.Prime 206241107497 := by
  apply nodeValid_prime [2, 3, 8593379479] ⟨206241107497, 5, [(2, 3), (3, 1), (8593379479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8593379479
  · decide +kernel

theorem prime_206241108967 : Nat.Prime 206241108967 := by
  apply nodeValid_prime [2, 3, 1013, 11310799] ⟨206241108967, 3, [(2, 1), (3, 2), (1013, 1), (11310799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1013
    · exact prime_11310799
  · decide +kernel

theorem prime_206241120373 : Nat.Prime 206241120373 := by
  apply nodeValid_prime [2, 3, 7, 2455251433] ⟨206241120373, 2, [(2, 2), (3, 1), (7, 1), (2455251433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2455251433
  · decide +kernel

theorem prime_206688376201 : Nat.Prime 206688376201 := by
  apply nodeValid_prime [2, 3, 5, 83, 4150369] ⟨206688376201, 7, [(2, 3), (3, 1), (5, 2), (83, 1), (4150369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_4150369
  · decide +kernel

theorem prime_206688376369 : Nat.Prime 206688376369 := by
  apply nodeValid_prime [2, 3, 29, 101, 461, 1063] ⟨206688376369, 7, [(2, 4), (3, 2), (29, 1), (101, 1), (461, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_101
    · exact prime_461
    · exact prime_1063
  · decide +kernel

theorem prime_206688376553 : Nat.Prime 206688376553 := by
  apply nodeValid_prime [2, 7, 19, 73, 691, 3851] ⟨206688376553, 11, [(2, 3), (7, 1), (19, 1), (73, 1), (691, 1), (3851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_73
    · exact prime_691
    · exact prime_3851
  · decide +kernel

theorem prime_207136259969 : Nat.Prime 207136259969 := by
  apply nodeValid_prime [2, 11, 239, 615539] ⟨207136259969, 3, [(2, 7), (11, 1), (239, 1), (615539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_615539
  · decide +kernel

theorem prime_207136260641 : Nat.Prime 207136260641 := by
  apply nodeValid_prime [2, 5, 17, 191, 577, 691] ⟨207136260641, 11, [(2, 5), (5, 1), (17, 1), (191, 1), (577, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_191
    · exact prime_577
    · exact prime_691
  · decide +kernel

theorem prime_207136293269 : Nat.Prime 207136293269 := by
  apply nodeValid_prime [2, 19, 227, 12006509] ⟨207136293269, 2, [(2, 2), (19, 1), (227, 1), (12006509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_227
    · exact prime_12006509
  · decide +kernel

theorem prime_207584856119 : Nat.Prime 207584856119 := by
  apply nodeValid_prime [2, 73, 1421814083] ⟨207584856119, 7, [(2, 1), (73, 1), (1421814083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1421814083
  · decide +kernel

theorem prime_207584856151 : Nat.Prime 207584856151 := by
  apply nodeValid_prime [2, 3, 5, 7, 12713, 15551] ⟨207584856151, 12, [(2, 1), (3, 1), (5, 2), (7, 1), (12713, 1), (15551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_12713
    · exact prime_15551
  · decide +kernel

theorem prime_207584866219 : Nat.Prime 207584866219 := by
  apply nodeValid_prime [2, 3, 23, 397, 3789013] ⟨207584866219, 3, [(2, 1), (3, 1), (23, 1), (397, 1), (3789013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_397
    · exact prime_3789013
  · decide +kernel

theorem prime_208034098583 : Nat.Prime 208034098583 := by
  apply nodeValid_prime [2, 67, 3929, 395137] ⟨208034098583, 5, [(2, 1), (67, 1), (3929, 1), (395137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_3929
    · exact prime_395137
  · decide +kernel

theorem prime_208034105639 : Nat.Prime 208034105639 := by
  apply nodeValid_prime [2, 139, 251, 2981371] ⟨208034105639, 17, [(2, 1), (139, 1), (251, 1), (2981371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_251
    · exact prime_2981371
  · decide +kernel

theorem prime_208034107079 : Nat.Prime 208034107079 := by
  apply nodeValid_prime [2, 7, 61, 570491] ⟨208034107079, 7, [(2, 1), (7, 2), (61, 2), (570491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_570491
  · decide +kernel

theorem prime_208483991323 : Nat.Prime 208483991323 := by
  apply nodeValid_prime [2, 3, 74219, 468173] ⟨208483991323, 2, [(2, 1), (3, 1), (74219, 1), (468173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74219
    · exact prime_468173
  · decide +kernel

theorem prime_208483992251 : Nat.Prime 208483992251 := by
  apply nodeValid_prime [2, 5, 17, 49055057] ⟨208483992251, 6, [(2, 1), (5, 3), (17, 1), (49055057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_49055057
  · decide +kernel

theorem prime_208483992953 : Nat.Prime 208483992953 := by
  apply nodeValid_prime [2, 293, 389, 228647] ⟨208483992953, 3, [(2, 3), (293, 1), (389, 1), (228647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_389
    · exact prime_228647
  · decide +kernel

theorem prime_208934541269 : Nat.Prime 208934541269 := by
  apply nodeValid_prime [2, 53, 985540289] ⟨208934541269, 2, [(2, 2), (53, 1), (985540289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_985540289
  · decide +kernel

theorem prime_208934548993 : Nat.Prime 208934548993 := by
  apply nodeValid_prime [2, 3, 13, 47, 74209] ⟨208934548993, 5, [(2, 9), (3, 2), (13, 1), (47, 1), (74209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
    · exact prime_74209
  · decide +kernel

theorem prime_208934550421 : Nat.Prime 208934550421 := by
  apply nodeValid_prime [2, 3, 5, 83, 347, 120907] ⟨208934550421, 6, [(2, 2), (3, 1), (5, 1), (83, 1), (347, 1), (120907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_347
    · exact prime_120907
  · decide +kernel

theorem prime_209385737567 : Nat.Prime 209385737567 := by
  apply nodeValid_prime [2, 5801, 18047383] ⟨209385737567, 5, [(2, 1), (5801, 1), (18047383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5801
    · exact prime_18047383
  · decide +kernel

theorem prime_209385738691 : Nat.Prime 209385738691 := by
  apply nodeValid_prime [2, 3, 5, 197, 35429059] ⟨209385738691, 2, [(2, 1), (3, 1), (5, 1), (197, 1), (35429059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
    · exact prime_35429059
  · decide +kernel

theorem prime_209385751033 : Nat.Prime 209385751033 := by
  apply nodeValid_prime [2, 3, 89, 3630631] ⟨209385751033, 10, [(2, 3), (3, 4), (89, 1), (3630631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_3630631
  · decide +kernel

theorem prime_209837624923 : Nat.Prime 209837624923 := by
  apply nodeValid_prime [2, 3, 1295293981] ⟨209837624923, 3, [(2, 1), (3, 4), (1295293981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1295293981
  · decide +kernel

theorem prime_209837628349 : Nat.Prime 209837628349 := by
  apply nodeValid_prime [2, 3, 59, 7559, 39209] ⟨209837628349, 2, [(2, 2), (3, 1), (59, 1), (7559, 1), (39209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_7559
    · exact prime_39209
  · decide +kernel

theorem prime_209837629849 : Nat.Prime 209837629849 := by
  apply nodeValid_prime [2, 3, 7, 11, 1907, 5413] ⟨209837629849, 23, [(2, 3), (3, 1), (7, 1), (11, 2), (1907, 1), (5413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1907
    · exact prime_5413
  · decide +kernel

end Sude.Lucas.Generated
